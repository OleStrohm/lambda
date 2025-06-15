use std::collections::HashMap;

mod pretty;

#[derive(Debug, Clone, PartialEq, Eq)]
enum InferrableTerm {
    Annotated(CheckableTerm, Type),
    Bound(usize),
    Free(Name),
    Application(Box<InferrableTerm>, CheckableTerm),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
enum Name {
    Global(&'static str),
    Local(usize),
    Quote(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CheckableTerm {
    Inferrable(Box<InferrableTerm>),
    Lambda(Box<CheckableTerm>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Type {
    Free(Name),
    Function(Box<Type>, Box<Type>),
}

enum Value {
    Neutral(Neutral),
    Lambda(Box<dyn LambdaFn>),
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Neutral(neutral) => f.debug_tuple("Neutral").field(neutral).finish(),
            Value::Lambda(_lambda_fn) => f.debug_tuple("Lambda(..)").finish(),
        }
    }
}

impl Clone for Value {
    fn clone(&self) -> Self {
        match self {
            Value::Neutral(neutral) => Value::Neutral(neutral.clone()),
            Value::Lambda(lambda_fn) => Value::Lambda((**lambda_fn).boxed_clone()),
        }
    }
}

trait LambdaFn: FnOnce(Value) -> Value + 'static {
    fn boxed_clone(&self) -> Box<dyn LambdaFn>;
}

impl<F: FnOnce(Value) -> Value + Clone + 'static> LambdaFn for F {
    fn boxed_clone(&self) -> Box<dyn LambdaFn> {
        Box::new(self.clone())
    }
}

#[derive(Debug, Clone)]
enum Neutral {
    Free(Name),
    Application(Box<Neutral>, Box<Value>),
}

type Env = Vec<Value>;

impl Value {
    fn free(name: Name) -> Value {
        Value::Neutral(Neutral::Free(name))
    }

    fn application(f: Value, arg: Value) -> Value {
        match f {
            Value::Neutral(neutral) => {
                Value::Neutral(Neutral::Application(Box::new(neutral), Box::new(arg)))
            }
            Value::Lambda(f) => f(arg),
        }
    }
}

impl InferrableTerm {
    fn eval(self, env: Env) -> Value {
        match self {
            InferrableTerm::Annotated(term, _) => term.eval(env),
            InferrableTerm::Bound(i) => env[i].clone(),
            InferrableTerm::Free(name) => Value::free(name),
            InferrableTerm::Application(f, arg) => {
                Value::application(f.eval(env.clone()), arg.eval(env))
            }
        }
    }
}

impl CheckableTerm {
    fn eval(self, mut env: Env) -> Value {
        match self {
            CheckableTerm::Inferrable(term) => term.eval(env),
            CheckableTerm::Lambda(term) => Value::Lambda(Box::new(move |arg| {
                env.insert(0, arg);
                term.eval(env)
            })),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Kind {
    Star,
}

#[derive(Debug, Clone)]
enum Info {
    HasKind(Kind),
    HasType(Type),
}

type Context = HashMap<Name, Info>;

type TRes<R> = Result<R, String>;

fn kind(ctx: Context, ty: &Type, _k: Kind) -> TRes<()> {
    match ty {
        Type::Free(name) => match ctx.get(name) {
            Some(Info::HasKind(Kind::Star)) => Ok(()),
            _ => Err("Unknown identifier".into()),
        },
        Type::Function(input, ret) => {
            kind(ctx.clone(), input, _k)?;
            kind(ctx, ret, _k)
        }
    }
}

impl InferrableTerm {
    fn ty(self, idx: usize, ctx: Context) -> TRes<Type> {
        match self {
            InferrableTerm::Annotated(term, ty) => {
                kind(ctx.clone(), &ty, Kind::Star)?;
                term.ty(idx, ctx, &ty)?;
                Ok(ty)
            }
            InferrableTerm::Free(name) => match ctx.get(&name) {
                Some(Info::HasType(ty)) => Ok(ty.clone()),
                _ => Err("Unknown identifier".into()),
            },
            InferrableTerm::Application(f, arg) => match f.ty(idx, ctx.clone())? {
                Type::Function(input, ret) => {
                    arg.ty(idx, ctx, &input)?;
                    Ok(*ret)
                }
                _ => Err("Illegal application".into()),
            },
            InferrableTerm::Bound(_) => Err("ICE: Can't run into Bound variables".into()),
        }
    }
}

impl CheckableTerm {
    fn ty(self, idx: usize, mut ctx: Context, ty: &Type) -> TRes<()> {
        match (self, ty) {
            (CheckableTerm::Inferrable(term), ty) => (&term.ty(idx, ctx)? == ty)
                .then_some(())
                .ok_or("Type mismatch".into()),
            (CheckableTerm::Lambda(term), Type::Function(input, ret)) => {
                let substituted = term.subst(0, InferrableTerm::Free(Name::Local(idx)));
                ctx.insert(Name::Local(idx), Info::HasType(*input.clone()));
                substituted.ty(idx + 1, ctx, ret)
            }
            _ => Err("Type mismatch".into()),
        }
    }
}

impl InferrableTerm {
    fn subst(self, idx: usize, to: InferrableTerm) -> InferrableTerm {
        match self {
            InferrableTerm::Annotated(term, ty) => {
                InferrableTerm::Annotated(term.subst(idx, to), ty)
            }
            InferrableTerm::Bound(i) => {
                if i == idx {
                    to
                } else {
                    InferrableTerm::Bound(i)
                }
            }
            InferrableTerm::Free(name) => InferrableTerm::Free(name),
            InferrableTerm::Application(f, body) => {
                InferrableTerm::Application(Box::new(f.subst(idx, to.clone())), body.subst(idx, to))
            }
        }
    }
}

impl CheckableTerm {
    fn subst(self, idx: usize, to: InferrableTerm) -> CheckableTerm {
        match self {
            CheckableTerm::Inferrable(term) => {
                CheckableTerm::Inferrable(Box::new(term.subst(idx, to)))
            }
            CheckableTerm::Lambda(term) => CheckableTerm::Lambda(Box::new(term.subst(idx + 1, to))),
        }
    }
}

impl Value {
    fn quote(self, idx: usize) -> CheckableTerm {
        match self {
            Value::Neutral(neutral) => CheckableTerm::Inferrable(Box::new(neutral.quote(idx))),
            Value::Lambda(f) => {
                CheckableTerm::Lambda(Box::new(f(Value::free(Name::Quote(idx))).quote(idx + 1)))
            }
        }
    }
}

impl Neutral {
    fn quote(self, idx: usize) -> InferrableTerm {
        match self {
            Neutral::Free(Name::Quote(k)) => InferrableTerm::Bound(idx - k - 1),
            Neutral::Free(name) => InferrableTerm::Free(name),
            Neutral::Application(neutral, value) => {
                InferrableTerm::Application(Box::new(neutral.quote(idx)), value.quote(idx))
            }
        }
    }
}

fn main() {
    let id_ = CheckableTerm::Lambda(Box::new(CheckableTerm::Inferrable(Box::new(
        InferrableTerm::Bound(0),
    ))));

    let const_ = CheckableTerm::Lambda(Box::new(CheckableTerm::Lambda(Box::new(
        CheckableTerm::Inferrable(Box::new(InferrableTerm::Bound(1))),
    ))));

    fn tfree(g: &'static str) -> Box<Type> {
        Box::new(Type::Free(Name::Global(g)))
    }

    fn free(g: &'static str) -> CheckableTerm {
        CheckableTerm::Inferrable(Box::new(InferrableTerm::Free(Name::Global(g))))
    }

    let term1 = InferrableTerm::Application(
        Box::new(InferrableTerm::Annotated(
            id_.clone(),
            Type::Function(tfree("a"), tfree("a")),
        )),
        free("y"),
    );
    dbg!((term1.clone().eval(vec![])).quote(0));

    // (const : (b -> b) -> a -> (b -> b)) id y => id
    let term2 = InferrableTerm::Application(
        Box::new(InferrableTerm::Application(
            Box::new(InferrableTerm::Annotated(
                const_.clone(),
                Type::Function(
                    Box::new(Type::Function(tfree("b"), tfree("b"))),
                    Box::new(Type::Function(
                        tfree("a"),
                        Box::new(Type::Function(tfree("b"), tfree("b"))),
                    )),
                ),
            )),
            id_,
        )),
        free("y"),
    );

    dbg!(term2.clone().eval(vec![]).quote(0));

    let env1 = [
        (Name::Global("y"), Info::HasType(*tfree("a"))),
        (Name::Global("a"), Info::HasKind(Kind::Star)),
    ]
    .into_iter()
    .collect::<HashMap<_, _>>();
    let env2 = [
        (Name::Global("y"), Info::HasType(*tfree("a"))),
        (Name::Global("a"), Info::HasKind(Kind::Star)),
        (Name::Global("b"), Info::HasKind(Kind::Star)),
    ]
    .into_iter()
    .collect::<HashMap<_, _>>();

    dbg!(term1.ty(0, env1).unwrap());
    dbg!(term2.ty(0, env2).unwrap());
}

#[cfg(test)]
mod tests {
    use super::*;

    // (\lam a.a)
    fn id_() -> CheckableTerm {
        CheckableTerm::Lambda(Box::new(CheckableTerm::Inferrable(Box::new(
            InferrableTerm::Bound(0),
        ))))
    }

    // (\lam a. (\lam b. a))
    fn const_() -> CheckableTerm {
        CheckableTerm::Lambda(Box::new(CheckableTerm::Lambda(Box::new(
            CheckableTerm::Inferrable(Box::new(InferrableTerm::Bound(1))),
        ))))
    }

    fn tfree(g: &'static str) -> Box<Type> {
        Box::new(Type::Free(Name::Global(g)))
    }

    fn free(g: &'static str) -> CheckableTerm {
        CheckableTerm::Inferrable(Box::new(InferrableTerm::Free(Name::Global(g))))
    }

    #[test]
    fn term1() {
        // (id: a -> a) y
        let term1 = InferrableTerm::Application(
            Box::new(InferrableTerm::Annotated(
                id_(),
                Type::Function(tfree("a"), tfree("a")),
            )),
            free("y"),
        );
        assert_eq!(
            (term1.clone().eval(vec![])).quote(0),
            CheckableTerm::Inferrable(Box::new(InferrableTerm::Free(Name::Global("y"))))
        );
    }

    #[test]
    fn term2() {
        // (const : (b -> b) -> a -> (b -> b)) id y => id
        let term2 = InferrableTerm::Application(
            Box::new(InferrableTerm::Application(
                Box::new(InferrableTerm::Annotated(
                    const_(),
                    Type::Function(
                        Box::new(Type::Function(tfree("b"), tfree("b"))),
                        Box::new(Type::Function(
                            tfree("a"),
                            Box::new(Type::Function(tfree("b"), tfree("b"))),
                        )),
                    ),
                )),
                id_(),
            )),
            free("y"),
        );

        assert_eq!(
            term2.clone().eval(vec![]).quote(0),
            CheckableTerm::Lambda(Box::new(CheckableTerm::Inferrable(Box::new(
                InferrableTerm::Bound(0)
            ))))
        );
    }

    #[test]
    fn typeof_term1() {
        // (id: a -> a) y
        let term1 = InferrableTerm::Application(
            Box::new(InferrableTerm::Annotated(
                id_(),
                Type::Function(tfree("a"), tfree("a")),
            )),
            free("y"),
        );

        let env1 = [
            (Name::Global("y"), Info::HasType(*tfree("a"))),
            (Name::Global("a"), Info::HasKind(Kind::Star)),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        assert_eq!(term1.ty(0, env1).unwrap(), *tfree("a"));
    }

    #[test]
    fn typeof_term2() {
        // (const : (b -> b) -> a -> (b -> b)) id y => id
        let term2 = InferrableTerm::Application(
            Box::new(InferrableTerm::Application(
                Box::new(InferrableTerm::Annotated(
                    const_(),
                    Type::Function(
                        Box::new(Type::Function(tfree("b"), tfree("b"))),
                        Box::new(Type::Function(
                            tfree("a"),
                            Box::new(Type::Function(tfree("b"), tfree("b"))),
                        )),
                    ),
                )),
                id_(),
            )),
            free("y"),
        );
        let env2 = [
            (Name::Global("y"), Info::HasType(*tfree("a"))),
            (Name::Global("a"), Info::HasKind(Kind::Star)),
            (Name::Global("b"), Info::HasKind(Kind::Star)),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        assert_eq!(
            term2.ty(0, env2).unwrap(),
            Type::Function(tfree("b"), tfree("b"))
        );
    }
}
