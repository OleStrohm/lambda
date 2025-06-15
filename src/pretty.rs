#![allow(unused)]

use crate::{CheckableTerm, InferrableTerm, Name, Type};

impl Name {
    fn pretty(&self) -> String {
        match self {
            Name::Global(name) => name.to_string(),
            Name::Local(i) => format!("Bound({i})"),
            Name::Quote(i) => format!("Quote({i})"),
        }
    }
}

impl Type {
    fn pretty(&self) -> String {
        match self {
            Type::Free(name) => name.pretty(),
            Type::Function(input, out) => format!("({} -> {})", input.pretty(), out.pretty()),
        }
    }
}

impl InferrableTerm {
    fn pretty(&self, nesting: usize) -> String {
        match self {
            InferrableTerm::Annotated(term, ty) => {
                format!("{} : {}", term.pretty(nesting), ty.pretty())
            }
            InferrableTerm::Bound(i) => format!("l{}", nesting - i - 1),
            InferrableTerm::Free(name) => name.pretty(),
            InferrableTerm::Application(inferrable_term, checkable_term) => {
                format!(
                    "{} {}",
                    inferrable_term.pretty(nesting),
                    checkable_term.pretty(nesting)
                )
            }
        }
    }
}

impl CheckableTerm {
    fn pretty(&self, nesting: usize) -> String {
        match self {
            CheckableTerm::Inferrable(term) => term.pretty(nesting),
            CheckableTerm::Lambda(term) => {
                format!("(λ l{nesting} -> {})", term.pretty(nesting + 1))
            }
        }
    }
}

#[cfg(test)]
#[test]
fn pretty_test() {
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
        format!("{}", term2.pretty(0)),
        "(λ l0 -> (λ l1 -> l0)) : ((b -> b) -> (a -> (b -> b))) (λ l0 -> l0) y"
    );
}
