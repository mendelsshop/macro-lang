use std::{collections::HashSet, rc::Rc};

type Ident = Rc<str>;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Scope(usize);

pub struct ScopeCreator(usize);

impl ScopeCreator {
    fn new() -> Self {
        Self(0)
    }

    fn new_scope(&mut self) -> Scope {
        let scope = Scope(self.0);
        self.0 += 1;
        scope
    }
}

type ScopeSet = HashSet<Scope>;
#[derive(Clone, PartialEq, Eq, Debug)]
struct Syntax(Ident, ScopeSet);

trait AdjustScope: Sized {
    fn adjust_scope(
        self,
        other_scope: Scope,
        operation: fn(HashSet<Scope>, Scope) -> HashSet<Scope>,
    ) -> Self;

    fn add_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(other_scope, |mut scopes, other_scope| {
            scopes.insert(other_scope);
            scopes
        })
    }

    fn flip_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(other_scope, |mut scopes, other_scope| {
            if !scopes.remove(&other_scope) {
                scopes.insert(other_scope);
            }
            scopes
        })
    }
}

impl Syntax {
    fn new(symbol: Rc<str>) -> Self {
        Self(symbol, HashSet::new())
    }
}

impl AdjustScope for Syntax {
    fn adjust_scope(
        self,
        other_scope_set: Scope,
        operation: fn(HashSet<Scope>, Scope) -> HashSet<Scope>,
    ) -> Self {
        Self(self.0, operation(self.1, other_scope_set))
    }
}

#[derive(Clone, PartialEq, Debug)]
enum Ast {
    List(Vec<Ast>),
    Syntax(Syntax),
    Symbol(Ident),
    Number(f64),
}

impl Ast {
    fn datum_to_syntax(self) -> Self {
        match self {
            Self::List(l) => Self::List(l.into_iter().map(Self::datum_to_syntax).collect()),
            Self::Syntax(_) => self,
            Self::Symbol(s) => Self::Syntax(Syntax::new(s)),
            _ => self,
        }
    }
    fn syntax_to_datum(self) -> Self {
        match self {
            Self::List(l) => Self::List(l.into_iter().map(Self::syntax_to_datum).collect()),
            Self::Syntax(Syntax(s, _)) => Self::Symbol(s),
            _ => self,
        }
    }
    fn identifier(&self) -> bool {
        matches!(self, Self::Syntax(_))
    }
}

impl AdjustScope for Ast {
    fn adjust_scope(
        self,
        other_scope: Scope,
        operation: fn(HashSet<Scope>, Scope) -> HashSet<Scope>,
    ) -> Self {
        match self {
            Self::List(l) => Self::List(
                l.into_iter()
                    .map(|e| e.adjust_scope(other_scope, operation))
                    .collect(),
            ),
            Self::Syntax(s) => Self::Syntax(s.adjust_scope(other_scope, operation)),
            _ => self,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::{AdjustScope, Ast, Scope, ScopeCreator, Syntax};

    #[test]
    fn identifier_test_with_empty_syntax() {
        assert!(Ast::Syntax(Syntax::new("a".into())).identifier())
    }

    #[test]
    fn datum_to_syntax_with_identifier() {
        assert_eq!(
            Ast::Symbol("a".into()).datum_to_syntax(),
            Ast::Syntax(Syntax("a".into(), HashSet::new()))
        );
    }

    #[test]
    fn datum_to_syntax_with_number() {
        assert_eq!(Ast::Number(1.0).datum_to_syntax(), Ast::Number(1.0));
    }

    #[test]
    fn datum_to_syntax_with_list() {
        assert_eq!(
            Ast::List(vec![
                Ast::Symbol("a".into()),
                Ast::Symbol("b".into()),
                Ast::Symbol("c".into()),
            ])
            .datum_to_syntax(),
            Ast::List(vec![
                Ast::Syntax(Syntax("a".into(), HashSet::new())),
                Ast::Syntax(Syntax("b".into(), HashSet::new())),
                Ast::Syntax(Syntax("c".into(), HashSet::new())),
            ])
        );
    }

    #[test]
    fn datum_to_syntax_with_list_and_syntax() {
        assert_eq!(
            Ast::List(vec![
                Ast::Symbol("a".into()),
                Ast::Syntax(Syntax("b".into(), HashSet::from([Scope(0), Scope(1)]))),
                Ast::Symbol("c".into()),
            ])
            .datum_to_syntax(),
            Ast::List(vec![
                Ast::Syntax(Syntax("a".into(), HashSet::new())),
                Ast::Syntax(Syntax("b".into(), HashSet::from([Scope(0), Scope(1)]))),
                Ast::Syntax(Syntax("c".into(), HashSet::new())),
            ])
        );
    }
    #[test]
    fn syntax_to_datum_with_identifier() {
        assert_eq!(
            Ast::Syntax(Syntax("a".into(), HashSet::new())).syntax_to_datum(),
            Ast::Symbol("a".into()),
        );
    }

    #[test]
    fn syntax_to_datum_with_number() {
        assert_eq!(Ast::Number(1.0).syntax_to_datum(), Ast::Number(1.0));
    }

    #[test]
    fn syntax_to_datum_with_list() {
        assert_eq!(
            Ast::List(vec![
                Ast::Syntax(Syntax("a".into(), HashSet::new())),
                Ast::Syntax(Syntax("b".into(), HashSet::new())),
                Ast::Syntax(Syntax("c".into(), HashSet::new())),
            ])
            .syntax_to_datum(),
            Ast::List(vec![
                Ast::Symbol("a".into()),
                Ast::Symbol("b".into()),
                Ast::Symbol("c".into()),
            ])
        );
    }

    #[test]
    fn scope_equality_test() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_ne!(sc1, sc2);
        assert_eq!(sc2, sc2)
    }

    #[test]
    fn add_scope_test_empty_scope() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), HashSet::new())).add_scope(sc1),
            Ast::Syntax(Syntax("x".into(), HashSet::from([sc1])))
        );
    }

    #[test]
    fn add_scope_test_empty_scope_list() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        assert_eq!(
            Ast::List(vec![Ast::Symbol("x".into()), Ast::Symbol("y".into()),])
                .datum_to_syntax()
                .add_scope(sc1),
            Ast::List(vec![
                Ast::Syntax(Syntax("x".into(), HashSet::from([sc1]))),
                Ast::Syntax(Syntax("y".into(), HashSet::from([sc1]))),
            ])
        );
    }

    #[test]
    fn add_scope_test_non_empty_scope() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), HashSet::from([sc1]))).add_scope(sc2),
            Ast::Syntax(Syntax("x".into(), HashSet::from([sc1, sc2])))
        );
    }

    #[test]
    fn add_scope_test_add_duplicate() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), HashSet::from([sc1]))).add_scope(sc1),
            Ast::Syntax(Syntax("x".into(), HashSet::from([sc1,])))
        );
    }

    #[test]
    fn flip_scope_test_different() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), HashSet::from([sc1]))).flip_scope(sc2),
            Ast::Syntax(Syntax("x".into(), HashSet::from([sc1, sc2])))
        );
    }

    #[test]
    fn flip_scope_test_same() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), HashSet::from([sc1, sc2]))).flip_scope(sc2),
            Ast::Syntax(Syntax("x".into(), HashSet::from([sc1,])))
        );
    }
}

fn main() {
    println!("Hello, world!");
}
