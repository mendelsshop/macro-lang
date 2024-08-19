use std::{collections::BTreeSet, fmt::Debug};

use crate::{ast::Pair, scope::ScopeSet, Ast, Scope, Symbol};

#[derive(Clone, PartialEq, Debug, Eq, Hash)]
pub struct Syntax<T: Clone + PartialEq + Debug>(pub T, pub ScopeSet);
impl TryFrom<Ast> for Syntax<Symbol> {
    type Error = String;

    fn try_from(value: Ast) -> Result<Self, Self::Error> {
        let Ast::Syntax(s) = value else {
            return Err("not a syntax object".to_string());
        };
        let Ast::Symbol(id) = s.0 else {
            return Err("not a syntax object wrapping a symbol".to_string());
        };
        Ok(Self(id, s.1))
    }
}

const EMPTY_SCOPE: BTreeSet<Scope> = ScopeSet::new();
const EMPTY_SYNTAX: Syntax<Ast> = Syntax(Ast::Boolean(false), EMPTY_SCOPE);

impl TryFrom<Syntax<Ast>> for Syntax<Symbol> {
    type Error = String;

    fn try_from(value: Syntax<Ast>) -> Result<Self, Self::Error> {
        if let Ast::Symbol(s) = value.0 {
            Ok(Self(s, value.1))
        } else {
            Err(format!("{value:?} is not a symbol"))
        }
    }
}
impl Ast {
    #[must_use]
    pub fn datum_to_syntax(self, scopes: Option<ScopeSet>) -> Self {
        let wrap = |e| Self::Syntax(Box::new(Syntax(e, scopes.clone().unwrap_or_default())));
        match self {
            Self::Syntax(_) => self,
            Self::Pair(pair) => wrap(Self::Pair(Box::new(Pair(
                pair.0.datum_to_syntax(scopes.clone()),
                pair.1.datum_to_syntax(scopes.clone()),
            )))),
            _ => wrap(self),
        }
    }
    pub(crate) fn syntax_to_datum(self) -> Self {
        match self {
            Self::Syntax(s) => s.0.syntax_to_datum(),
            Self::Pair(pair) => Self::Pair(Box::new(Pair(
                pair.0.syntax_to_datum(),
                pair.1.syntax_to_datum(),
            ))),
            _ => self,
        }
    }
    pub fn identifier(&self) -> bool {
        matches!( self, Self::Syntax(s) if  matches!(**s,Syntax(Self::Symbol(_), _)))
    }
}
impl<T: Clone + Debug + PartialEq> Syntax<T> {
    #[must_use]
    pub fn new(expr: T) -> Self {
        Self(expr, BTreeSet::new())
    }
    fn bound_identifier(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}
