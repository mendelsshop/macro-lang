use std::collections::BTreeSet;

use crate::{Ast, Scope};

type ScopeSet = BTreeSet<Scope>;
#[derive(Clone, PartialEq, Debug)]
pub struct Syntax(pub Ast, pub ScopeSet);
const EMPTY_SCOPE: BTreeSet<Scope> = ScopeSet::new();

impl Ast {
    fn identifier(&self) -> bool {
        matches!( self, Ast::Syntax(s) if  matches!(**s,Syntax(Ast::Symbol(_), _)))
    }

    fn syntax_to_datum(self) -> Self {
        match self {
            Self::Syntax(s) => s.0,
            Self::List(l) => Self::List(l.into_iter().map(Self::syntax_to_datum).collect()),
            _ => self,
        }
    }
}
impl Syntax {
    fn bound_identifier(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}
