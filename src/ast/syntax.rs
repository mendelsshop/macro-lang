use std::hash::Hash;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
};

use super::{
    scope::{Scope, ScopeSet},
    Ast, Pair, Symbol,
};

pub type Properties = BTreeMap<Symbol, Ast>;

#[derive(Clone, PartialEq, Debug, Eq, Hash, Default)]
pub struct SourceLocation {
    file: String,
    line: u32,
    column: u32,
}
#[derive(Clone, PartialEq, Debug)]
pub struct Syntax<T>(pub T, pub ScopeSet, pub SourceLocation, pub Properties);

impl<T> Syntax<T> {
    // TODO: make with take &self so we only need to clone properties srcloc scopes
    pub fn with<U>(self, other: U) -> Syntax<U> {
        Syntax(other, self.1, self.2, self.3)
    }
    pub fn with_ref<U>(&self, other: U) -> Syntax<U> {
        Syntax(other, self.1.clone(), self.2.clone(), self.3.clone())
    }
}

impl<T: Hash> Hash for Syntax<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}
impl<T: Eq> Eq for Syntax<T> {}
impl TryFrom<Ast> for Syntax<Symbol> {
    type Error = String;

    fn try_from(value: Ast) -> Result<Self, Self::Error> {
        let Ast::Syntax(s) = value else {
            return Err("not a syntax object".to_string());
        };
        let Ast::Symbol(id) = s.0.clone() else {
            return Err("not a syntax object wrapping a symbol".to_string());
        };
        Ok(s.with(id))
    }
}

const EMPTY_SCOPE: BTreeSet<Scope> = ScopeSet::new();
const EMPTY_PROPERTY: Properties = BTreeMap::new();
fn empty_srcloc() -> SourceLocation {
    SourceLocation {
        file: String::new(),
        line: 0,
        column: 0,
    }
}
fn empty_syntax() -> Syntax<Ast> {
    Syntax(
        Ast::Boolean(false),
        EMPTY_SCOPE,
        empty_srcloc(),
        EMPTY_PROPERTY,
    )
}

impl TryFrom<Syntax<Ast>> for Syntax<Symbol> {
    type Error = String;

    fn try_from(value: Syntax<Ast>) -> Result<Self, Self::Error> {
        if let Ast::Symbol(s) = value.0.clone() {
            Ok(value.with(s))
        } else {
            Err(format!("{value:?} is not a symbol"))
        }
    }
}
impl Ast {
    #[must_use]
    pub fn datum_to_syntax(
        self,
        scopes: Option<ScopeSet>,
        srcloc: Option<SourceLocation>,
        properties: Option<Properties>,
    ) -> Self {
        let wrap = |e| {
            Self::Syntax(Box::new(Syntax(
                e,
                scopes.clone().unwrap_or_default(),
                srcloc.clone().unwrap_or_default(),
                properties.clone().unwrap_or_default(),
            )))
        };
        match self {
            Self::Syntax(_) => self,
            _ if self.list() => wrap(
                self.map(|e| {
                    Ok(e.datum_to_syntax(scopes.clone(), srcloc.clone(), properties.clone()))
                })
                .unwrap(),
            ),
            Self::Pair(pair) => wrap(Self::Pair(Box::new(Pair(
                pair.0
                    .datum_to_syntax(scopes.clone(), srcloc.clone(), properties.clone()),
                pair.1
                    .datum_to_syntax(scopes.clone(), srcloc.clone(), properties.clone()),
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
        matches!( self, Self::Syntax(s) if  matches!(**s,Syntax(Self::Symbol(_), ..)))
    }
}
impl<T> Syntax<T> {
    #[must_use]
    pub fn new(expr: T) -> Self {
        Self(expr, EMPTY_SCOPE, empty_srcloc(), EMPTY_PROPERTY)
    }
    fn bound_identifier(&self, other: &Self) -> bool
    where
        T: PartialEq,
    {
        self.0 == other.0 && self.1 == other.1
    }
}
