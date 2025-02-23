use core::fmt;
use std::hash::Hash;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
};

use super::scope::{ScopeNoMultiScope, ShiftedMultiScope};
use super::{Ast, Pair, Symbol};

pub type Properties = BTreeMap<Symbol, Ast>;

#[derive(Clone, PartialEq, Debug, Eq, Hash, Default)]
pub struct SourceLocation {
    file: String,
    line: u32,
    column: u32,
}
#[derive(Clone, PartialEq)]
pub struct Syntax<T>(
    pub T,
    pub BTreeSet<ScopeNoMultiScope>,
    pub BTreeSet<ShiftedMultiScope>,
    pub SourceLocation,
    pub Properties,
);

impl<T: Debug> Debug for Syntax<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Syntax")
            .field(&self.0)
            // .field(&self.1).field(&self.2).field(&self.3)
            .finish()
    }
}

impl<T> Syntax<T> {
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Syntax<U> {
        Syntax(f(self.0), self.1, self.2, self.3, self.4)
    }
    pub fn map_ref<U>(&self, f: impl FnOnce(&T) -> U) -> Syntax<U> {
        Syntax(
            f(&self.0),
            self.1.clone(),
            self.2.clone(),
            self.3.clone(),
            self.4.clone(),
        )
    }
    // TODO: make with take &self so we only need to clone properties srcloc scopes
    pub fn with<U>(self, other: U) -> Syntax<U> {
        Syntax(other, self.1, self.2, self.3, self.4)
    }
    pub fn with_ref<U>(&self, other: U) -> Syntax<U> {
        Syntax(
            other,
            self.1.clone(),
            self.2.clone(),
            self.3.clone(),
            self.4.clone(),
        )
    }
}
impl<T: fmt::Display> fmt::Display for Syntax<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#'{}", self.0)
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

const EMPTY_SCOPES: BTreeSet<ScopeNoMultiScope> = BTreeSet::new();
const EMPTY_SHIFTED_MULTI_SCOPES: BTreeSet<ShiftedMultiScope> = BTreeSet::new();
const EMPTY_PROPERTY: Properties = BTreeMap::new();
const EMPTY_SOURCE_LOCATION: SourceLocation = SourceLocation {
    file: String::new(),
    line: 0,
    column: 0,
};
pub const EMPTY_SYNTAX: Syntax<Ast> = Syntax(
    Ast::Boolean(false),
    EMPTY_SCOPES,
    EMPTY_SHIFTED_MULTI_SCOPES,
    EMPTY_SOURCE_LOCATION,
    EMPTY_PROPERTY,
);
const fn empty_syntax() -> Syntax<Ast> {
    EMPTY_SYNTAX
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
        scopes: Option<BTreeSet<ScopeNoMultiScope>>,
        shifted_multi_scopes: Option<BTreeSet<ShiftedMultiScope>>,
        srcloc: Option<SourceLocation>,
        properties: Option<Properties>,
    ) -> Self {
        let wrap = |e| {
            Self::Syntax(Box::new(Syntax(
                e,
                scopes.clone().unwrap_or_default(),
                shifted_multi_scopes.clone().unwrap_or_default(),
                srcloc.clone().unwrap_or_default(),
                properties.clone().unwrap_or_default(),
            )))
        };
        match self {
            Self::Syntax(_) => self,
            _ if self.list() => wrap(
                self.map(|e| {
                    Ok(e.datum_to_syntax(
                        scopes.clone(),
                        shifted_multi_scopes.clone(),
                        srcloc.clone(),
                        properties.clone(),
                    ))
                })
                .unwrap(),
            ),
            Self::Pair(pair) => wrap(Self::Pair(Box::new(Pair(
                pair.0.datum_to_syntax(
                    scopes.clone(),
                    shifted_multi_scopes.clone(),
                    srcloc.clone(),
                    properties.clone(),
                ),
                pair.1.datum_to_syntax(
                    scopes.clone(),
                    shifted_multi_scopes.clone(),
                    srcloc.clone(),
                    properties.clone(),
                ),
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
    pub const fn identifier(&self) -> bool {
        matches!( self, Self::Syntax(s) if  matches!(**s,Syntax(Self::Symbol(_), ..)))
    }
}
impl<T> Syntax<T> {
    #[must_use]
    pub const fn new(expr: T) -> Self {
        Self(
            expr,
            EMPTY_SCOPES,
            EMPTY_SHIFTED_MULTI_SCOPES,
            EMPTY_SOURCE_LOCATION,
            EMPTY_PROPERTY,
        )
    }
}
