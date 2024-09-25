use std::{collections::HashMap, fmt, rc::Rc};

use crate::ast::{syntax::Syntax, Ast, Symbol};

use super::{namespace::NameSpace, Expander};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Binding {
    Variable(Symbol),
    CoreBinding(Rc<str>),
}
impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Variable(s) => format!("{s}"),
                Self::CoreBinding(s) => format!("{s}"),
            }
        )
    }
}
impl From<Binding> for Symbol {
    fn from(value: Binding) -> Self {
        match value {
            Binding::Variable(s) => s,
            Binding::CoreBinding(c) => c.into(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum CompileTimeBinding {
    Regular(Ast),
    // maybe this should just be Function
    // as we need to capture expander state
    CoreForm(CoreForm),
}
pub type CoreForm = fn(&mut Expander, Ast, CompileTimeEnvoirnment) -> Result<Ast, String>;
#[derive(Clone, Debug)]
pub struct CompileTimeEnvoirnment(pub(crate) HashMap<Symbol, Ast>);

impl Default for CompileTimeEnvoirnment {
    fn default() -> Self {
        Self::new()
    }
}

impl CompileTimeEnvoirnment {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn extend(&self, key: Symbol, value: Ast) -> Self {
        let mut map = self.0.clone();
        map.insert(key, value);
        Self(map)
    }

    pub fn lookup(
        &self,
        key: &Binding,
        ns: NameSpace,
        // TODO: maybe core form can get their own type
        id: Symbol,
    ) -> Result<CompileTimeBinding, String> {
        match key {
            Binding::Variable(key) => self
                .0
                .get(key)
                .cloned()
                .map(CompileTimeBinding::Regular)
                .ok_or(format!("identifier used out of context: {key}")),
            Binding::CoreBinding(core) => Ok(ns
                .transformers
                .get(&core.clone().into())
                .cloned()
                .unwrap_or(CompileTimeBinding::Regular(Ast::Symbol(id)))),
        }
    }
}
impl Expander {
    pub fn free_identifier(&self, a: Syntax<Symbol>, b: Syntax<Symbol>) -> Result<bool, String> {
        let ab = self.resolve(&a, false)?;
        let bb = self.resolve(&b, false)?;
        Ok(ab == bb)
    }
    pub fn add_local_binding(&mut self, id: Syntax<Symbol>) -> Symbol {
        let symbol = self.scope_creator.gen_sym(&id.0 .0);
        Self::add_binding(id, Binding::Variable(symbol.clone()));
        symbol
    }
}
