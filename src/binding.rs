use crate::{syntax::Syntax, Expander, Function, Symbol};
use std::{collections::HashMap, fmt, rc::Rc};

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

#[derive(Clone)]
pub enum CompileTimeBinding {
    Variable,
    Procedure(Function),
}
#[derive(Clone)]
pub struct CompileTimeEnvoirnment(HashMap<Symbol, CompileTimeBinding>);

impl CompileTimeEnvoirnment {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn extend(&self, key: Symbol, value: CompileTimeBinding) -> Self {
        let mut map = self.0.clone();
        map.insert(key, value);
        Self(map)
    }

    pub fn lookup(
        &self,
        key: &Binding,
        // TODO: maybe core form can get their own type
        core_forms: HashMap<Rc<str>, Function>,
    ) -> Option<CompileTimeBinding> {
        match key {
            Binding::Variable(key) => self.0.get(key).cloned(),
            Binding::CoreBinding(core) => Some(core_forms
                .get(core)
                .map(|f| CompileTimeBinding::Procedure(f.clone()))
                .unwrap_or(CompileTimeBinding::Variable)),
        }
    }
}
impl Expander {
    pub fn free_identifier(&self, a: Syntax<Symbol>, b: Syntax<Symbol>) -> Result<bool, String> {
        let ab = self.resolve(&a)?;
        let bb = self.resolve(&b)?;
        Ok(ab == bb)
    }
    pub fn add_local_binding(&mut self, id: Syntax<Symbol>) -> Symbol {
        let symbol = self.scope_creator.gen_sym(&id.0 .0);
        self.add_binding(id, Binding::Variable(symbol.clone()));
        symbol
    }
}
