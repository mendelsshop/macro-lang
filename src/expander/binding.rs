use std::{collections::HashMap, fmt};

use crate::ast::{syntax::Syntax, Ast, Symbol};

use super::{expand_context::ExpandContext, namespace::NameSpace, phase::Phase, Expander};

pub type ModulePathIndex = Symbol;
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct ModuleBinding {
    pub from_module: ModulePathIndex,
    pub from_phase: Phase,
    pub from_symbol: Symbol,
    pub norminal_from_module: ModulePathIndex,
    pub norminal_from_phase: Phase,
    pub norminal_from_symbol: Symbol,
    pub norminal_require_phase: Phase,
}
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Binding {
    Local(Symbol),
    Module(ModuleBinding),
}
impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Local(s) => format!("{s}"),
                Self::Module(s) => format!("{}", s.norminal_from_symbol),
            }
        )
    }
}
impl From<Binding> for Symbol {
    fn from(value: Binding) -> Self {
        match value {
            Binding::Local(s) => s,
            Binding::Module(c) => c.norminal_from_symbol,
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
pub type CoreForm = fn(&mut Expander, Ast, ExpandContext) -> Result<Ast, String>;
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

    /// variable coressponds to Expander.variable
    pub fn lookup<T: fmt::Display>(
        &self,
        key: &Binding,
        ns: &NameSpace,
        // TODO: maybe core form can get their own type
        phase: Phase,
        id: &T,
        variable: Symbol,
    ) -> Result<CompileTimeBinding, String> {
        match key {
            Binding::Local(key) => self
                .0
                .get(key)
                .cloned()
                .map(CompileTimeBinding::Regular)
                .ok_or(format!("identifier used out of context: {id}")),
            Binding::Module(core) => {
                let module = ns
                    .namespace_to_module_namespace(
                        &core.from_module,
                        phase - core.from_phase,
                        false,
                    )
                    .map_err(|e| e.unwrap_or(format!("no module found")))?;
                Ok(module
                    .namespace_get_transformer(core.from_phase, &core.from_symbol)
                    .unwrap_or(CompileTimeBinding::Regular(Ast::Symbol(variable))))
            }
        }
    }
}
impl Expander {
    pub fn free_identifier(&mut self, a: Syntax<Symbol>, b: Syntax<Symbol>, phase: Phase) -> bool {
        let a_sym = a.0.clone();
        let b_sym = b.0.clone();
        let ab = self.resolve(a, phase, false);
        let bb = self.resolve(b, phase, false);
        match (ab, bb) {
            (Ok(Binding::Local(f0_self)), Ok(Binding::Local(f0_other))) => f0_self == (f0_other),
            (Ok(Binding::Module(f0_self)), Ok(Binding::Module(f0_other))) => {
                f0_self.from_module == f0_other.from_module
                    && f0_self.from_phase == f0_other.from_phase
                    && f0_self.from_symbol == f0_other.from_symbol
            }
            _ => a_sym == b_sym,
        }
    }
    pub fn add_local_binding(&mut self, id: Syntax<Symbol>, phase: Phase) -> Symbol {
        let symbol = self.scope_creator.gen_sym(&id.0 .0);
        self.add_binding(id, phase, Binding::Local(symbol.clone()));
        symbol
    }
}
