use std::collections::HashMap;

use crate::ast::{
    scope::{MultiScope, MutableMap, Scope, ShiftedMultiScope},
    Ast, Symbol,
};

use super::{binding::CompileTimeBinding, phase::Phase};

pub type ResolvedModuleName = Symbol;
#[derive(Clone, Debug)]
pub struct Module {
    pub self_name: Symbol,
    pub requires: HashMap<Phase, Vec<ResolvedModuleName>>,
    pub provides: HashMap<Phase, Vec<ResolvedModuleName>>,
    pub min_phase_level: Phase,
    pub max_phase_level: Phase,
    pub instantiate: fn(NameSpace, Phase, Phase),
}

// TODO: some of these hashmaps are cells, do we have to use internal mutablitly with MutableMap?
impl Module {
    pub fn new(
        self_name: Symbol,
        requires: HashMap<Phase, Vec<ResolvedModuleName>>,
        provides: HashMap<Phase, Vec<ResolvedModuleName>>,
        min_phase_level: Phase,
        max_phase_level: Phase,
        instantiate: fn(NameSpace, Phase, Phase),
    ) -> Self {
        Self {
            self_name,
            requires,
            provides,
            min_phase_level,
            max_phase_level,
            instantiate,
        }
    }
}
// Currently just keeps top level bindings + transformers
#[derive(Clone, Debug)]
pub struct NameSpace {
    pub scope: Scope,
    pub phases: HashMap<Phase, Definitions>,
    pub module_declarations: HashMap<ResolvedModuleName, Module>,
    pub submodule_declarations: HashMap<ResolvedModuleName, Module>,
    pub module_instances: HashMap<(ResolvedModuleName, Phase), NameSpace>,
}

#[derive(Clone, Debug)]
pub struct Definitions {
    pub variables: HashMap<Symbol, Ast>,
    pub transformers: HashMap<Symbol, CompileTimeBinding>,
    pub instantiated: bool,
}
impl Default for NameSpace {
    fn default() -> Self {
        Self {
            scope: Scope::ShiftedMultiScope(ShiftedMultiScope(
                Phase(0),
                MultiScope(MutableMap::default()),
            )),
            phases: HashMap::new(),
            module_declarations: HashMap::new(),
            submodule_declarations: HashMap::new(),
            module_instances: HashMap::new(),
        }
    }
}

impl NameSpace {
    fn namespace_to_module(&self, name: &ResolvedModuleName) -> Option<&Module> {
        self.module_declarations
            .get(name)
            .or_else(|| self.submodule_declarations.get(name))
    }
}
