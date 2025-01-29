use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    rc::Rc,
};

use crate::ast::{
    scope::{MultiScope, MutableMap, Scope, ShiftedMultiScope},
    Ast, Symbol,
};

use super::{
    binding::{Binding, CompileTimeBinding},
    phase::Phase,
};

pub type ResolvedModuleName = Symbol;
#[derive(Clone, Debug)]
pub struct Module {
    pub self_name: ResolvedModuleName,
    // immutable
    pub requires: HashMap<Phase, Vec<ResolvedModuleName>>,
    // immutable
    pub provides: HashMap<Phase, HashMap<Symbol, Binding>>,
    pub min_phase_level: Phase,
    pub max_phase_level: Phase,
    pub instantiate: fn(NameSpace, Phase, Phase),
}

// TODO: some of these hashmaps are cells, do we have to use internal mutablitly with MutableMap?
impl Module {
    pub fn new(
        self_name: Symbol,
        requires: HashMap<Phase, Vec<ResolvedModuleName>>,
        provides: HashMap<Phase, HashMap<Symbol, Binding>>,
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
#[derive(Clone, Debug)]
pub struct NameSpace {
    pub scope: Scope,
    // TODO: maybe use ecs/global database structure as opposed to rc refcelling everything - could
    // do same thing for scopes
    // all the hashmaps look like the mutable
    pub phases: MutableMap<Phase, Definitions>,
    // all module declarations avaliable in any namespace?
    // seems to be same object in all namespaces
    pub module_declarations: MutableMap<ResolvedModuleName, Module>,
    pub submodule_declarations: MutableMap<ResolvedModuleName, Module>,
    pub module_instances: MutableMap<(ResolvedModuleName, Phase), NameSpace>,
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
            phases: MutableMap::default(),
            module_declarations: MutableMap::default(),
            submodule_declarations: MutableMap::default(),
            module_instances: MutableMap::default(),
        }
    }
}

impl NameSpace {
    fn make_module_namespace(&mut self, name: ResolvedModuleName, for_submodule: bool) -> Self {
        let module_namespace = NameSpace {
            submodule_declarations: if for_submodule {
                Rc::clone(&self.submodule_declarations)
            } else {
                MutableMap::default()
            },
            module_declarations: Rc::clone(&self.module_declarations),
            ..Default::default()
        };
        self.module_instances
            .borrow_mut()
            .insert((name, Phase(0)), module_namespace.clone());
        module_namespace
    }
    fn namespace_to_module(&self, name: &ResolvedModuleName) -> Option<Ref<'_, Module>> {
        {
            Ref::filter_map(self.module_declarations.borrow(), |borrow| borrow.get(name))
                .or_else(|_| {
                    Ref::filter_map(self.submodule_declarations.borrow(), |borrow| {
                        borrow.get(name)
                    })
                })
                .ok()
        }
    }
    /// as_submodule: defualts to false
    fn declare_module(&self, name: ResolvedModuleName, m: Module, as_submodule: bool) {
        if as_submodule {
            self.submodule_declarations.clone()
        } else {
            self.module_declarations.clone()
        }
        .borrow_mut()
        .insert(name, m);
    }
}
