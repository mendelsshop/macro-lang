use std::{cell::Ref, collections::HashMap, rc::Rc};

use crate::ast::{
    scope::{MultiScope, MutableMap, Scope, ShiftedMultiScope},
    Ast, Symbol,
};

use super::{
    binding::{CompileTimeBinding, ModuleBinding},
    phase::Phase,
};

pub type ResolvedModuleName = Symbol;
#[derive(Clone)]
pub struct Module {
    pub self_name: ResolvedModuleName,
    // immutable
    pub requires: HashMap<Phase, Vec<ResolvedModuleName>>,
    // immutable
    // TODO: should this allow non module bindings
    pub provides: HashMap<Phase, HashMap<Symbol, ModuleBinding>>,
    pub min_phase_level: Phase,
    pub max_phase_level: Phase,
    pub instantiate: Rc<dyn Fn(NameSpace, Phase, Phase)>,
}

impl std::fmt::Debug for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Module")
            .field("self_name", &self.self_name)
            .field("requires", &self.requires)
            .field("provides", &self.provides)
            .field("min_phase_level", &self.min_phase_level)
            .field("max_phase_level", &self.max_phase_level)
            .finish()
    }
}

// TODO: some of these hashmaps are cells, do we have to use internal mutablitly with MutableMap?
impl Module {
    pub fn new(
        self_name: Symbol,
        requires: HashMap<Phase, Vec<ResolvedModuleName>>,
        provides: HashMap<Phase, HashMap<Symbol, ModuleBinding>>,
        min_phase_level: Phase,
        max_phase_level: Phase,
        instantiate: Rc<dyn Fn(NameSpace, Phase, Phase)>,
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

#[derive(Clone, Debug, Default)]
pub struct Definitions {
    pub variables: HashMap<Symbol, Ast>,
    pub transformers: HashMap<Symbol, CompileTimeBinding>,
    // although it says this should be mutable looking at how it is used seems to show its always
    // true
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
                self.submodule_declarations.clone()
            } else {
                MutableMap::default()
            },
            module_declarations: self.module_declarations.clone(),
            ..Default::default()
        };
        self.module_instances
            .insert((name, Phase(0)), module_namespace.clone());
        module_namespace
    }
    pub fn namespace_to_module(&self, name: &ResolvedModuleName) -> Option<Ref<'_, Module>> {
        {
            self.module_declarations
                .get(name)
                .or_else(|| self.submodule_declarations.get(name))
        }
    }
    /// as_submodule: defualts to false
    pub fn declare_module(&self, name: ResolvedModuleName, m: Module, as_submodule: bool) {
        if as_submodule {
            self.submodule_declarations.clone()
        } else {
            self.module_declarations.clone()
        }
        .insert(name, m);
    }

    // min_phase: defualts to Phase(0)
    fn namespace_module_instantiate(
        &self,
        name: &ResolvedModuleName,
        phase_shift: Phase,
        min_phase: Phase,
    ) -> Result<(), String> {
        // since we use create the error variant should never be none, if we had dependent types we
        // wouldn't need the unwrap
        let module_namespace = self
            .namespace_to_module_namespace(name, phase_shift, true)
            .map_err(Option::unwrap)?;

        let module = self
            .namespace_to_module(&name)
            .ok_or(format!("no module found {name}"))?;
        module
            .requires
            .iter()
            .try_for_each(|(require_phase, modules)| {
                modules.iter().try_for_each(|module| {
                    self.namespace_module_instantiate(
                        module,
                        phase_shift + *require_phase,
                        min_phase,
                    )
                })
            })?;
        (module.min_phase_level.0..module.max_phase_level.0 + 1)
            .map(Phase)
            .for_each(|phase_level| {
                let phase = phase_level + phase_shift;
                if phase >= min_phase {
                    module_namespace.namespace_to_definitions(phase_level, |definitions| {
                        if !definitions.instantiated {
                            definitions.instantiated = true;
                            (module.instantiate)(
                                module_namespace.clone(),
                                phase_shift,
                                phase_level,
                            );
                        }
                    });
                }
            });
        Ok(())
    }

    fn namespace_module_visit(
        &self,
        name: &ResolvedModuleName,
        phase: Phase,
    ) -> Result<(), String> {
        self.namespace_module_instantiate(name, phase, Phase(1))
    }
    /// create: defaults to false
    pub fn namespace_to_module_namespace(
        &self,
        name: &ResolvedModuleName,
        phase: Phase,
        create: bool,
    ) -> Result<NameSpace, Option<String>> {
        if let Some(v) = self
            .module_instances
            .get(&(name.clone(), phase))
            .map(|c| c.clone())
        {
            Ok(v)
        } else if !create {
            Err(None)
        } else if self.namespace_to_module(&name).is_none() {
            Err(Some(format!("no module declared to instantiate {name}")))
        } else {
            let module_namespace = NameSpace {
                module_declarations: self.module_declarations.clone(),
                submodule_declarations: self.submodule_declarations.clone(),
                module_instances: self.module_instances.clone(),
                ..Default::default()
            };
            self.module_instances
                .insert((name.clone(), phase), module_namespace.clone());
            Ok(module_namespace)
        }
    }

    fn namespace_to_definitions<T>(
        &self,
        phase_level: Phase,
        k: impl FnOnce(&mut Definitions) -> T,
    ) -> T {
        self.phases
            .entry(phase_level, |definitions| k(definitions.or_default()))
    }

    pub fn namespace_set_variable(&self, phase_level: Phase, name: Symbol, value: Ast) {
        self.namespace_to_definitions(phase_level, |d| d.variables.insert(name, value));
    }
    pub fn namespace_set_transformer(
        &self,
        phase_level: Phase,
        name: Symbol,
        value: CompileTimeBinding,
    ) {
        self.namespace_to_definitions(phase_level, |d| d.transformers.insert(name, value));
    }
    fn namespace_get_variable(&self, phase_level: Phase, name: &Symbol) -> Option<Ast> {
        self.namespace_to_definitions(phase_level, |d| d.variables.get(name).cloned())
    }
    pub fn namespace_get_transformer(
        &self,
        phase_level: Phase,
        name: &Symbol,
    ) -> Option<CompileTimeBinding> {
        self.namespace_to_definitions(phase_level, |d| d.transformers.get(name).cloned())
    }
}
