use std::{cell::Ref, collections::HashMap};

use crate::ast::{scope::MutableMap, syntax::Syntax, Ast, Symbol};

use super::{
    binding::{self, Binding},
    phase::Phase,
};

type ModuleName = Symbol;
#[derive(Default, Clone, Debug)]
struct RequiresAndProvides {
    requires: MutableMap<ModuleName, HashMap<Phase, Vec<Required>>>,
    provides: MutableMap<ModuleName, HashMap<Symbol, Binding>>,
}

impl RequiresAndProvides {
    fn add_required_module(&self, module: ModuleName, phase: Phase) {
        self.requires
            .entry(module, |e| e.or_default().insert(phase, vec![]));
    }

    fn add_defined_or_required_id(
        &self,
        phase: Phase,
        binding: Binding,
        can_show: bool,
    ) -> Result<(), String> {
        todo!()
    }

    fn check_not_required_or_defined(
        &self,
        id: Syntax<Symbol>,
        phase: Phase,
    ) -> Result<(), String> {
        todo!()
    }

    fn extract_module_requires(
        &self,
        mod_path: &ModuleName,
        phase: Phase,
    ) -> Option<Ref<'_, Vec<Required>>> {
        self.requires
            .get(mod_path)
            .and_then(|require| Ref::filter_map(require, |require| require.get(&phase)).ok())
    }

    fn reset_provides(&self) {
        self.provides.clear();
    }

    fn add_provide(
        &self,
        sym: Symbol,
        phase: Phase,
        binding: Binding,
        id: Syntax<Symbol>,
    ) -> Result<(), String> {
        todo!()
    }
    fn attach_require_provide_property<T>(&self, s: Syntax<T>, phase: Phase) -> Ast {
        todo!()
    }
}
#[derive(Clone, Debug)]
pub struct Required {
    id: Syntax<Symbol>,
    phase: Phase,
    can_show: bool,
}
