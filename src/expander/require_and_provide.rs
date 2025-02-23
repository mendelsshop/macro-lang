use std::{cell::Ref, collections::HashMap};

use crate::ast::{scope::MutableMap, syntax::Syntax, Ast, Symbol};

use super::{
    binding::{Binding, ModuleBinding},
    phase::Phase,
    Expander,
};

type ModuleName = Symbol;
#[derive(Default, Clone, Debug)]
pub struct RequiresAndProvides {
    requires: MutableMap<ModuleName, HashMap<Phase, Vec<Required>>>,
    provides: MutableMap<Phase, HashMap<Symbol, Binding>>,
}

impl RequiresAndProvides {
    fn add_required_module(&self, module: ModuleName, phase: Phase) {
        self.requires
            .entry(module, |e| e.or_default().insert(phase, vec![]));
    }

    fn add_defined_or_required_id(
        &self,
        phase: Phase,
        id: Syntax<Symbol>,
        binding: ModuleBinding,
        can_shadow: bool,
    ) -> Result<(), String> {
        if phase != binding.norminal_from_phase + binding.norminal_require_phase {
            return Err(format!(
                "internal error: binding phase does not match nominal phase"
            ));
        }
        self.requires.entry(binding.norminal_from_module, |at_mod| {
            at_mod
                .or_default()
                .entry(binding.norminal_require_phase)
                .or_default()
                .insert(
                    0,
                    Required {
                        id,
                        phase,
                        can_shadow,
                    },
                );
        });
        Ok(())
    }

    fn check_not_required_or_defined(
        &self,
        id: Syntax<Symbol>,
        phase: Phase,
    ) -> Result<(), String> {
        if let Binding::Module(b) = Expander::resolve(&id, phase, true)? {
            if let Some(at_mod) = self.requires.get(&b.norminal_from_module) {
                at_mod
                    .get(&b.norminal_require_phase)
                    .into_iter()
                    .flatten()
                    .try_for_each(|require| {
                        if id.0 == require.id.0 && !require.can_shadow {
                            Err(format!("already required or defined: {id}"))
                        } else {
                            Ok(())
                        }
                    })?
            }
        }
        Ok(())
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
        _id: &Syntax<Symbol>,
    ) -> Result<(), String> {
        self.provides.entry(phase, |at_phase| {
            let or_default = at_phase.or_default();
            match (or_default.get(&sym), binding) {
                (Some(Binding::Module(b)), Binding::Module(binding))
                    if b.from_module == binding.from_module
                        && b.from_phase == binding.from_phase
                        && b.from_symbol == binding.from_symbol =>
                {
                    Ok(())
                }
                (None, binding) => {
                    or_default.insert(sym, binding);
                    Ok(())
                }
                _ => Err(format!(
                    "name already provided by a different binding: {sym}"
                )),
            }
        })
    }
    // TODO: better way to handle syntax property mabye add ast hashmap
    fn attach_require_provide_property<T>(&self, s: Syntax<T>, phase: Phase) -> Ast {
        todo!()
    }
}
#[derive(Clone, Debug)]
pub struct Required {
    id: Syntax<Symbol>,
    phase: Phase,
    can_shadow: bool,
}
