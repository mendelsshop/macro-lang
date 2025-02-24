use std::{collections::HashMap, rc::Rc};

use crate::{
    ast::{
        syntax::{Properties, SourceLocation, Syntax},
        Ast, Symbol,
    },
    sexpr,
};

use super::{
    binding::{Binding, CompileTimeBinding, CoreForm, ModuleBinding},
    module_path::ResolvedModulePath,
    namespace::{Module, NameSpace},
    phase::Phase,
    r#match::try_match_syntax,
    Expander,
};

impl Expander {
    fn add_core_binding(&self, sym: Symbol) -> Result<(), String> {
        Self::add_binding(
            Syntax(
                sym.clone(),
                self.core_syntax.1.clone(),
                self.core_syntax.2.clone(),
                SourceLocation::default(),
                Properties::new(),
            ),
            Phase(0),
            Binding::Module(ModuleBinding {
                from_module: "#%core".into(),
                from_phase: Phase(0),
                from_symbol: sym.clone(),
                nominal_from_module: "#%core".into(),
                nominal_from_phase: Phase(0),
                nominal_from_symbol: sym,
                nominal_require_phase: Phase(0),
            }),
        )
    }

    pub fn add_core_form(&mut self, sym: Rc<str>, proc: CoreForm) {
        self.add_core_binding(sym.clone().into());
        self.core_forms.insert(sym, proc);
    }
    pub fn add_core_primitive(&mut self, sym: Rc<str>, proc: Ast) {
        self.add_core_binding(sym.clone().into());
        self.core_primitives.insert(sym, proc);
    }

    pub fn declare_core_module(&mut self, ns: &NameSpace) {
        let primitives = self.core_primitives.clone();
        let transformers = self.core_forms.clone();
        ns.declare_module(
            "#%core".into(),
            Module::new(
                "#%core".into(),
                HashMap::new(),
                HashMap::from([(
                    Phase(0),
                    self.core_primitives
                        .keys()
                        .chain(self.core_forms.keys())
                        .map(|sym| {
                            let sym = sym.clone();
                            (
                                sym.clone().into(),
                                ModuleBinding {
                                    from_module: "#%core".into(),
                                    from_phase: Phase(0),
                                    from_symbol: sym.clone().into(),
                                    nominal_from_module: "#%core".into(),
                                    nominal_from_phase: Phase(0),
                                    nominal_from_symbol: sym.into(),
                                    nominal_require_phase: Phase(0),
                                },
                            )
                        })
                        .collect(),
                )]),
                Phase(0),
                Phase(1),
                Rc::new(move |ns, _phase, phase_level| match phase_level {
                    Phase(0) => {
                        primitives
                            .clone()
                            .into_iter()
                            .map(|(key, value)| (key.into(), value))
                            .for_each(|(sym, value)| {
                                ns.namespace_set_variable(phase_level, sym, value);
                            });
                    }
                    Phase(1) => {
                        transformers
                            .clone()
                            .into_iter()
                            .map(|(key, value)| (key.into(), value))
                            .for_each(|(sym, value)| {
                                ns.namespace_set_transformer(
                                    phase_level,
                                    sym,
                                    CompileTimeBinding::CoreForm(value),
                                );
                            });
                    }
                    _ => unreachable!(),
                }),
            ),
            false,
        );
    }

    pub fn core_form_symbol(s: Ast, phase: Phase) -> Result<Symbol, String> {
        try_match_syntax(s, sexpr!((id . "_"))).and_then(|f| {
            // could this also be a plain symbol?
            let sym: Syntax<Symbol> = f("id".into()).ok_or("internal error")?.try_into()?;
            let b = Self::resolve(&sym, phase, false).inspect_err(|e| {
                dbg!(format!("{e}"));
            })?;
            match b {
                Binding::Module(s)
                    if s.from_module == ResolvedModulePath::Symbol("#%core".into()) =>
                {
                    Ok(s.from_symbol)
                }
                _ => Err(format!("{sym} is not a core form")),
            }
        })
    }
}
