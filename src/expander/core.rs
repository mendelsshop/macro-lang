use std::{collections::BTreeSet, rc::Rc};

use crate::ast::{
    syntax::{Properties, SourceLocation, Syntax},
    Ast, Pair, Symbol,
};

use super::{
    binding::{Binding, CompileTimeBinding, CoreForm},
    namespace::NameSpace,
    r#match::try_match_syntax,
    Expander,
};

impl Expander {
    fn add_core_binding(&mut self, sym: Symbol) {
        Self::add_binding(
            Syntax(
                sym.clone(),
                BTreeSet::from([self.core_scope.clone()]),
                SourceLocation::default(),
                Properties::new(),
            ),
            Binding::CoreBinding(sym.0),
        );
    }
    pub fn add_core_form(&mut self, sym: Rc<str>, proc: CoreForm) {
        self.add_core_binding(sym.clone().into());
        self.core_forms.insert(sym, proc);
    }
    pub fn add_core_primitive(&mut self, sym: Rc<str>, proc: Ast) {
        self.add_core_binding(sym.clone().into());
        self.core_primitives.insert(sym, proc);
    }

    pub fn declare_core_top_level(&mut self, ns: &mut NameSpace) {
        ns.transformers.extend(
            self.core_forms
                .clone()
                .into_iter()
                .map(|(key, value)| (key.into(), CompileTimeBinding::CoreForm(value))),
        );
        ns.variables.extend(
            self.core_primitives
                .clone()
                .into_iter()
                .map(|(key, value)| (key.into(), value)),
        );
    }

    pub fn core_form_symbol(& self, s: Ast) -> Result<Rc<str>, String> {
        try_match_syntax(
            s,
            Ast::Pair(Box::new(Pair(
                Ast::Symbol("id".into()),
                Ast::Symbol("_".into()),
            ))),
        )
        .and_then(|f| {
            // could this also be a plain symbol?
            let Some(Ast::Syntax(s)) = f("id".into()) else {
                return Err("no such pattern variable id".to_string());
            };
            let Ast::Symbol(ref sym) = s.0 else {
                return Err("no such pattern variable id".to_string());
            };
            let b = self.resolve(&s.with_ref(sym.clone()), false)?;
            match b {
                Binding::Variable(_) => Err(format!("{sym} is not a core form")),
                Binding::CoreBinding(s) => Ok(s.clone()),
            }
        })
    }
}
