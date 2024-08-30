use std::{collections::BTreeSet, rc::Rc};

use crate::ast::{
    syntax::{Properties, SourceLocation, Syntax},
    Ast, Pair, Symbol,
};

use super::{
    binding::{Binding, CoreForm},
    r#match::try_match_syntax,
    Expander,
};

impl Expander {
    fn add_core_binding(&mut self, sym: Symbol) {
        self.add_binding(
            Syntax(
                sym.clone(),
                BTreeSet::from([self.core_scope]),
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

    pub fn core_form_symbol(&mut self, s: Ast) -> Result<Rc<str>, String> {
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
            let b = self.resolve(&s.with_ref(sym.clone()))?;
            match b {
                Binding::Variable(_) => Err(format!("{sym} is not a core form")),
                Binding::CoreBinding(s) => Ok(s.clone()),
            }
        })
    }
}
