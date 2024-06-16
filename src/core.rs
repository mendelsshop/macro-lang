use std::{collections::BTreeSet, rc::Rc};

use crate::{
    binding::{Binding, CoreForm},
    r#match::try_match_syntax,
    syntax::Syntax,
    Ast, Expander, Function, Symbol,
};

impl Expander {
    fn add_core_binding(&mut self, sym: Symbol) {
        self.add_binding(
            Syntax(sym.clone(), BTreeSet::from([self.core_scope])),
            Binding::CoreBinding(sym.0),
        );
    }
    fn add_core_form(&mut self, sym: Rc<str>, proc: CoreForm) {
        self.add_core_binding(sym.clone().into());
        self.core_forms.insert(sym, proc);
    }
    fn add_core_primitive(&mut self, sym: Rc<str>, proc: Function) {
        self.add_core_binding(sym.clone().into());
        self.core_primitives.insert(sym, proc);
    }

    fn core_form_symbol(&mut self, s: Ast) -> Result<Rc<str>, String> {
        try_match_syntax(
            s,
            Ast::List(vec![Ast::Symbol("id".into()), Ast::Symbol("_".into())]),
        )
        .and_then(|f| {
            // could this also be a plain symbol?
            let Some(Ast::Syntax(s)) = f("id".into()) else {
                return Err(format!("no such pattern variable id"));
            };
            let Ast::Symbol(sym) = s.0 else {
                return Err(format!("no such pattern variable id"));
            };
            let b = self.resolve(&Syntax(sym.clone(), s.1))?;
            match b {
                Binding::Variable(_) => Err(format!("{sym} is not a core form")),
                Binding::CoreBinding(s) => Ok(s.clone()),
            }
        })
    }
}
