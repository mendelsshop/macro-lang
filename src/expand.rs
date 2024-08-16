use std::{collections::BTreeSet, intrinsics::unreachable};

use crate::{
    ast::{Ast, Pair, Symbol},
    binding::{CompileTimeBinding, CompileTimeEnvoirnment},
    list,
    r#match::match_syntax,
    syntax::Syntax,
    Expander,
};

impl Expander {
    pub fn expand(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        match s {
            Ast::Syntax(syntax) => match syntax.0 {
                Ast::Symbol(symbol) => self.expand_identifier(Syntax(symbol, syntax.1), env),
                Ast::Pair(p) if p.0.identifier() => self.expand_id_application_form(s, env),
                _ => todo!(),
            },
            _ => todo!(),
        }
    }
    // constraints = s.len() > 0
    // constraints = s[0] == Ast::Syntax(Symbol)
    pub(crate) fn expand_id_application_form(
        &mut self,
        s: Pair,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let Ast::Syntax(ref id_syntax) = s.0 else {
            unreachable!()
        };
        let Ast::Symbol(id) = id_syntax.0 else {
            unreachable!();
        };
        let binding = self.resolve(&Syntax(id, id_syntax.1))?;
        let t = env.lookup(binding, self.core_forms, self.variable);
        match t {
            Ok(CompileTimeBinding::CoreForm(form)) => {}
            Err(_) => self.expand_app(s, env),
            Ok(CompileTimeBinding::Regular(Ast::Symbol(s))) if s == self.variable => {}
            Ok(t) => self.dispatch(t, Ast::Pair(Box::new(s)), env),
        }
    }

    fn dispatch(
        &self,
        t: CompileTimeBinding,
        s: Ast,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        todo!()
    }
    pub(crate) fn expand_app(
        &mut self,
        s: Ast,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let m = match_syntax(s, list!("rator".into(), "rand".into(), "...".into()))?;
        let rator = m("rator".into()).ok_or("internal error".to_string())?;
        let rand = m("rand".into())
            .ok_or("internal error".to_string())?
            .map(|rand| self.expand(rand, env))?;

        //let Pair(rator, rands) = s;
        //
        //Ok(Ast::Pair(Box::new(Pair(
        //    Ast::Syntax(Box::new(Syntax(
        //        "%app".into(),
        //        BTreeSet::from([self.core_scope]),
        //    ))),
        //    Ast::Pair(Box::new(Pair(
        //        self.expand(rator, env.clone())?,
        //        rands.map(|rand| self.expand(rand, env.clone()))?,
        //    ))),
        //))))
    }
    pub(crate) fn expand_identifier(
        &mut self,
        s: Syntax<Symbol>,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let binding = self.resolve(&s)?;
        let t = env
            .lookup(binding, self.core_forms, self.variable)
            .map_err(|_| format!("illegal use of syntax {s:?}"))?;
        self.dispatch(t, Ast::Syntax(Box::new(Syntax(Ast::Symbol(s.0), s.1))), env)
    }
}
