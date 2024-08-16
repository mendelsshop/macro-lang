use std::collections::BTreeSet;

use crate::{
    ast::{Ast, Pair, Symbol},
    binding::{CompileTimeBinding, CompileTimeEnvoirnment},
    list,
    r#match::{self, match_syntax},
    scope::AdjustScope,
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
            Err(_) => self.expand_app(s, env),
            Ok(CompileTimeBinding::Regular(Ast::Symbol(s))) if s == self.variable => {}
            Ok(t) => self.dispatch(t, Ast::Pair(Box::new(s)), env),
        }
    }

    pub(crate) fn apply_transformer(&mut self, m: Function, s: Ast) -> Result<Ast, String> {
        let intro_scope = self.scope_creator.new_scope();
        //println!("apply_transformer {s:?}");
        let intro_s = s.add_scope(intro_scope);
        let transformed_s = m.apply(Ast::Pair(Box::new(Pair(intro_s, Ast::TheEmptyList))))?;
        if !matches!(transformed_s, Ast::Syntax(_)) {
            return Err(format!("transformer produced non syntax: {transformed_s}"));
        }
        Ok(transformed_s.flip_scope(intro_scope))
    }

    fn dispatch(
        &mut self,
        t: CompileTimeBinding,
        s: Ast,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        match t {
            CompileTimeBinding::Regular(t) => match t {
                Ast::Function(transfromer) => {
                    self.expand(self.apply_transformer(transfromer, s)?, env)
                }
                Ast::Symbol(variable) if variable == self.variable => Ok(s),
                _ => Err(format!("illegal use of syntax: {t}")),
            },
            CompileTimeBinding::CoreForm(form) => form(self, s, env),
        }
    }
    pub fn eval_for_syntax_binding(
        &mut self,
        rhs: Ast,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        // let var_name = format!("problem `evaluating` macro {rhs}");
        //println!("macro body {rhs}");
        let expand = self.expand_transformer(rhs, env)?;
        //println!("macro body {expand}");
        self.expand_time_eval(self.compile(expand)?)
    }

    fn expand_transformer(&mut self, rhs: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        self.expand(rhs, CompileTimeEnvoirnment::new())
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
        Ok(rebuild(
            s,
            Ast::Pair(Box::new(Pair(
                "%app"
                    .into()
                    .datum_to_syntax(Some(BTreeSet::from([self.core_scope]))),
                rator,
            ))),
        ))
    }
    pub(crate) fn expand_identifier(
        &mut self,
        s: Syntax<Symbol>,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let binding = self.resolve(&s)?;
        let t = env
            .lookup(binding, self.core_forms.clone(), self.variable.clone())
            .map_err(|_| format!("illegal use of syntax {s:?}"))?;
        self.dispatch(t, Ast::Syntax(Box::new(Syntax(Ast::Symbol(s.0), s.1))), env)
    }
}

pub fn rebuild(s: Ast, rator: Ast) -> Ast {
    rator.datum_to_syntax(s.scope_set())
}
