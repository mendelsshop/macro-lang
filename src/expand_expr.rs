use crate::{
    ast::{Ast, Symbol},
    binding::CompileTimeEnvoirnment,
    expand::rebuild,
    list,
    r#match::match_syntax,
    syntax::Syntax,
    AdjustScope, Expander,
};

impl Expander {
    pub fn add_core_forms(&mut self) {
        self.add_core_form("lambda".into(), Self::core_form_lambda);
        self.add_core_form("let-syntax".into(), Self::core_form_let_syntax);
        self.add_core_form("%app".into(), Self::core_form_app);
        self.add_core_form("quote".into(), Self::core_form_quote);
        self.add_core_form("quote-syntax".into(), Self::core_form_quote_syntax);
    }

    fn core_form_lambda(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        let m = match_syntax(
            s.clone(),
            list!(
                "lambda".into(),
                list!("id".into(), "...".into(),),
                "body".into()
            ),
        )?;
        let sc = self.scope_creator.new_scope();
        let ids = m("id".into()).ok_or("internal error".to_string())?;
        let ids = ids.clone().map_pair(|term, base| match term {
            Ast::Syntax(id) => {
                let id = id.add_scope(sc);
                Ok(Ast::Syntax(Box::new(id)))
            }
            Ast::TheEmptyList if base => Ok(Ast::TheEmptyList),
            _ => Err(format!(
                "{term} is not a symbol so it cannot be a parameter"
            )),
        })?;
        let body_env = ids.clone().foldl_pair(
            |term, base, env: Result<CompileTimeEnvoirnment, String>| match term {
                Ast::Syntax(ref id_syntax) => {
                    if let Ast::Symbol(id) = &id_syntax.0 {
                        let binding =
                            self.add_local_binding(Syntax(id.clone(), id_syntax.1.clone()));
                        env.map(|env| {
                            env.extend(binding.clone(), Ast::Symbol(self.variable.clone()))
                        })
                    } else {
                        Err(format!(
                            "{term} is not a symbol so it cannot be a parameter"
                        ))
                    }
                }
                Ast::TheEmptyList if base => env,
                _ => Err(format!(
                    "{term} is not a symbol so it cannot be a parameter"
                )),
            },
            Ok(env),
        )?;
        let exp_body = self.expand(
            m("body".into()).ok_or("internal error".to_string())?,
            body_env,
        )?;
        Ok(rebuild(
            s,
            list!(
                m("lambda".into()).ok_or("internal error".to_string())?,
                ids,
                exp_body
            ),
        ))
    }
    fn core_form_let_syntax(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        let m = match_syntax(
            s.clone(),
            list!(
                "let-syntax".into(),
                list!(list!("trans-id".into(), "trans-rhs".into()), "...".into()),
                "body".into()
            ),
        )?;
        let sc = self.scope_creator.new_scope();
        let trans_ids = m("trans-id".into())
            .ok_or("internal error".to_string())?
            .foldl(
                |current_id, ids| {
                    let mut ids = ids?;
                    match current_id {
                        Ast::Syntax(id) if matches!(id.0, Ast::Symbol(_)) => {
                            let id = id.add_scope(sc);
                            let id: Syntax<Symbol> = id.try_into()?;
                            ids.push(self.add_local_binding(id));

                            Ok(ids)
                        }
                        _ => Err(format!(
                            "{current_id} is not a symbol so it cannot be a parameter"
                        )),
                    }
                },
                Ok(vec![]),
            )??;
        let trans_vals = m("trans-rhs".into())
            .ok_or("internal error".to_string())?
            .foldl(
                |current_rhs, rhss: Result<Vec<Ast>, String>| {
                    rhss.and_then(|mut rhss| {
                        self.eval_for_syntax_binding(current_rhs, env.clone())
                            .map(|current_rhs| rhss.push(current_rhs));
                        Ok(rhss)
                    })
                },
                Ok(vec![]),
            )??;
        let body_env =
            CompileTimeEnvoirnment(trans_ids.into_iter().zip(trans_vals.into_iter()).collect());
        self.expand(
            m("body".into()).ok_or("internal error")?.add_scope(sc),
            body_env,
        )
    }
    fn core_form_app(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {}
    fn core_form_quote(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {}
    fn core_form_quote_syntax(
        &mut self,
        s: Ast,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
    }
}
