use crate::UniqueNumberManager;
use crate::{
    ast::{
        scope::{AdjustScope, Scope},
        syntax::Syntax,
        Ast, Pair, Symbol,
    },
    expander::{
        duplicate_check::{check_no_duplicate_ids, make_check_no_duplicate_table},
        expand,
    },
    list, sexpr,
};
use itertools::Itertools;

use super::{
    binding::CompileTimeBinding, expand::rebuild, expand_context::ExpandContext,
    r#match::match_syntax, Expander,
};
macro_rules! make_let_values_form {
    ($id:ident, $syntaxes:literal, $rec:literal) => {
        fn $id(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
            let variable = Ast::Symbol(self.variable.clone());
            let m = if $syntaxes {
                match_syntax(
                    s.clone(),
                    sexpr!((
                        "letrec-syntaxes+values"
                        ([("trans-id" "...") "trans-rhs"] "...")
                        ([("val-id" "...") "val-rhs"] "...")
                        body
                        "...+"
                    )),
                )?
            } else {
                match_syntax(
                    s.clone(),
                    sexpr!((
                        "let-values"
                        ([("val-id" "...") "val-rhs"] "...")
                        body
                        "...+"
                    )),
                )?
            };
            let sc = UniqueNumberManager::new_scope();
            let trans_idss = if $syntaxes {
                itertools::Itertools::try_collect(
                    m("trans-id".into())
                        .ok_or("internal error")?
                        .to_list_checked()?
                        .into_iter()
                        .map(|ids| {
                            expand::to_id_list(ids).map(|ids| {
                                ids.into_iter()
                                    .map(|id| id.add_scope(sc.clone()))
                                    .collect_vec()
                            })
                        }),
                )?
            } else {
                vec![]
            };

            let val_idss: Vec<_> = itertools::Itertools::try_collect(
                m("val-id".into())
                    .ok_or("internal error")?
                    .to_list_checked()?
                    .into_iter()
                    .map(|ids| {
                        expand::to_id_list(ids).map(|ids| {
                            ids.into_iter()
                                .map(|id| id.add_scope(sc.clone()))
                                .collect_vec()
                        })
                    }),
            )?;
            check_no_duplicate_ids(
                trans_idss
                    .clone()
                    .into_iter()
                    .chain(val_idss.clone())
                    .concat(),
                &s,
                make_check_no_duplicate_table(),
            )?;
            let mut rec_ctx = ctx.clone();
            let val_keyss = val_idss
                .clone()
                .into_iter()
                .flat_map(|ids| self.add_local_bindings(ids));
            rec_ctx
                .env
                .0
                .extend(val_keyss.map(|key| (key, variable.clone())));
            let trans_keyss = trans_idss
                .clone()
                .into_iter()
                .flat_map(|ids| self.add_local_bindings(ids))
                .collect_vec();
            let trans_valss = if $syntaxes {
                m("trans-rhs".into())
                    .ok_or("internal error")?
                    .to_list_checked()?
                    .into_iter()
                    .zip(trans_idss)
                    .map(|(vals, ids)| {
                        self.eval_for_syntaxes_binding(
                            vals.add_scope(sc.clone()),
                            ids.len(),
                            ctx.clone(),
                        )
                    })
                    .try_collect()?
            } else {
                vec![]
            };
            rec_ctx
                .env
                .0
                .extend(trans_keyss.into_iter().zip(trans_valss.concat()));
            let letrec_values_id = if $syntaxes {
                self.core_datum_to_syntax("letrec-values".into())
            } else {
                m("let-values".into()).ok_or("internal eror")?
            };
            let val_idss = list_to_cons(val_idss.into_iter(), |ids| {
                list_to_cons(ids.into_iter(), |x| {
                    Ast::Syntax(Box::new(x.clone().with(Ast::Symbol(x.0))))
                })
            });
            Ok(expand::rebuild(
                s.clone(),
                list!(
                    letrec_values_id,
                    Ast::map2(
                        val_idss,
                        m("val-rhs".into()).ok_or("internal error")?,
                        |ids, rhs| {
                            Ok(list!(
                                ids,
                                if $rec {
                                    self.expand(rhs.add_scope(sc.clone()), rec_ctx.clone())?
                                } else {
                                    self.expand(rhs, ctx.clone())?
                                }
                            ))
                        },
                    )?,
                    self.expand_body(m("body".into()).ok_or("internal error")?, sc, s, rec_ctx)?
                ),
            ))
        }
    };
}
fn list_to_cons<T>(list: impl DoubleEndedIterator<Item = T>, mut f: impl FnMut(T) -> Ast) -> Ast {
    list.into_iter()
        .rfold(Ast::TheEmptyList, |rest, current| list!(f(current); rest))
}
impl Expander {
    fn add_local_bindings(&mut self, ids: Vec<Syntax<Symbol>>) -> Vec<Symbol> {
        ids.into_iter()
            .map(|id| self.add_local_binding(id))
            .collect()
    }
    pub fn add_core_forms(&mut self) {
        self.add_core_form("lambda".into(), Self::core_form_lambda);
        self.add_core_form("case-lambda".into(), Self::core_form_case_lambda);
        self.add_core_form("let-values".into(), Self::core_form_let_values);
        self.add_core_form("letrec-values".into(), Self::core_form_letrec_values);
        self.add_core_form(
            "letrec-syntaxes+values".into(),
            Self::core_form_letrec_syntaxes_and_values,
        );
        self.add_core_form("#%datum".into(), Self::core_form_datum);
        self.add_core_form("#%app".into(), Self::core_form_app);
        self.add_core_form("quote".into(), Self::core_form_quote);
        self.add_core_form("quote-syntax".into(), Self::core_form_quote_syntax);
        self.add_core_form("if".into(), Self::core_form_if);
        self.add_core_form(
            "with-continuation-mark".into(),
            Self::core_form_with_continuation_mark,
        );
        self.add_core_form("begin".into(), Self::core_form_begin);
        self.add_core_form("begin0".into(), Self::core_form_begin0);
        self.add_core_form("set!".into(), Self::core_form_set);
        // from expand_top_level
        self.add_core_form("define-values".into(), Self::core_form_define_values);
        self.add_core_form("define-syntaxes".into(), Self::core_form_define_syntaxes);
    }

    fn make_lambda_expander(
        &mut self,
        s: Ast,
        formals: Ast,
        bodys: Ast,
        ctx: ExpandContext,
    ) -> Result<(Ast, Ast), String> {
        let sc = self.scope_creator.new_scope();
        let ids = self.parse_and_flatten_formals(formals.clone(), sc.clone())?;
        check_no_duplicate_ids(ids.clone(), &s, make_check_no_duplicate_table())?;
        let variable = Ast::Symbol(self.variable.clone());
        let keys = ids.into_iter().map(|id| self.add_local_binding(id));
        let mut body_ctx = ctx;
        body_ctx
            .env
            .0
            .extend(keys.map(|key| (key, variable.clone())));
        let exp_body = self.expand_body(bodys, sc.clone(), s, body_ctx)?;
        Ok((formals.add_scope(sc), exp_body))
    }
    fn core_form_lambda(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        let m = match_syntax(
            s.clone(),
            list!(
                "lambda".into(),
                "formals".into(),
                "body".into(),
                "...+".into()
            ),
        )?;
        let (formals, body) = self.make_lambda_expander(
            s.clone(),
            m("formals".into()).ok_or("internal error")?,
            m("body".into()).ok_or("internal error")?,
            ctx,
        )?;
        Ok(rebuild(
            s,
            list!(
                m("lambda".into()).ok_or("internal error".to_string())?,
                formals,
                body
            ),
        ))
    }
    fn core_form_case_lambda(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        let m = match_syntax(
            s.clone(),
            list!(
                "case-lambda".into(),
                list!("formals".into(), "body".into(), "...+".into()),
                "...".into()
            ),
        )?;
        let cm = match_syntax(
            s.clone(),
            list!("case-lambda".into(), "clause".into(), "...".into()),
        )?;
        let iter = m("formals".into())
            .ok_or("internal error")?
            .to_list_checked()?
            .into_iter()
            .zip(
                m("body".into())
                    .ok_or("internal error")?
                    .to_list_checked()?,
            )
            .zip(
                cm("clause".into())
                    .ok_or("internal error")?
                    .to_list_checked()?,
            )
            .try_rfold(Ast::TheEmptyList, |rest, ((formals, bodys), clause)| {
                let (formals, body) =
                    self.make_lambda_expander(s.clone(), formals, bodys, ctx.clone())?;
                Ok::<Ast, String>(list!(rebuild(clause, list!(formals, body));rest))
            })?;
        Ok(rebuild(
            s,
            list!(m("case-lambda".into()).ok_or("internal error")?; iter),
        ))
    }
    fn parse_and_flatten_formals(
        &self,
        formals: Ast,
        sc: Scope,
    ) -> Result<Vec<Syntax<Symbol>>, String> {
        fn parse_and_flatten_formals_loop(
            formals: Ast,
            all_formals: Ast,
            sc: Scope,
            formals_list: &mut Vec<Syntax<Symbol>>,
        ) -> Result<(), String> {
            match formals {
                Ast::Syntax(s) => match s.0 {
                    Ast::Symbol(ref sym) => {
                        formals_list.push(s.clone().with(sym.clone()));
                        Ok(())
                    }
                    Ast::TheEmptyList => Ok(()),
                    p @ Ast::Pair(_) => {
                        parse_and_flatten_formals_loop(p, all_formals, sc, formals_list)
                    }
                    p => Err(format!("not an identifier: {p}")),
                },
                Ast::TheEmptyList => Ok(()),
                Ast::Pair(p) => {
                    let Pair(car, cdr) = *p;
                    let s: Syntax<Symbol> = car
                        .clone()
                        .try_into()
                        .map_err(|_| format!("not and identifier {car}"))?;
                    let s = s.add_scope(sc.clone());
                    formals_list.push(s);
                    parse_and_flatten_formals_loop(cdr, all_formals, sc, formals_list)
                }
                _ => Err(format!("bad arguement sequence: {all_formals}")),
            }
        }
        let mut formal_list = vec![];
        parse_and_flatten_formals_loop(formals.clone(), formals, sc, &mut formal_list)
            .map(|()| formal_list)
    }
    make_let_values_form!(core_form_let_values, false, false);
    make_let_values_form!(core_form_letrec_values, true, false);
    make_let_values_form!(core_form_letrec_syntaxes_and_values, true, true);

    fn core_form_datum(&mut self, s: Ast, _ctx: ExpandContext) -> Result<Ast, String> {
        let m = match_syntax(s.clone(), list!("#%datum".into();  "datum".into()))?;
        let datum = m("datum".into()).ok_or("internal error")?;
        if matches!(datum, Ast::Syntax(ref s) if s.0.is_keyword()) {
            return Err(format!("keyword misused as an expression: {datum}"));
        }
        Ok(rebuild(
            s,
            list!(self.core_datum_to_syntax("quote".into()), datum),
        ))
    }
    fn core_form_app(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        let m = match_syntax(
            s.clone(),
            //TODO: should app be a syntax object
            list!("#%app".into(), "rator".into(), "rand".into(), "...".into()),
        )?;
        let rator = self.expand(
            m("rator".into()).ok_or("internal error".to_string())?,
            ctx.clone(),
        )?;
        let rand = m("rand".into())
            .ok_or("internal error".to_string())?
            .map(|rand| self.expand(rand, ctx.clone()))?;
        Ok(rebuild(
            s,
            Ast::Pair(Box::new(Pair(
                m("#%app".into()).ok_or("internal error")?,
                Ast::Pair(Box::new(Pair(rator, rand))),
            ))),
        ))
    }
    fn core_form_quote(&mut self, s: Ast, _ctx: ExpandContext) -> Result<Ast, String> {
        match_syntax(s.clone(), list!("quote".into(), "datum".into())).map(|_| s)
    }
    fn core_form_quote_syntax(&mut self, s: Ast, _ctx: ExpandContext) -> Result<Ast, String> {
        match_syntax(s.clone(), list!("quote-syntax".into(), "datum".into())).map(|_| s)
    }
    fn core_form_if(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        let m = match_syntax(
            s.clone(),
            list!(
                "if".into(),
                "condition".into(),
                "consequent".into(),
                "alternative".into()
            ),
        )?;
        Ok(rebuild(
            s,
            list!(
                m("if".into()).ok_or("internal_error")?,
                self.expand(m("condition".into()).ok_or("internal_error")?, ctx.clone())?,
                self.expand(m("consequent".into()).ok_or("internal_error")?, ctx.clone())?,
                self.expand(m("alternative".into()).ok_or("internal_error")?, ctx)?
            ),
        ))
    }
    fn core_form_with_continuation_mark(
        &mut self,
        s: Ast,
        ctx: ExpandContext,
    ) -> Result<Ast, String> {
        let m = match_syntax(
            s.clone(),
            list!(
                "with-continuation-mark".into(),
                "key".into(),
                "val".into(),
                "body".into()
            ),
        )?;
        Ok(rebuild(
            s,
            list!(
                m("with-continuation-mark".into()).ok_or("internal_error")?,
                self.expand(m("key".into()).ok_or("internal_error")?, ctx.clone())?,
                self.expand(m("val".into()).ok_or("internal_error")?, ctx.clone())?,
                self.expand(m("body".into()).ok_or("internal_error")?, ctx)?
            ),
        ))
    }
    fn make_begin(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        let m = match_syntax(s.clone(), list!("begin".into(), "e".into(), "...+".into()))?;
        Ok(rebuild(
            s,
            list!(m("begin".into()).ok_or("internal_error")?; m("e".into()).ok_or("internal_error")?.map(|e|self.expand(e, ctx.clone()))?),
        ))
    }
    fn core_form_begin(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        self.make_begin(s, ctx)
    }
    fn core_form_begin0(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        self.make_begin(s, ctx)
    }
    fn core_form_set(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        let m = match_syntax(s.clone(), list!("set!".into(), "id".into(), "rhs".into()))?;
        let id = m("id".into()).ok_or("internal error")?;
        let binding = self
            .resolve(&id.clone().try_into()?, false)
            .inspect_err(|e| {
                dbg!(format!("{e}"));
            })
            .map_err(|_| format!("no binding for assignment: {s}"))?;
        let t = ctx
            .env
            .lookup(&binding, &ctx.namespace, &s, self.variable.clone())?;
        if !matches!(t, CompileTimeBinding::Regular(Ast::Symbol(s)) if s == self.variable) {
            return Err(format!("cannot assign to syntax: {s}"));
        }
        let set = m("set!".into()).ok_or("internal error")?;
        let rhs = m("rhs".into()).ok_or("internal error")?;
        Ok(expand::rebuild(s, list!(set, id, rhs)))
    }
}
