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
    list,
};
use itertools::Itertools;

use super::{
    binding::CompileTimeBinding, expand::rebuild, expand_context::ExpandContext, Expander,
};
matcher::match_syntax_as!(LetSyntaxMatcher as

    (
        // TODO: letrec_syntaxes+values
        letrec_syntaxes_and_values
        (((trans_id ...) trans_rhs) ...)
        (((val_id ...) val_rhs) ...)
        body ..+
    )
);
matcher::match_syntax_as!(
LetMatcher as
                (
                    let_values
                    (((val_id ...) val_rhs) ...)
                    body
                    ..+
                ));
macro_rules! make_let_values_form {
    (syntax $id:ident,  $rec:literal) => {
        make_let_values_form!(
            $id,
            |s: Ast| LetSyntaxMatcher::matches(s),
            |m: LetSyntaxMatcher, sc: Scope| itertools::Itertools::try_collect(
                m.trans_id.to_list_checked()?.into_iter().map(|ids| {
                    expand::to_id_list(ids).map(|ids| {
                        ids.into_iter()
                            .map(|id| id.add_scope(sc.clone()))
                            .collect_vec()
                    })
                }),
            )?,
            |m, trans_idss, this, ctx, sc| m
                .trans_rhs
                .to_list_checked()?
                .into_iter()
                .zip(trans_idss)
                .map(|(vals, ids)| {
                    this.eval_for_syntaxes_binding(
                        vals.add_scope(sc.clone()),
                        ids.len(),
                        ctx.clone(),
                    )
                })
                .try_collect()?,
            |_, this| this.core_datum_to_syntax("letrec-values".into()),
            $rec
        );
    };

    ( $id:ident,  $rec:literal) => {
        make_let_values_form!(
            $id,
            |s: Ast| LetMatcher::matches(s.clone()),
            |_, _| vec![],
            |_, _, _, _, _| vec![],
            |m, _| m.let_values,
            $rec
        );
    };
    ($id:ident, $m:expr, $trans_idss:expr, $trans_valss:expr, $letrecvalues:expr, $rec:literal) => {
        fn $id(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
            let variable = Ast::Symbol(self.variable.clone());
            //TODO: compile time matcher for this would have 2 different types
            let m = ($m)(s)?;

            let sc = UniqueNumberManager::new_scope();
            let trans_idss = ($trans_idss)(m, sc);

            let val_idss: Vec<_> = itertools::Itertools::try_collect(
                m.val_id.to_list_checked()?.into_iter().map(|ids| {
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
            let trans_valss = ($trans_valss)(m, trans_idss, self, ctx, sc);

            rec_ctx
                .env
                .0
                .extend(trans_keyss.into_iter().zip(trans_valss.concat()));
            let letrec_values_id = ($letrecvalues)(m, self);
            let val_idss = list_to_cons(val_idss.into_iter(), |ids| {
                list_to_cons(ids.into_iter(), |x| {
                    Ast::Syntax(Box::new(x.clone().with(Ast::Symbol(x.0))))
                })
            });
            Ok(expand::rebuild(
                s.clone(),
                list!(
                    letrec_values_id,
                    Ast::map2(val_idss, m.val_rhs, |ids, rhs| {
                        Ok(list!(
                            ids,
                            if $rec {
                                self.expand(rhs.add_scope(sc.clone()), rec_ctx.clone())?
                            } else {
                                self.expand(rhs, ctx.clone())?
                            }
                        ))
                    },)?,
                    self.expand_body(m.body, sc, s, rec_ctx)?
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
            .map(|id| Self::add_local_binding(id))
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
        self.add_core_form("begin-for-syntax".into(), Self::core_form_begin_for_syntax);
        self.add_core_form("#%require".into(), Self::core_form_require);
        self.add_core_form("#%provide".into(), Self::core_form_define_provide);
        // from expand_module
        self.add_core_form("module".into(), Self::core_form_module);
        self.add_core_form("module*".into(), Self::core_form_module_star);
        self.add_core_form("#%module-begin".into(), Self::core_form_module_begin);
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
        let m = matcher::match_syntax!(
            (
                lambda
                formal
                body
                ..+
            )
        )(s.clone())?;
        let (formals, body) = self.make_lambda_expander(s.clone(), m.formal, m.body, ctx)?;
        Ok(rebuild(s, list!(m.lambda, formals, body)))
    }
    fn core_form_case_lambda(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        let m = matcher::match_syntax!((
            case_lambda
            (formals body ..+)
            ...
        ))(s.clone())?;
        let cm = matcher::match_syntax!(
            (case_lambda clause ...)
        )(s.clone())?;
        let iter = m
            .formals
            .to_list_checked()?
            .into_iter()
            .zip(m.body.to_list_checked()?)
            .zip(cm.clause.to_list_checked()?)
            .try_rfold(Ast::TheEmptyList, |rest, ((formals, bodys), clause)| {
                let (formals, body) =
                    self.make_lambda_expander(s.clone(), formals, bodys, ctx.clone())?;
                Ok::<Ast, String>(list!(rebuild(clause, list!(formals, body));rest))
            })?;
        Ok(rebuild(s, list!(m.case_lambda; iter)))
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
    make_let_values_form!(core_form_let_values, false);
    make_let_values_form!(core_form_letrec_values, true);
    make_let_values_form!(syntax core_form_letrec_syntaxes_and_values, true);

    fn core_form_datum(&mut self, s: Ast, _ctx: ExpandContext) -> Result<Ast, String> {
        // TODO: let m = matcher::match_syntax!((#%datum  datum))(s.clone())?;
        let m = matcher::match_syntax!((_datum  datum))(s.clone())?;
        let datum = m.datum;
        if matches!(datum, Ast::Syntax(ref s) if s.0.is_keyword()) {
            return Err(format!("keyword misused as an expression: {datum}"));
        }
        Ok(rebuild(
            s,
            list!(self.core_datum_to_syntax("quote".into()), datum),
        ))
    }
    fn core_form_app(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        let m = matcher::match_syntax!(
            //TODO: should app be a syntax object
            // TODO: (%app rator rand ...)
            (app rator rand ...)
        )(s.clone())?;
        let rator = self.expand(m.rator, ctx.clone())?;
        let rand = self.expand(m.rand, ctx)?;
        Ok(rebuild(
            s,
            Ast::Pair(Box::new(Pair(
                m.app,
                Ast::Pair(Box::new(Pair(rator, rand))),
            ))),
        ))
    }
    fn core_form_quote(&mut self, s: Ast, _ctx: ExpandContext) -> Result<Ast, String> {
        matcher::match_syntax!( (quote datum))(s.clone()).map(|_| s)
    }
    fn core_form_quote_syntax(&mut self, s: Ast, _ctx: ExpandContext) -> Result<Ast, String> {
        matcher::match_syntax!( (quote_syntax datum))(s.clone()).map(|_| s)
    }
    fn core_form_if(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        let m = matcher::match_syntax!(

            (
                r#if
                condition
                consequent
                alternative
            )
        )(s.clone())?;
        Ok(rebuild(
            s,
            list!(
                m.r#if,
                self.expand(m.condition, ctx.clone())?,
                self.expand(m.consequent, ctx.clone())?,
                self.expand(m.alternative, ctx)?
            ),
        ))
    }
    fn core_form_with_continuation_mark(
        &mut self,
        s: Ast,
        ctx: ExpandContext,
    ) -> Result<Ast, String> {
        let m = matcher::match_syntax!(
            (
                with_continuation_mark
                key
                val
                body
            )
        )(s.clone())?;
        Ok(rebuild(
            s,
            list!(
                m.with_continuation_mark,
                self.expand(m.key, ctx.clone())?,
                self.expand(m.val, ctx.clone())?,
                self.expand(m.body, ctx)?
            ),
        ))
    }
    fn make_begin(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        let m = matcher::match_syntax!( (begin e ..+))(s.clone())?;

        Ok(rebuild(
            s,
            list!(m.begin; m.e.map(|e|self.expand(e, ctx.clone()))?),
        ))
    }
    fn core_form_begin(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        self.make_begin(s, ctx)
    }
    fn core_form_begin0(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        self.make_begin(s, ctx)
    }
    fn core_form_set(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        // TODO: let m = matcher::match_syntax!( (set! id rhs))(s.clone(),)?;
        let m = matcher::match_syntax!( (set id rhs))(s.clone())?;
        let id = m.id;
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
        let set = m.set;
        let rhs = m.rhs;
        Ok(expand::rebuild(s, list!(set, id, rhs)))
    }
}
