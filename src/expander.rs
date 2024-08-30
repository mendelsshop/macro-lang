use std::{
    collections::{BTreeSet, HashMap},
    rc::Rc,
};

use binding::{Binding, CoreForm};

use crate::ast::{
    scope::AdjustScope,
    syntax::{Properties, SourceLocation},
};
use crate::{
    ast::scope::Scope,
    ast::{syntax::Syntax, Ast, Symbol},
    evaluator::{Env, EnvRef},
    primitives::new_primitive_env,
    UniqueNumberManager,
};

pub mod binding;
mod compile;
mod core;
mod duplicate_check;
pub mod expand;
mod expand_context;
mod expand_expr;
mod expand_top_level;
mod r#match;
mod namespace;
#[derive(Debug)]
pub struct Expander {
    core_forms: HashMap<Rc<str>, CoreForm>,
    core_primitives: HashMap<Rc<str>, Ast>,
    core_scope: Scope,
    scope_creator: UniqueNumberManager,
    pub(crate) all_bindings: HashMap<Syntax<Symbol>, Binding>,
    run_time_env: EnvRef,
    expand_env: EnvRef,
    core_syntax: Syntax<Ast>,
    pub(crate) variable: Symbol,
}

impl Default for Expander {
    fn default() -> Self {
        Self::new()
    }
}

impl Expander {
    #[must_use]
    pub fn new() -> Self {
        let mut scope_creator = UniqueNumberManager::new();
        let core_scope = scope_creator.new_scope();
        let variable = scope_creator.gen_sym("variable");
        let mut this = Self {
            core_syntax: Syntax(
                Ast::Boolean(false),
                BTreeSet::from([core_scope.clone()]),
                SourceLocation::default(),
                Properties::new(),
            ),
            scope_creator,
            core_scope,
            core_primitives: HashMap::new(),
            core_forms: HashMap::new(),
            all_bindings: HashMap::new(),
            run_time_env: Env::new_env(),
            expand_env: Env::new_env(),
            variable,
        };
        this.add_core_forms();
        new_primitive_env(|name, primitive| {
            this.add_core_primitive(name, primitive);
        });
        this
    }

    pub fn introduce<T: AdjustScope>(&self, s: T) -> T {
        s.add_scope(self.core_scope.clone())
    }

    //pub fn expand(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
    //    match s {
    //        Ast::List(l) if matches!(&l[..], [s, ..] if s.identifier()) => {
    //            self.expand_id_application_form(l, env)
    //        }
    //        Ast::Syntax(s) => self.expand_identifier(s, env),
    //        Ast::Number(_) | Ast::Function(_) | Ast::Boolean(_) => Ok(s),
    //        Ast::Symbol(_) => unreachable!(),
    //        Ast::List(l) => self.expand_app(l, env),
    //    }
    //}

    //fn expand_identifier(&self, s: Syntax, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
    //    let binding = self.resolve(&s)?;
    //    if self.core_forms.contains(binding) {
    //        Err(format!("bad syntax dangling core form {}", s.0))
    //    } else if self.core_primitives.contains(binding) {
    //        Ok(Ast::Syntax(s))
    //    } else {
    //        println!("{:?}", self.core_primitives);
    //        let Binding::Variable(binding) = binding else {
    //            panic!()
    //        };
    //        let v = env
    //            .lookup(binding)
    //            .ok_or(format!("out of context {}", s.0))?;
    //        if let CompileTimeBinding::Variable(_) = v {
    //            Ok(Ast::Syntax(s))
    //        } else {
    //            Err(format!("bad syntax non function call macro {}", s.0))
    //        }
    //    }
    //}

    // constraints = s.len() > 0
    // constraints = s[0] == Ast::Syntax(_)
    //fn expand_id_application_form(
    //    &mut self,
    //    s: Vec<Ast>,
    //    env: CompileTimeEnvoirnment,
    //) -> Result<Ast, String> {
    //    let Some(a) = s.first() else { unreachable!() };
    //    // let try_into = TryFrom::<Syntax<Ast>>::try_from(a)?;
    //    let binding = self.resolve(&(*a).clone().try_into()?)?;
    //    match binding {
    //        Binding::Lambda => self.expand_lambda(s, env),
    //        Binding::LetSyntax => self.expand_let_syntax(s, env),
    //        Binding::Quote | Binding::QuoteSyntax => match &s[..] {
    //            [_, _] => Ok(Ast::List(s)),
    //            _ => Err(format!("bad syntax to many expression in quote {s:?}")),
    //        },
    //        Binding::Variable(binding) => match env.lookup(binding) {
    //            Some(CompileTimeBinding::Procedure(m)) => {
    //                let apply_transformer = self.apply_transformer(m, Ast::List(s));
    //                self.expand(apply_transformer?, env)
    //            }
    //            _ => self.expand_app(s, env),
    //        },
    //    }
    //}

    //fn expand_app(&mut self, s: Vec<Ast>, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
    //    s.into_iter()
    //        .map(|sub_s| self.expand(sub_s, env.clone()))
    //        .collect::<Result<Vec<_>, _>>()
    //        .map(Ast::List)
    //}

    //fn expand_lambda(&mut self, s: Vec<Ast>, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
    //    let [lambda_id, Ast::List(arg), body] = &s[..] else {
    //        Err(format!("invalid syntax {s:?} bad lambda"))?
    //    };
    //    let [Ast::Syntax(arg_id)] = &arg[..] else {
    //        Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
    //    };
    //    let sc = self.scope_creator.new_scope();
    //    let id = arg_id.clone().add_scope(sc);
    //    let binding = self.add_local_binding(id.clone());
    //    let body_env = env.extend(binding.clone(), CompileTimeBinding::Variable(binding));
    //    let exp_body = self.expand(body.clone().add_scope(sc), body_env)?;
    //    Ok(Ast::List(vec![
    //        lambda_id.clone(),
    //        Ast::List(vec![Ast::Syntax(id)]),
    //        exp_body,
    //    ]))
    //}

    //fn expand_let_syntax(
    //    &mut self,
    //    s: Vec<Ast>,
    //    env: CompileTimeEnvoirnment,
    //) -> Result<Ast, String> {
    //    let [_let_syntax_id, Ast::List(arg), body] = &s[..] else {
    //        Err(format!("invalid syntax {s:?} bad let-syntax"))?
    //    };
    //    let [Ast::List(arg)] = &arg[..] else {
    //        Err(format!(
    //            "invalid syntax {s:?}, bad binder list for let-syntax {arg:?}"
    //        ))?
    //    };
    //    let [Ast::Syntax(lhs_id), rhs] = &arg[..] else {
    //        Err(format!(
    //            "invalid syntax {s:?}, bad binder for let-syntax {arg:?}"
    //        ))?
    //    };
    //    let sc = self.scope_creator.new_scope();
    //    let id = lhs_id.clone().add_scope(sc);
    //    let binding = self.add_local_binding(id);
    //    let rhs_val = self.eval_for_syntax_binding(rhs.clone())?;
    //    let body_env = env.extend(binding, rhs_val);
    //    self.expand(body.clone().add_scope(sc), body_env)
    //}

    //fn eval_for_syntax_binding(&mut self, rhs: Ast) -> Result<CompileTimeBinding, String> {
    //    // let var_name = format!("problem `evaluating` macro {rhs}");
    //    let expand = self.expand(rhs, CompileTimeEnvoirnment::new());
    //    self.eval_compiled(self.compile(expand?)?).and_then(|e| {
    //        if let Ast::Function(f) = e {
    //            Ok(CompileTimeBinding::Procedure(f))
    //        } else {
    //            Err(format!("{e} is not a macro"))
    //        }
    //    })
    //}

    //fn compile(&self, rhs: Ast) -> Result<Ast, String> {
    //    match rhs {
    //        Ast::List(l) => {
    //            let s = l
    //                .first()
    //                .ok_or("bad syntax empty application".to_string())?;
    //            let core_sym = if let Ast::Syntax(s) = s {
    //                self.resolve(s)
    //            } else {
    //                Err("just for _ case in next match does not actually error".to_string())
    //            };
    //            match core_sym {
    //                Ok(Binding::Lambda) => {
    //                    let [_, Ast::List(arg), body] = &l[..] else {
    //                        Err("bad syntax lambda")?
    //                    };
    //                    let [Ast::Syntax(id)] = &arg[..] else {
    //                        Err("bad syntax lambda arg")?
    //                    };
    //                    let Binding::Variable(id) = self.resolve(id)? else {
    //                        Err("bad syntax cannot play with core form")?
    //                    };
    //                    Ok(Ast::List(vec![
    //                        Ast::Symbol(Symbol("lambda".into(), 0)),
    //                        Ast::List(vec![Ast::Symbol(id.clone())]),
    //                        self.compile(body.clone())?,
    //                    ]))
    //                }
    //                Ok(Binding::Quote) => {
    //                    if let [_, datum] = &l[..] {
    //                        Ok(Ast::List(vec![
    //                            Ast::Symbol(Symbol("quote".into(), 0)),
    //                            datum.clone().syntax_to_datum(),
    //                        ]))
    //                    } else {
    //                        Err("bad syntax, quote requires one expression")?
    //                    }
    //                }
    //                Ok(Binding::QuoteSyntax) => {
    //                    if let [_, datum] = &l[..] {
    //                        Ok(Ast::List(vec![
    //                            Ast::Symbol(Symbol("quote".into(), 0)),
    //                            datum.clone(),
    //                        ]))
    //                    } else {
    //                        Err("bad syntax, quote-syntax requires one expression")?
    //                    }
    //                }
    //                _ => Ok(Ast::List(
    //                    l.into_iter()
    //                        .map(|e| self.compile(e))
    //                        .collect::<Result<Vec<_>, _>>()?,
    //                )),
    //            }
    //        }
    //        Ast::Syntax(s) => {
    //            if let Binding::Variable(s) = self.resolve(&s)? {
    //                Ok(Ast::Symbol(s.clone()))
    //            } else {
    //                Err("bad syntax cannot play with core form")?
    //            }
    //        }
    //        Ast::Boolean(_) | Ast::Number(_) | Ast::Function(_) => Ok(rhs),
    //
    //        Ast::Symbol(_) => unreachable!(),
    //    }
    //}

    //fn eval_compiled(&self, new: Ast) -> Result<Ast, String> {
    //    Evaluator::eval(new, self.env.clone())
    //}

    //fn apply_transformer(&mut self, m: Function, s: Ast) -> Result<Ast, String> {
    //    let intro_scope = self.scope_creator.new_scope();
    //    let intro_s = s.add_scope(intro_scope);
    //    let transformed_s = m.apply(vec![intro_s])?;
    //
    //    Ok(transformed_s.flip_scope(intro_scope))
    //}
}
//#[cfg(test)]
//mod unit_tests {
//    use std::collections::{BTreeSet, HashSet};
//
//    use crate::{
//        ast::{bound_identifier, Ast, Function, Lambda, Symbol},
//        evaluator::Env,
//        expander::CompileTimeEnvoirnment,
//        scope::{AdjustScope, Scope},
//        syntax::Syntax,
//        UniqueNumberManager,
//    };
//
//    use super::{check_unambiguous, Binding, Expander};
//
//    #[test]
//    fn bound_identifier_same() {
//        list!(Ast::Symbol("a".into()), Ast::Symbol("b".into()));
//        assert!(bound_identifier(
//            Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([Scope(0)])))),
//            Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([Scope(0)]))))
//        ));
//    }
//    #[test]
//    fn bound_identifier_different_symbol() {
//        assert!(!bound_identifier(
//            Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([Scope(0)])))),
//            Ast::Syntax(Box::new(Syntax("b".into(), BTreeSet::from([Scope(0)]))))
//        ));
//    }
//    #[test]
//    fn bound_identifier_different_scope() {
//        assert!(!bound_identifier(
//            Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([Scope(0)])))),
//            Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([Scope(1)]))))
//        ));
//    }
//
//    #[test]
//    fn datum_to_syntax_with_identifier() {
//        assert_eq!(
//            Ast::Symbol("a".into()).datum_to_syntax(None),
//            Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::new())))
//        );
//    }
//
//    #[test]
//    fn datum_to_syntax_with_number() {
//        assert_eq!(Ast::Number(1.0).datum_to_syntax(None), Ast::Number(1.0));
//    }
//
//    #[test]
//    fn datum_to_syntax_with_list() {
//        assert_eq!(
//            list![
//                Ast::Symbol(Symbol("a".into(), 0)),
//                Ast::Symbol(Symbol("b".into(), 0)),
//                Ast::Symbol(Symbol("c".into(), 0)),
//            ]
//            .datum_to_syntax(None),
//            list![
//                Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::new()))),
//                Ast::Syntax(Box::new(Syntax("b".into(), BTreeSet::new()))),
//                Ast::Syntax(Box::new(Syntax("c".into(), BTreeSet::new()))),
//            ]
//        );
//    }
//    #[test]
//    fn datum_to_syntax_with_list_and_syntax() {
//        assert_eq!(
//            list![
//                Ast::Symbol(Symbol("a".into(), 0)),
//                Ast::Syntax(Box::new(Syntax("b".into(), BTreeSet::new()))),
//                Ast::Symbol(Symbol("c".into(), 0)),
//            ]
//            .datum_to_syntax(None),
//            list![
//                Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::new()))),
//                Ast::Syntax(Box::new(Syntax("b".into(), BTreeSet::new()))),
//                Ast::Syntax(Box::new(Syntax("c".into(), BTreeSet::new()))),
//            ]
//        );
//    }
//
//    #[test]
//    fn syntax_to_datum_with_identifier() {
//        assert_eq!(
//            Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::new()))).syntax_to_datum(),
//            Ast::Symbol(Symbol("a".into(), 0)),
//        );
//    }
//
//    #[test]
//    fn syntax_to_datum_with_number() {
//        assert_eq!(Ast::Number(1.0).syntax_to_datum(), Ast::Number(1.0));
//    }
//
//    #[test]
//    fn syntax_to_datum_with_list() {
//        assert_eq!(
//            list![
//                Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::new()))),
//                Ast::Syntax(Box::new(Syntax("b".into(), BTreeSet::new()))),
//                Ast::Syntax(Box::new(Syntax("c".into(), BTreeSet::new()))),
//            ]
//            .syntax_to_datum(),
//            list![
//                Ast::Symbol(Symbol("a".into(), 0)),
//                Ast::Symbol(Symbol("b".into(), 0)),
//                Ast::Symbol(Symbol("c".into(), 0)),
//            ]
//        );
//    }
//
//    #[test]
//    fn scope_equality_test() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//        assert_ne!(sc1, sc2);
//        assert_eq!(sc2, sc2);
//    }
//    #[test]
//    fn add_scope_test_empty_scope() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        assert_eq!(
//            Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::new()))).add_scope(sc1),
//            Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::from([sc1]))))
//        );
//    }
//
//    #[test]
//    fn add_scope_test_empty_scope_list() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        assert_eq!(
//            list![
//                Ast::Symbol(Symbol("x".into(), 0)),
//                Ast::Symbol(Symbol("y".into(), 0)),
//            ]
//            .datum_to_syntax(None)
//            .add_scope(sc1),
//            list![
//                Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::from([sc1])))),
//                Ast::Syntax(Box::new(Syntax("y".into(), BTreeSet::from([sc1])))),
//            ]
//        );
//    }
//
//    #[test]
//    fn add_scope_test_non_empty_scope() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//        assert_eq!(
//            Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::from([sc1])))).add_scope(sc2),
//            Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::from([sc1, sc2]))))
//        );
//    }
//
//    #[test]
//    fn add_scope_test_add_duplicate() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        assert_eq!(
//            Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::from([sc1])))).add_scope(sc1),
//            Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::from([sc1,]))))
//        );
//    }
//
//    #[test]
//    fn flip_scope_test_different() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//        assert_eq!(
//            Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::from([sc1])))).flip_scope(sc2),
//            Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::from([sc1, sc2]))))
//        );
//    }
//
//    #[test]
//    fn flip_scope_test_same() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//        assert_eq!(
//            Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::from([sc1, sc2])))).flip_scope(sc2),
//            Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::from([sc1,]))))
//        );
//    }
//    #[test]
//    pub fn resolve_test_bound_once() {
//        let mut expander = Expander::new();
//        let loc_a = Binding::Variable(expander.scope_creator.gen_sym("a"));
//        let sc1 = expander.scope_creator.new_scope();
//        let sc2 = expander.scope_creator.new_scope();
//        expander.add_binding(Syntax("a".into(), BTreeSet::from([sc1])), loc_a.clone());
//
//        assert_eq!(
//            expander.resolve(&Syntax("a".into(), BTreeSet::from([sc1]))),
//            Ok(&loc_a)
//        );
//        assert_eq!(
//            expander.resolve(&Syntax("a".into(), BTreeSet::from([sc1, sc2]))),
//            Ok(&loc_a)
//        );
//    }
//    #[test]
//    pub fn resolve_test_shadow() {
//        let mut expander = Expander::new();
//        let loc_b_out = Binding::Variable(expander.scope_creator.gen_sym("b"));
//        let loc_b_in = Binding::Variable(expander.scope_creator.gen_sym("b"));
//        let sc1 = expander.scope_creator.new_scope();
//        let sc2 = expander.scope_creator.new_scope();
//
//        expander.add_binding(Syntax("b".into(), BTreeSet::from([sc1])), loc_b_out.clone());
//        expander.add_binding(
//            Syntax("b".into(), BTreeSet::from([sc1, sc2])),
//            loc_b_in.clone(),
//        );
//
//        assert_eq!(
//            expander.resolve(&Syntax("b".into(), BTreeSet::from([sc1]))),
//            Ok(&loc_b_out)
//        );
//        assert_eq!(
//            expander.resolve(&Syntax("b".into(), BTreeSet::from([sc1, sc2]))),
//            Ok(&loc_b_in)
//        );
//        assert!(expander
//            .resolve(&Syntax("b".into(), BTreeSet::from([sc2])))
//            .is_err_and(|e| e.contains("free variable")));
//    }
//    #[test]
//    pub fn resolve_test_ambiguous() {
//        let mut expander = Expander::new();
//        let loc_c1 = Binding::Variable(expander.scope_creator.gen_sym("c"));
//        let loc_c2 = Binding::Variable(expander.scope_creator.gen_sym("c"));
//        let sc1 = expander.scope_creator.new_scope();
//        let sc2 = expander.scope_creator.new_scope();
//        expander.add_binding(Syntax("c".into(), BTreeSet::from([sc1])), loc_c1.clone());
//        expander.add_binding(Syntax("c".into(), BTreeSet::from([sc2])), loc_c2.clone());
//
//        assert_eq!(
//            expander.resolve(&Syntax("c".into(), BTreeSet::from([sc1]))),
//            Ok(&loc_c1)
//        );
//        assert!(expander
//            .resolve(&Syntax("c".into(), BTreeSet::from([sc1, sc2])))
//            .is_err_and(|e| e.contains("ambiguous")));
//        assert_eq!(
//            expander.resolve(&Syntax("c".into(), BTreeSet::from([sc2]))),
//            Ok(&loc_c2)
//        );
//    }
//    #[test]
//    fn find_all_bindings_test_bound_once() {
//        let mut expander = Expander::new();
//        let loc_a = Binding::Variable(expander.scope_creator.gen_sym("a"));
//        let sc1 = expander.scope_creator.new_scope();
//        let sc2 = expander.scope_creator.new_scope();
//        expander.add_binding(Syntax("a".into(), BTreeSet::from([sc1])), loc_a);
//        assert_eq!(
//            expander
//                .find_all_matching_bindings(&Syntax("a".into(), BTreeSet::from([sc1])))
//                .collect::<Vec<_>>(),
//            vec![&Syntax("a".into(), BTreeSet::from([sc1]))]
//        );
//        assert_eq!(
//            expander
//                .find_all_matching_bindings(&Syntax("a".into(), BTreeSet::from([sc2])))
//                .count(),
//            0
//        );
//    }
//    #[test]
//    pub fn find_all_bindings_test_shadow() {
//        let mut expander = Expander::new();
//        let loc_b_out = Binding::Variable(expander.scope_creator.gen_sym("b"));
//        let loc_b_in = Binding::Variable(expander.scope_creator.gen_sym("b"));
//        let sc1 = expander.scope_creator.new_scope();
//        let sc2 = expander.scope_creator.new_scope();
//
//        expander.add_binding(Syntax("b".into(), BTreeSet::from([sc1])), loc_b_out);
//        expander.add_binding(Syntax("b".into(), BTreeSet::from([sc1, sc2])), loc_b_in);
//        assert_eq!(
//            expander
//                .find_all_matching_bindings(&Syntax("b".into(), BTreeSet::from([sc1, sc2])))
//                .collect::<HashSet<_>>(),
//            HashSet::from([
//                &Syntax("b".into(), BTreeSet::from([sc1])),
//                &Syntax("b".into(), BTreeSet::from([sc1, sc2]))
//            ])
//        );
//    }
//    #[test]
//    pub fn find_all_bindings_test_ambiguous() {
//        let mut expander = Expander::new();
//        let loc_c1 = Binding::Variable(expander.scope_creator.gen_sym("c"));
//        let loc_c2 = Binding::Variable(expander.scope_creator.gen_sym("c"));
//        let sc1 = expander.scope_creator.new_scope();
//        let sc2 = expander.scope_creator.new_scope();
//        expander.add_binding(Syntax("c".into(), BTreeSet::from([sc1])), loc_c1);
//        expander.add_binding(Syntax("c".into(), BTreeSet::from([sc2])), loc_c2);
//        assert_eq!(
//            expander
//                .find_all_matching_bindings(&Syntax("c".into(), BTreeSet::from([sc1, sc2])))
//                .collect::<HashSet<_>>(),
//            HashSet::from([
//                &Syntax("c".into(), BTreeSet::from([sc1])),
//                &Syntax("c".into(), BTreeSet::from([sc2]))
//            ])
//        );
//    }
//
//    #[test]
//    pub fn check_ambiguous_test_non_ambiguous() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//
//        assert!(check_unambiguous(
//            &Syntax("b".into(), BTreeSet::from([sc1, sc2])),
//            [
//                &Syntax("b".into(), BTreeSet::from([sc1])),
//                &Syntax("b".into(), BTreeSet::from([sc1, sc2]))
//            ]
//            .into_iter()
//        ));
//    }
//    #[test]
//    pub fn check_ambiguous_test_ambiguous() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//
//        assert!(!check_unambiguous(
//            &Syntax("c".into(), BTreeSet::from([sc2])),
//            [
//                &Syntax("c".into(), BTreeSet::from([sc1])),
//                &Syntax("c".into(), BTreeSet::from([sc2]))
//            ]
//            .into_iter()
//        ));
//    }
//    #[test]
//    fn free_identifier_test_bound_once() {
//        let mut expander = Expander::new();
//        let loc_a = Binding::Variable(expander.scope_creator.gen_sym("a"));
//        let sc1 = expander.scope_creator.new_scope();
//        let sc2 = expander.scope_creator.new_scope();
//        expander.add_binding(Syntax("a".into(), BTreeSet::from([sc1])), loc_a);
//        assert!(expander.free_identifier(
//            Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([sc1])))),
//            Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([sc1, sc2]))))
//        ));
//    }
//    #[test]
//    pub fn free_identifier_test_shadow() {
//        let mut expander = Expander::new();
//        let loc_b_out = Binding::Variable(expander.scope_creator.gen_sym("b"));
//        let loc_b_in = Binding::Variable(expander.scope_creator.gen_sym("b"));
//        let sc1 = expander.scope_creator.new_scope();
//        let sc2 = expander.scope_creator.new_scope();
//        expander.add_binding(Syntax("b".into(), BTreeSet::from([sc1])), loc_b_out);
//        expander.add_binding(Syntax("b".into(), BTreeSet::from([sc1, sc2])), loc_b_in);
//        assert!(!expander.free_identifier(
//            Ast::Syntax(Box::new(Syntax("b".into(), BTreeSet::from([sc1])))),
//            Ast::Syntax(Box::new(Syntax("b".into(), BTreeSet::from([sc1, sc2]))))
//        ));
//    }
//
//    #[test]
//    fn resolve_test_lambda_empty() {
//        let expander = Expander::new();
//
//        assert!(expander
//            .resolve(&Syntax("lambda".into(), BTreeSet::new()))
//            .is_err_and(|error| error.contains("free variable")),);
//    }
//
//    #[test]
//    fn resolve_test_lambda_core() {
//        let expander = Expander::new();
//
//        assert_eq!(
//            expander.resolve(
//                &expander.namespace_syntax_introduce(Syntax("lambda".into(), BTreeSet::new()))
//            ),
//            Ok(&Binding::Lambda)
//        );
//    }
//
//    #[test]
//    fn env_lookup_test_empty() {
//        let mut expander = Expander::new();
//        let loc_a = expander.scope_creator.gen_sym("a");
//        let sc1 = expander.scope_creator.new_scope();
//        expander.add_binding(
//            Syntax("a".into(), BTreeSet::from([sc1])),
//            Binding::Variable(loc_a.clone()),
//        );
//        let env = CompileTimeEnvoirnment::new();
//        assert!(env.lookup(&loc_a).is_none());
//    }
//    #[test]
//    fn env_lookup_test_present() {
//        let mut expander = Expander::new();
//        let loc_a = expander.scope_creator.gen_sym("a");
//        let sc1 = expander.scope_creator.new_scope();
//        expander.add_binding(
//            Syntax("a".into(), BTreeSet::from([sc1])),
//            Binding::Variable(loc_a.clone()),
//        );
//        let env = CompileTimeEnvoirnment::new();
//        let env = env.extend(loc_a.clone(), Ast::Symbol(expander.variable));
//        assert!(env.lookup(&loc_a).is_some());
//    }
//
//    #[test]
//    fn add_local_binding_test() {
//        let mut expander = Expander::new();
//        let sc1 = expander.scope_creator.new_scope();
//        let sc2 = expander.scope_creator.new_scope();
//        let loc_d = expander.add_local_binding(Syntax("d".into(), BTreeSet::from([sc1, sc2])));
//        assert_eq!(
//            expander.resolve(&Syntax("d".into(), BTreeSet::from([sc1, sc2]))),
//            Ok(&Binding::Variable(loc_d))
//        );
//    }
//
//    #[test]
//    fn expand_test_number() {
//        let mut expander = Expander::new();
//        assert_eq!(
//            expander.expand(
//                Ast::Number(1.0).datum_to_syntax(None),
//                CompileTimeEnvoirnment::new()
//            ),
//            Ok(list!(
//                Ast::Syntax(Box::new(Syntax(
//                    "quote".into(),
//                    BTreeSet::from([expander.core_scope])
//                ))),
//                Ast::Number(1.0)
//            ))
//        );
//    }
//
//    #[test]
//    fn expand_test_lambda() {
//        let mut expander = Expander::new();
//        assert_eq!(
//            expander
//                .expand(
//                    list!(
//                        Ast::Symbol("lambda".into()),
//                        list!(Ast::Symbol("x".into())),
//                        Ast::Symbol("x".into())
//                    )
//                    .datum_to_syntax(None)
//                    .add_scope(expander.core_scope),
//                    CompileTimeEnvoirnment::new()
//                )
//                .map(Ast::syntax_to_datum),
//            Ok(list!(
//                Ast::Symbol("lambda".into()),
//                list!(Ast::Symbol("x".into())),
//                Ast::Symbol("x".into())
//            ))
//        );
//    }
//
//    #[test]
//    fn expand_test_primitive() {
//        let mut expander = Expander::new();
//        assert_eq!(
//            expander.expand(
//                Ast::Syntax(Box::new(Syntax(
//                    "cons".into(),
//                    BTreeSet::from([expander.core_scope])
//                ))),
//                CompileTimeEnvoirnment::new()
//            ),
//            Ok(Ast::Syntax(Box::new(Syntax(
//                "cons".into(),
//                BTreeSet::from([expander.core_scope])
//            ))))
//        );
//    }
//
//    #[test]
//    fn expand_test_basic_variable() {
//        let mut expander = Expander::new();
//        let loc_a = expander.scope_creator.gen_sym("a");
//        let sc1 = expander.scope_creator.new_scope();
//        expander.add_binding(
//            Syntax("a".into(), BTreeSet::from([sc1])),
//            Binding::Variable(loc_a.clone()),
//        );
//
//        assert_eq!(
//            expander.expand(
//                Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([sc1])))),
//                CompileTimeEnvoirnment::new().extend(loc_a, Ast::Symbol(expander.variable.clone()))
//            ),
//            Ok(Ast::Syntax(Box::new(Syntax(
//                "a".into(),
//                BTreeSet::from([sc1])
//            ))))
//        );
//    }
//
//    #[test]
//    fn expand_test_free_variable() {
//        let mut expander = Expander::new();
//        let sc1 = expander.scope_creator.new_scope();
//        assert!(expander
//            .expand(
//                Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([sc1])))),
//                CompileTimeEnvoirnment::new()
//            )
//            .is_err_and(|e| e.contains("free variable")));
//    }
//
//    #[test]
//    fn expand_test_basic_app() {
//        let mut expander = Expander::new();
//        let loc_a = expander.scope_creator.gen_sym("a");
//        let sc1 = expander.scope_creator.new_scope();
//        expander.add_binding(
//            Syntax("a".into(), BTreeSet::from([sc1])),
//            Binding::Variable(loc_a.clone()),
//        );
//        assert_eq!(
//            expander.expand(
//                list!(
//                    Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([sc1])))),
//                    Ast::Number(1.0)
//                ),
//                CompileTimeEnvoirnment::new().extend(loc_a, Ast::Symbol(expander.variable.clone()))
//            ),
//            Ok(list!(
//                Ast::Syntax(Box::new(Syntax(
//                    "%app".into(),
//                    BTreeSet::from([expander.core_scope])
//                ))),
//                Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([sc1])))),
//                list!(
//                    Ast::Syntax(Box::new(Syntax(
//                        "quote".into(),
//                        BTreeSet::from([expander.core_scope])
//                    ))),
//                    Ast::Number(1.)
//                )
//            ))
//        );
//    }
//    #[test]
//    fn expand_test_weird_but_works_app() {
//        let mut expander = Expander::new();
//        assert_eq!(
//            expander.expand(
//                list!(Ast::Number(0.), Ast::Number(1.)).datum_to_syntax(None),
//                CompileTimeEnvoirnment::new()
//            ),
//            Ok(list!(
//                Ast::Syntax(Box::new(Syntax(
//                    "%app".into(),
//                    BTreeSet::from([expander.core_scope])
//                ))),
//                list!(
//                    Ast::Syntax(Box::new(Syntax(
//                        "quote".into(),
//                        BTreeSet::from([expander.core_scope])
//                    ))),
//                    Ast::Number(0.)
//                ),
//                list!(
//                    Ast::Syntax(Box::new(Syntax(
//                        "quote".into(),
//                        BTreeSet::from([expander.core_scope])
//                    ))),
//                    Ast::Number(1.)
//                )
//            ))
//        );
//    }
//
//    #[test]
//    fn expand_test_macro_basic() {
//        let mut expander = Expander::new();
//        let loc_a = expander.scope_creator.gen_sym("a");
//        let sc1 = expander.scope_creator.new_scope();
//        expander.add_binding(
//            Syntax("a".into(), BTreeSet::from([sc1])),
//            Binding::Variable(loc_a.clone()),
//        );
//        assert_eq!(
//            expander
//                .expand(
//                    Ast::Syntax(Box::new(Syntax("a".into(), BTreeSet::from([sc1])))),
//                    CompileTimeEnvoirnment::new().extend(
//                        loc_a,
//                        Ast::Function(Function::Lambda(Lambda(
//                            Box::new(list!(Ast::Number(1.).datum_to_syntax(None))),
//                            Env::new(),
//                            Box::new(list!(Ast::Symbol("s".into())))
//                        )))
//                    )
//                )
//                .map(Ast::syntax_to_datum),
//            Ok(Ast::Number(1.))
//        );
//    }
//    #[test]
//    fn expand_test_macro_identity() {
//        let mut expander = Expander::new();
//        let loc_a = expander.scope_creator.gen_sym("a");
//        let sc1 = expander.scope_creator.new_scope();
//        expander.add_binding(
//            Syntax("a".into(), BTreeSet::from([sc1])),
//            Binding::Variable(loc_a.clone()),
//        );
//        assert_eq!(
//            expander
//                .expand(
//                    list!(
//                        Ast::Symbol("a".into()),
//                        list!(
//                            Ast::Symbol("lambda".into()),
//                            list!(Ast::Symbol("x".into())),
//                            Ast::Symbol("x".into())
//                        )
//                    )
//                    .datum_to_syntax(None)
//                    .add_scope(sc1)
//                    .add_scope(expander.core_scope),
//                    CompileTimeEnvoirnment::new().extend(
//                        loc_a,
//                        Ast::Function(Function::Lambda(Lambda(
//                            Box::new(list!(list!(
//                                Ast::Symbol("car".into()),
//                                list!(Ast::Symbol("cdr".into()), Ast::Symbol("s".into()))
//                            ))),
//                            Env::new_env(),
//                            Box::new(list!(Ast::Symbol("s".into())))
//                        )))
//                    )
//                )
//                .map(Ast::syntax_to_datum),
//            Ok(list!(
//                Ast::Symbol("lambda".into()),
//                list!(Ast::Symbol("x".into())),
//                Ast::Symbol("x".into())
//            ))
//        );
//    }
//
//    #[test]
//    fn apply_transformer_test() {
//        let mut expander = Expander::new();
//        let sc1 = expander.scope_creator.new_scope();
//        let transformed_s = expander
//            .apply_transformer(
//                Function::Lambda(Lambda(
//                    Box::new(list!(list!(
//                        Ast::Symbol("list".into()),
//                        list!(
//                            Ast::Symbol("car".into()),
//                            list!(Ast::Symbol("cdr".into()), Ast::Symbol("s".into()))
//                        ),
//                        Ast::Syntax(Box::new(Syntax("x".into(), BTreeSet::new())))
//                    ))),
//                    Env::new_env(),
//                    Box::new(list!(Ast::Symbol("s".into()))),
//                )),
//                list!(
//                    Ast::Syntax(Box::new(Syntax("m".into(), BTreeSet::new()))),
//                    Ast::Syntax(Box::new(Syntax("f".into(), BTreeSet::from([sc1]))))
//                ),
//            )
//            .unwrap();
//        assert_eq!(
//            transformed_s.syntax_to_datum(),
//            list!(Ast::Symbol("f".into()), Ast::Symbol("x".into())),
//        );
//    }
//    #[test]
//    fn eval_for_syntax_test_number() {
//        let mut expander = Expander::new();
//        assert_eq!(
//            expander.eval_for_syntax_binding(
//                list!(
//                    Ast::Symbol("car".into()),
//                    list!(Ast::Symbol("list".into()), Ast::Number(1.), Ast::Number(2.))
//                )
//                .datum_to_syntax(None)
//                .add_scope(expander.core_scope)
//            ),
//            Ok(Ast::Number(1.))
//        );
//    }
//    #[test]
//    fn eval_for_syntax_test_symbol() {
//        let mut expander = Expander::new();
//        assert_eq!(
//            expander
//                .eval_for_syntax_binding(
//                    list!(
//                        Ast::Symbol("lambda".into()),
//                        list!(Ast::Symbol("x".into())),
//                        list!(Ast::Symbol("syntax-e".into()), Ast::Symbol("x".into())),
//                    )
//                    .datum_to_syntax(None)
//                    .add_scope(expander.core_scope)
//                )
//                .and_then(|f| {
//                    let Ast::Function(f) = f else {
//                        Err("not a function")?
//                    };
//                    f.apply(list!(Ast::Syntax(Box::new(Syntax(
//                        "x".into(),
//                        BTreeSet::new()
//                    )))))
//                }),
//            Ok(Ast::Symbol("x".into()))
//        );
//    }
//}
//
#[cfg(test)]
mod tests {

    use crate::evaluator::Evaluator;
    use crate::expander::binding::CompileTimeEnvoirnment;
    use crate::expander::Expander;
    use crate::list;
    use crate::reader::Reader;
    use crate::Ast;

    impl Expander {
        fn expand_expression(&mut self, e: Ast) -> Result<Ast, String> {
            self.expand(
                self.namespace_syntax_introduce(e.datum_to_syntax(None, None, None)),
                CompileTimeEnvoirnment::new(),
            )
        }

        fn compile_eval_expression(&mut self, e: Ast) -> (Ast, Ast) {
            let c = self
                .expand_expression(e)
                .and_then(|e| self.compile(e))
                .and_then(|e| {
                    Evaluator::eval(e.clone(), self.run_time_env.clone()).map(|v| (e, v))
                });
            match c {
                Ok(v) => v,
                Err(e) => panic!("{}", e),
            }
        }
        fn eval_expression(&mut self, e: Ast, check: Option<Ast>) -> Ast {
            let (_, v) = self.compile_eval_expression(e);
            check.inspect(|check| assert_eq!(&v, check));
            v
        }
    }

    fn add_let(e: &str) -> String {
        format!(
            "(let-syntax (( let (lambda (stx)
                       (datum->syntax
                        (quote-syntax here)
                        (cons
                         (list (quote-syntax lambda)
                               (map (lambda (b)
                                      (car (syntax-e b)))
                                    (syntax-e (car (cdr (syntax-e stx)))))
                               (car (cdr (cdr (syntax-e stx)))))
                         (map (lambda (b)
                                (car (cdr (syntax-e b))))
                              (syntax-e (car (cdr (syntax-e stx)))))))) ))
                {e})"
        )
    }

    #[test]
    fn expander_test_lambda() {
        let mut expander = Expander::new();
        expander.compile_eval_expression(list!(
            Ast::Symbol("lambda".into()),
            list!(Ast::Symbol("x".into())),
            Ast::Symbol("x".into())
        ));
    }

    #[test]
    fn expander_test_basic_let() {
        let mut expander = Expander::new();
        let mut reader = Reader::new_with_input(&add_let("(lambda (x) (let ((y x)) y))"));
        expander.compile_eval_expression(reader.read().unwrap());
    }
    #[test]
    fn expander_test_basic_macro() {
        let mut expander = Expander::new();
        let mut reader = Reader::new_with_input(
            &"(lambda (x)
                (let-syntax ((y (lambda (stx) (quote-syntax 7))))
     y))",
        );
        expander.compile_eval_expression(reader.read().unwrap());
    }
    #[test]
    fn expander_test_complex_let() {
        let mut expander = Expander::new();
        let mut reader = Reader::new_with_input(&add_let(
            "(let ((z 9))
    (let-syntax (( m (lambda (stx) (car (cdr (syntax-e stx)))) ))
      (let (( x 5 )
            ( y (lambda (z) z) ))
        (let (( z 10 ))
          (list z (m 10))))))",
        ));
        expander.compile_eval_expression(reader.read().unwrap());
    }

    #[test]
    fn expander_test_expansion_not_captured() {
        let mut expander = Expander::new();
        let mut reader = Reader::new_with_input(&add_let(
            "(let ((x 'x-1))
    (let-syntax ((m (lambda (stx) (quote-syntax x))))
      (let ((x 'x-3))
        (m))))",
        ));
        expander.eval_expression(reader.read().unwrap(), Some(Ast::Symbol("x-1".into())));
    }

    #[test]
    fn expander_test_not_capturing_expansion() {
        let mut expander = Expander::new();
        let mut reader = Reader::new_with_input(&add_let(
            "(let (( x 'x-1 ))
    (let-syntax (( m (lambda (stx)
                      (datum->syntax
(quote-syntax here)
                       (list (quote-syntax let)
                             (list (list (quote-syntax x)
                                         (quote-syntax 'x-2)))
                             (car (cdr (syntax-e stx)))))) ))
      (let (( x 'x-3 ))
        (m x))))",
        ));
        expander.eval_expression(reader.read().unwrap(), Some(Ast::Symbol("x-3".into())));
    }

    #[test]
    fn expander_test_distinct_generated_variables_via_introduction_scope() {
        let mut expander = Expander::new();
        let mut reader = Reader::new_with_input(&add_let(
            "(let-syntax (( gen2 (lambda (stx)
                        (datum->syntax
(quote-syntax here)
                         (list (quote-syntax let)
                               (list (list (car (cdr (cdr (syntax-e stx))))
                                           (car (cdr (cdr (cdr (cdr (syntax-e stx)))))))
                                     (list (car (cdr (cdr (cdr (syntax-e stx)))))
                                           (car (cdr (cdr (cdr (cdr (cdr (syntax-e stx)))))))))
                               (list (quote-syntax list)
                                     (car (cdr (cdr (syntax-e stx))))
                                     (car (cdr (cdr (cdr (syntax-e stx))))))))) ))
    (let-syntax (( gen1 (lambda ( stx)
                         (datum->syntax
(quote-syntax here)
                          (cons (car (cdr (syntax-e stx)))
                                (cons (quote-syntax gen2)
                                      (cons (quote-syntax x)
                                            (cdr (cdr (syntax-e stx)))))))) ))
      (gen1 gen1 1 2)))",
        ));
        expander.eval_expression(
            reader.read().unwrap(),
            Some(list!(Ast::Number(1.), Ast::Number(2.))),
        );
    }
    #[test]
    fn expander_test_non_transformer_binding_misuse() {
        let mut expander = Expander::new();
        let mut reader = Reader::new_with_input(
            &"(let-syntax ((v 1))
                            v)",
        );
        assert!(expander
            .expand(
                expander.namespace_syntax_introduce(
                    reader.read().unwrap().datum_to_syntax(None, None, None)
                ),
                CompileTimeEnvoirnment::new()
            )
            .is_err_and(|e| e.contains("illegal use of syntax")));
    }
}
