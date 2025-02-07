use std::{
    collections::{BTreeSet, HashMap},
    rc::Rc,
};

use binding::CoreForm;
use expand_context::ExpandContext;
use namespace::NameSpace;

use crate::{
    ast::scope::Scope,
    ast::{syntax::Syntax, Ast, Symbol},
    evaluator::{Env, EnvRef},
    primitives::new_primitive_env,
    UniqueNumberManager,
};
use crate::{
    ast::{
        scope::AdjustScope,
        syntax::{Properties, SourceLocation},
    },
    evaluator::Values,
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
pub mod module_path;
mod namespace;
pub mod phase;
pub struct Expander {
    core_forms: HashMap<Rc<str>, CoreForm>,
    core_primitives: HashMap<Rc<str>, Ast>,
    core_scope: Scope,
    pub scope_creator: UniqueNumberManager,
    expand_time_env: EnvRef,
    run_time_env: EnvRef,
    core_syntax: Ast,
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
            run_time_env: Env::new_env(),
            expand_time_env: Env::new_env(),
            variable,
        };
        this.add_core_forms();
        new_primitive_env(|name, primitive| {
            this.add_core_primitive(name, primitive);
        });

        this
    }
    pub fn namespace(&mut self) -> NameSpace {
        let mut ns = NameSpace::default();
        self.declare_core_top_level(&mut ns);
        ns
    }
    pub fn introduce<T: AdjustScope>(&self, s: T) -> T {
        s.add_scope(self.core_scope.clone())
    }

    // TODO: mutability of ns/ctx how should/are changes to envoirnments preserved over multiple
    // expansions maybe have a namespace as part of the expander object
    // TODO: annonate fully expanded expressions so we don't have to reexpand them
    pub fn eval(&mut self, s: Ast, ns: NameSpace) -> Result<Values, String> {
        let ctx = ExpandContext::new(ns.clone());
        let expanded = self.expand(
            self.namespace_syntax_introduce(s.datum_to_syntax(None, None, None)),
            ctx,
        )?;
        let compiled = self
            .compile(expanded, &ns)
            .inspect(|e| println!("after expander: {e}"))?;
        self.run_time_eval(compiled)
    }
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
//                    "#%app".into(),
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
//                    "#%app".into(),
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

    use crate::evaluator::{Evaluator, Values};

    use crate::expander::Expander;
    use crate::Ast;
    use crate::{list, sexpr};

    use super::expand_context::ExpandContext;

    impl Expander {
        fn expand_expression(&mut self, e: Ast) -> Result<Ast, String> {
            let ctx = ExpandContext::new(self.namespace());
            self.expand(
                self.namespace_syntax_introduce(e.datum_to_syntax(None, None, None)),
                ctx,
            )
        }

        fn compile_eval_expression(&mut self, e: Ast) -> (Ast, Values) {
            let c = self
                .expand_expression(e)
                .and_then(|e| {
                    let namespace = self.namespace();
                    self.compile(e, &namespace)
                })
                .and_then(|e| {
                    Evaluator::eval(e.clone(), self.run_time_env.clone()).map(|v| (e, v))
                });
            match c {
                Ok(v) => v,
                Err(e) => panic!("{}", e),
            }
        }
        fn eval_expression(&mut self, e: Ast, check: Option<Values>) -> Values {
            let (_, v) = self.compile_eval_expression(e);
            check.inspect(|check| assert_eq!(&v, check));
            v
        }
    }

    fn add_let(e: Ast) -> Ast {
        sexpr!(
            ("letrec-syntaxes+values" ([ (let) (lambda (stx)
                       ("datum->syntax"
                        ("quote-syntax" here)
                        (cons
                         (list ("quote-syntax" lambda)
                               (map (lambda (b)
                                      (car ("syntax-e" b)))
                                    ("syntax-e" (car (cdr ("syntax-e" stx)))))
                               (car (cdr (cdr ("syntax-e" stx)))))
                         (map (lambda (b)
                                (car (cdr ("syntax-e" b))))
                              ("syntax-e" (car (cdr ("syntax-e" stx)))))))) ])
            ()
                #(e))
        )
    }

    #[test]
    fn expander_test_lambda() {
        let mut expander = Expander::new();
        expander.compile_eval_expression(sexpr!((lambda (x) x)));
    }

    #[test]
    fn expander_test_basic_let() {
        let mut expander = Expander::new();
        let expr = add_let(sexpr!((lambda (x) (let ((y x)) y))));
        expander.compile_eval_expression(expr);
    }
    #[test]
    fn expander_test_basic_macro() {
        let mut expander = Expander::new();
        let expr = sexpr!((lambda (x)
                ("letrec-syntaxes+values" ([ (y) (lambda (stx) ("quote-syntax" 7)) ]) ()
     y)));

        expander.compile_eval_expression(expr);
    }
    #[test]
    fn expander_test_complex_let() {
        let mut expander = Expander::new();
        let expr = add_let(sexpr!((let ((z 9))
        ("letrec-syntaxes+values" ([ (m) (lambda (stx) (car (cdr ("syntax-e" stx)))) ]) ()
          (let (( x 5 )
                ( y (lambda (z) z) ))
            (let (( z 10 ))
              (list z (m 10))))))
            ));
        expander.compile_eval_expression(expr);
    }

    #[test]
    fn expander_test_expansion_not_captured() {
        let mut expander = Expander::new();
        let expr = add_let(sexpr!((let ((x (quote "x-1")))
        ("letrec-syntaxes+values" ([ (m) (lambda (stx) ("quote-syntax" x)) ]) ()
          (let ((x (quote "x-3")))
            (m))))
            ));
        expander.eval_expression(expr, Some(Values::Single(Ast::Symbol("x-1".into()))));
    }

    #[test]
    fn expander_test_not_capturing_expansion() {
        let mut expander = Expander::new();
        let expr = add_let(sexpr!(
                    (let (( x (quote "x-1") ))
            ("letrec-syntaxes+values" ([ (m) (lambda (stx)
                              ("datum->syntax"
        ("quote-syntax" here)
                               (list ("quote-syntax" let)
                                     (list (list ("quote-syntax" x)
                                                 ("quote-syntax"(quote  "x-2"))))
                                     (car (cdr ("syntax-e" stx)))))) ]) ()
              (let (( x (quote "x-3") ))
                (m x))))
                ));
        expander.eval_expression(expr, Some(Values::Single(Ast::Symbol("x-3".into()))));
    }

    #[test]
    fn expander_test_distinct_generated_variables_via_introduction_scope() {
        let mut expander = Expander::new();
        let expr = add_let(sexpr!(
            ("letrec-syntaxes+values" ([ (gen2) (lambda (stx)
                        ("datum->syntax"
("quote-syntax" here)
                         (list ("quote-syntax" let)
                               (list (list (car (cdr (cdr ("syntax-e" stx))))
                                           (car (cdr (cdr (cdr (cdr ("syntax-e" stx)))))))
                                     (list (car (cdr (cdr (cdr ("syntax-e" stx)))))
                                           (car (cdr (cdr (cdr (cdr (cdr ("syntax-e" stx)))))))))
                               (list ("quote-syntax" list)
                                     (car (cdr (cdr ("syntax-e" stx))))
                                     (car (cdr (cdr (cdr ("syntax-e" stx))))))))) ]) ()
    ("letrec-syntaxes+values" ([ (gen1) (lambda ( stx)
                         ("datum->syntax"
("quote-syntax" here)
                          (cons (car (cdr ("syntax-e" stx)))
                                (cons ("quote-syntax" gen2)
                                      (cons ("quote-syntax" x)
                                            (cdr (cdr ("syntax-e" stx)))))))) ]) ()
      (gen1 gen1 1 2)))));
        expander.eval_expression(
            expr,
            Some(Values::Single(list!(Ast::Number(1.), Ast::Number(2.)))),
        );
    }
    #[test]
    fn expander_test_non_transformer_binding_misuse() {
        let mut expander = Expander::new();
        let env = ExpandContext::new(expander.namespace());
        let expr = sexpr!(
            ("letrec-syntaxes+values" ([ (v) 1 ]) ()
                            v)
        );
        assert!(expander
            .expand(
                expander.namespace_syntax_introduce(expr.datum_to_syntax(None, None, None)),
                env
            )
            .is_err_and(|e| e.contains("illegal use of syntax")));
    }
}
