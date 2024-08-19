use crate::{scope::AdjustScope, Expander};

//use crate::{
//    ast::{Ast, Function, Pair, Symbol},
//    evaluator::{self, Env},
//    scope::{AdjustScope, Scope},
//    syntax::Syntax,
//    DEPTH,
//};
//
//use super::UniqueNumberManager;
//
//use std::{
//    collections::{BTreeSet, HashMap},
//    fmt,
//};
//
//#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
//pub enum Binding {
//    Lambda,
//    LetSyntax,
//    Quote,
//    QuoteSyntax,
//    App,
//    Variable(Symbol),
//}
//
//impl fmt::Display for Binding {
//    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//        write!(
//            f,
//            "{}",
//            match self {
//                Self::Variable(s) => format!("{s}"),
//                Self::Lambda => "lambda".to_string(),
//                Self::LetSyntax => "let-syntax".to_string(),
//                Self::Quote => "quote".to_string(),
//                Self::QuoteSyntax => "quote-syntax".to_string(),
//                Self::App => "%app".to_string(),
//            }
//        )
//    }
//}
//
//impl From<Binding> for Symbol {
//    fn from(value: Binding) -> Self {
//        match value {
//            Binding::Variable(s) => s,
//            Binding::Lambda => "lambda".into(),
//            Binding::LetSyntax => "let-syntax".into(),
//            Binding::Quote => "quote".into(),
//            Binding::QuoteSyntax => "quote-syntax".into(),
//            Binding::App => "%app".into(),
//        }
//    }
//}
//
//#[derive(Debug)]
//pub struct Expander<T> {
//    pub(crate) all_bindings: HashMap<Syntax<Symbol>, T>,
//    pub(crate) core_forms: BTreeSet<Binding>,
//    pub(crate) core_primitives: BTreeSet<Binding>,
//    pub(crate) core_scope: Scope,
//    pub(crate) variable: Symbol,
//    pub(crate) scope_creator: UniqueNumberManager,
//    pub(crate) env: evaluator::EnvRef,
//}
//
//impl Default for Expander<Binding> {
//    fn default() -> Self {
//        Self::new()
//    }
//}
//
impl Expander {
    //    #[must_use]
    //    pub fn new() -> Self {
    //        let mut scope_creator = UniqueNumberManager::new();
    //        let core_scope = scope_creator.new_scope();
    //        let core_forms = BTreeSet::from([
    //            Binding::Lambda,
    //            Binding::LetSyntax,
    //            Binding::Quote,
    //            Binding::QuoteSyntax,
    //            Binding::App,
    //        ]);
    //        let core_primitives = BTreeSet::from([
    //            Binding::Variable("datum->syntax".into()),
    //            Binding::Variable("syntax->datum".into()),
    //            Binding::Variable("syntax-e".into()),
    //            Binding::Variable("list".into()),
    //            Binding::Variable("cons".into()),
    //            Binding::Variable("car".into()),
    //            Binding::Variable("cdr".into()),
    //            Binding::Variable("map".into()),
    //        ]);
    //        let variable = scope_creator.gen_sym("variable");
    //        let mut this = Self {
    //            scope_creator,
    //            core_scope,
    //            core_primitives,
    //            core_forms,
    //            all_bindings: HashMap::new(),
    //            variable,
    //            env: Env::new_env(),
    //        };
    //        this.core_forms
    //            .clone()
    //            .union(&this.core_primitives.clone())
    //            .for_each(|core| {
    //                this.add_binding(
    //                    Syntax(core.clone().into(), BTreeSet::from([this.core_scope])),
    //                    core.clone(),
    //                );
    //            });
    //        this
    //    }
    //    pub(crate) fn add_binding(&mut self, id: Syntax, binding: Binding) {
    //        self.all_bindings.insert(id, binding);
    //    }
    //
    //    pub(crate) fn resolve(&self, id: &Syntax) -> Result<&Binding, String> {
    //        let candidate_ids = self.find_all_matching_bindings(id);
    //        let id = candidate_ids
    //            .clone()
    //            .max_by_key(|id| id.1.len())
    //            .ok_or(format!("free variable {}", id.0))?;
    //        if check_unambiguous(id, candidate_ids) {
    //            self.all_bindings
    //                .get(id)
    //                .ok_or(format!("free variable {}", id.0))
    //        } else {
    //            Err(format!("ambiguous binding {}", id.0 .0))
    //        }
    //    }
    //
    //    pub(crate) fn free_identifier(&self, a: Ast, b: Ast) -> bool {
    //        matches!((a, b), (Ast::Syntax(a), Ast::Syntax(b)) if self.resolve( &a).is_ok_and(|a| self.resolve(&b).is_ok_and(|b| a == b )))
    //    }
    //
    //    pub(crate) fn find_all_matching_bindings<'a>(
    //        &'a self,
    //        id: &'a Syntax,
    //    ) -> impl Iterator<Item = &Syntax> + Clone + 'a {
    //        self.all_bindings
    //            .keys()
    //            .filter(move |c_id| c_id.0 == id.0 && c_id.1.is_subset(&id.1))
    //    }
    //
    pub fn namespace_syntax_introduce<T: AdjustScope>(&self, s: T) -> T {
        s.add_scope(self.core_scope)
    }
    //
    //    #[trace::trace()]
    //    pub fn expand(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
    //        match s {
    //            Ast::Syntax(s) => self.expand_identifier(s, env),
    //            Ast::Pair(l) if matches!(&l.0, Ast::Syntax(_)) => {
    //                self.expand_id_application_form(*l, env)
    //            }
    //            Ast::Pair(l) => self.expand_app(*l, env),
    //            _ => Ok(Ast::Pair(Box::new(Pair(
    //                Ast::Syntax(Box::new(Syntax(
    //                    "quote".into(),
    //                    BTreeSet::from([self.core_scope]),
    //                ))),
    //                Ast::Pair(Box::new(Pair(s, Ast::TheEmptyList))),
    //            )))),
    //        }
    //    }
    //
    //    pub(crate) fn expand_identifier(
    //        &mut self,
    //        s: Syntax,
    //        env: CompileTimeEnvoirnment,
    //    ) -> Result<Ast, String> {
    //        let binding = self.resolve(&s)?;
    //        if self.core_forms.contains(binding) {
    //            Err(format!("bad syntax dangling core form {}", s.0))
    //        } else if self.core_primitives.contains(binding) {
    //            Ok(Ast::Syntax(s))
    //        } else {
    //            let Binding::Variable(binding) = binding else {
    //                panic!()
    //            };
    //            let v = env
    //                .lookup(&binding)
    //                .ok_or(format!("out of context {s:?}"))?;
    //            match v {
    //                Ast::Symbol(sym) if sym == self.variable => Ok(Ast::Syntax(s)),
    //                Ast::Function(m) => self.apply_transformer(m, Ast::Syntax(s)),
    //                _ => Err(format!("illegal use of syntax: {s:?}")),
    //            }
    //        }
    //    }
    //
    //    // constraints = s.len() > 0
    //    // constraints = s[0] == Ast::Syntax(_)
    //    pub(crate) fn expand_id_application_form(
    //        &mut self,
    //        s: Pair,
    //        env: CompileTimeEnvoirnment,
    //    ) -> Result<Ast, String> {
    //        let Ast::Syntax(ref id) = s.0 else {
    //            unreachable!()
    //        };
    //        let binding = self.resolve(id)?;
    //        match binding {
    //            Binding::Lambda => self.expand_lambda(s, env),
    //            Binding::LetSyntax => self.expand_let_syntax(s, env),
    //            Binding::Quote | Binding::QuoteSyntax => Ok(Ast::Pair(Box::new(s))),
    //            Binding::App => {
    //                if !s.list() {
    //                    Err("%app form's arguements must be a list".to_string())?;
    //                }
    //                // TODO: empty list
    //                let Ast::Pair(p) = s.1 else { unreachable!() };
    //                self.expand_app(*p, env)
    //            }
    //            Binding::Variable(binding) => match env.lookup(&binding) {
    //                Some(Ast::Function(m)) => {
    //                    //println!("{binding} in {env:?}");
    //                    let apply_transformer = self.apply_transformer(m, Ast::Pair(Box::new(s)))?;
    //                    //println!("app {apply_transformer}");
    //                    self.expand(apply_transformer, env)
    //                }
    //                _ => self.expand_app(s, env),
    //            },
    //        }
    //    }
    //    pub(crate) fn apply_transformer(&mut self, m: Function, s: Ast) -> Result<Ast, String> {
    //        let intro_scope = self.scope_creator.new_scope();
    //        //println!("apply_transformer {s:?}");
    //        let intro_s = s.add_scope(intro_scope);
    //        let transformed_s = m.apply(Ast::Pair(Box::new(Pair(intro_s, Ast::TheEmptyList))))?;
    //
    //        Ok(transformed_s.flip_scope(intro_scope))
    //    }
    //    pub(crate) fn expand_app(
    //        &mut self,
    //        s: Pair,
    //        env: CompileTimeEnvoirnment,
    //    ) -> Result<Ast, String> {
    //        let Pair(rator, rands) = s;
    //
    //        Ok(Ast::Pair(Box::new(Pair(
    //            Ast::Syntax(Box::new(Syntax(
    //                "%app".into(),
    //                BTreeSet::from([self.core_scope]),
    //            ))),
    //            Ast::Pair(Box::new(Pair(
    //                self.expand(rator, env.clone())?,
    //                rands.map(|rand| self.expand(rand, env.clone()))?,
    //            ))),
    //        ))))
    //    }
    //
    //    pub(crate) fn expand_lambda(
    //        &mut self,
    //        s: Pair,
    //        env: CompileTimeEnvoirnment,
    //    ) -> Result<Ast, String> {
    //        //println!("lambda body {s:?}");
    //        let Pair(ref lambda_id, Ast::Pair(ref inner)) = s else {
    //            Err(format!("invalid syntax {s:?} bad lambda"))?
    //        };
    //        let Pair(ref args, Ast::Pair(ref body)) = **inner else {
    //            Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
    //        };
    //        let sc = self.scope_creator.new_scope();
    //        let args = args.clone().map_pair(|term, base| match term {
    //            Ast::Syntax(id) => {
    //                let id = id.add_scope(sc);
    //                Ok(Ast::Syntax(Box::new(id)))
    //            }
    //            Ast::TheEmptyList if base => Ok(Ast::TheEmptyList),
    //            _ => Err(format!(
    //                "{term} is not a symbol so it cannot be a parameter"
    //            )),
    //        })?;
    //        let body_env = args.clone().foldl_pair(
    //            |term, base, env: Result<CompileTimeEnvoirnment, String>| match term {
    //                Ast::Syntax(id) => {
    //                    let binding = self.add_local_binding(id);
    //                    env.map(|env| env.extend(binding.clone(), Ast::Symbol(self.variable.clone())))
    //                }
    //                Ast::TheEmptyList if base => env,
    //                _ => Err(format!(
    //                    "{term} is not a symbol so it cannot be a parameter"
    //                )),
    //            },
    //            Ok(env),
    //        )?;
    //        let Pair(ref body, Ast::TheEmptyList) = **body else {
    //            Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
    //        };
    //        let exp_body = self.expand(body.clone().add_scope(sc), body_env)?;
    //        Ok(Ast::Pair(Box::new(Pair(
    //            lambda_id.clone(),
    //            Ast::Pair(Box::new(Pair(
    //                args,
    //                Ast::Pair(Box::new(Pair(exp_body, Ast::TheEmptyList))),
    //            ))),
    //        ))))
    //    }
    //
    //    pub(crate) fn expand_let_syntax(
    //        &mut self,
    //        s: Pair,
    //        env: CompileTimeEnvoirnment,
    //    ) -> Result<Ast, String> {
    //        // `(,let-syntax-id ([,lhs-id ,rhs] ...)
    //        //            ,body)
    //        // (cons 'let-syntax (cons (cons (cons 'lhs (cons 'rhs '())) '()) (cons 'body '())))
    //        // (let-syntax (...) ...)
    //        let Pair(ref _let_syntax_id, Ast::Pair(ref inner)) = s else {
    //            Err(format!("invalid syntax {s:?} bad let-syntax"))?
    //        };
    //        let Pair(ref binder_list, Ast::Pair(ref body)) = **inner else {
    //            Err(format!("invalid syntax {s:?} bad let-syntax {:?}", inner.0))?
    //        };
    //        let Pair(ref body, Ast::TheEmptyList) = **body else {
    //            Err(format!(
    //                "invalid syntax {s:?}, bad binder list for let-syntax {body:?}"
    //            ))?
    //        };
    //        let sc = self.scope_creator.new_scope();
    //        let binders = binder_list.clone().foldl(
    //            |binder, env: Result<CompileTimeEnvoirnment, String>| {
    //                let env = env?;
    //                let Ast::Pair(binder_list) = binder else {
    //                    Err(format!(
    //                        "invalid syntax {s:?}, bad binder list for let-syntax {binder_list:?}"
    //                    ))?
    //                };
    //                let Pair(Ast::Syntax(ref lhs_id), Ast::Pair(ref rhs_list)) = *binder_list else {
    //                    Err(format!(
    //                        "invalid syntax {s:?}, bad binder for let-syntax {binder_list:?}"
    //                    ))?
    //                };
    //                let Pair(ref rhs, Ast::TheEmptyList) = **rhs_list else {
    //                    Err(format!(
    //                        "invalid syntax {s:?}, bad binder list for let-syntax {rhs_list:?}"
    //                    ))?
    //                };
    //                let id = lhs_id.clone().add_scope(sc);
    //                let binding = self.add_local_binding(id);
    //                let rhs_val = self.eval_for_syntax_binding(rhs.clone())?;
    //                let body_env = env.extend(binding, rhs_val);
    //                Ok(body_env)
    //            },
    //            Ok(env),
    //        )??;
    //        //println!("found macro {binding}");
    //        //println!("expand {body} in {body_env:?}");
    //        self.expand(body.clone().add_scope(sc), binders)
    //    }
    //
    //    pub(crate) fn eval_for_syntax_binding(&mut self, rhs: Ast) -> Result<Ast, String> {
    //        // let var_name = format!("problem `evaluating` macro {rhs}");
    //        //println!("macro body {rhs}");
    //        let expand = self.expand(rhs, CompileTimeEnvoirnment::new())?;
    //        //println!("macro body {expand}");
    //        self.eval_compiled(self.compile(expand)?)
    //    }
    //
    //    #[trace::trace()]
    //    pub(crate) fn compile(&self, rhs: Ast) -> Result<Ast, String> {
    //        //println!("compile {rhs}");
    //        match rhs {
    //            Ast::Pair(l) => {
    //                let core_sym = if let Ast::Syntax(ref s) = l.0 {
    //                    self.resolve(s)
    //                } else {
    //                    Err("just for _ case in next match does not actually error".to_string())
    //                };
    //                match core_sym {
    //                    Ok(Binding::Lambda) => {
    //                        let Pair(ref _lambda_id, Ast::Pair(ref inner)) = *l else {
    //                            Err(format!("invalid syntax {l:?} bad lambda"))?
    //                        };
    //                        let Pair(ref args, Ast::Pair(ref body)) = **inner else {
    //                            Err(format!("invalid syntax {inner:?}, bad form for lambda"))?
    //                        };
    //
    //                        let args = args.clone().map_pair(|term, base| match term {
    //                            Ast::Syntax(id) => {
    //                                let Binding::Variable(id) = self.resolve(&id)? else {
    //                                    Err("bad syntax cannot play with core form")?
    //                                };
    //                                Ok(Ast::Symbol(id.clone()))
    //                            }
    //                            Ast::TheEmptyList if base => Ok(Ast::TheEmptyList),
    //                            _ => Err(format!(
    //                                "{term} is not a symbol so it cannot be a parameter"
    //                            )),
    //                        })?;
    //                        let Pair(ref body, Ast::TheEmptyList) = **body else {
    //                            Err(format!("invalid syntax {body:?}, bad body for lambda"))?
    //                        };
    //
    //                        // (list 'lambda (list 'x) 'body)
    //                        Ok(Ast::Pair(Box::new(Pair(
    //                            Ast::Symbol(Symbol("lambda".into(), 0)),
    //                            Ast::Pair(Box::new(Pair(
    //                                args,
    //                                Ast::Pair(Box::new(Pair(
    //                                    self.compile(body.clone())?,
    //                                    Ast::TheEmptyList,
    //                                ))),
    //                            ))),
    //                        ))))
    //                    }
    //                    Ok(Binding::Quote) => {
    //                        let Pair(_, Ast::Pair(datum)) = *l else {
    //                            Err("bad syntax, quote requires one expression")?
    //                        };
    //                        let Pair(datum, Ast::TheEmptyList) = *datum else {
    //                            Err("bad syntax, quote requires one expression")?
    //                        };
    //                        Ok(Ast::Pair(Box::new(Pair(
    //                            Ast::Symbol(Symbol("quote".into(), 0)),
    //                            Ast::Pair(Box::new(Pair(datum.syntax_to_datum(), Ast::TheEmptyList))),
    //                        ))))
    //                    }
    //                    Ok(Binding::QuoteSyntax) => {
    //                        let Pair(_, Ast::Pair(datum)) = *l else {
    //                            Err("bad syntax, quote-syntax requires one expression")?
    //                        };
    //                        let Pair(datum, Ast::TheEmptyList) = *datum else {
    //                            Err("bad syntax, quote-syntax requires one expression")?
    //                        };
    //                        Ok(Ast::Pair(Box::new(Pair(
    //                            Ast::Symbol(Symbol("quote".into(), 0)),
    //                            Ast::Pair(Box::new(Pair(datum, Ast::TheEmptyList))),
    //                        ))))
    //                    }
    //                    Ok(Binding::App) => {
    //                        let Pair(_, Ast::Pair(app)) = *l else {
    //                            Err("bad syntax, %app requires at least a function")?
    //                        };
    //                        if !app.1.list() {
    //                            Err("bad syntax, %app arguments must be a list")?;
    //                        }
    //                        Ok(Ast::Pair(Box::new(Pair(
    //                            self.compile(app.0)?,
    //                            app.1.map(|e| self.compile(e))?,
    //                        ))))
    //                    }
    //                    _ => Err(format!("unrecognized core form {}", l.0)),
    //                }
    //            }
    //            Ast::Syntax(s) => {
    //                if let Binding::Variable(s) = self.resolve(&s)? {
    //                    Ok(Ast::Symbol(s.clone()))
    //                } else {
    //                    Err("bad syntax cannot play with core form")?
    //                }
    //            }
    //            Ast::Number(_) | Ast::Boolean(_) | Ast::Function(_) => Ok(rhs),
    //            Ast::Symbol(_) | Ast::TheEmptyList => unreachable!(),
    //        }
    //    }
    //
    //    pub(crate) fn eval_compiled(&self, new: Ast) -> Result<Ast, String> {
    //        //println!("body {new}");
    //        evaluator::Evaluator::eval(new, self.env.clone())
    //    }
}
//
//#[derive(Clone, Debug)]
//pub struct CompileTimeEnvoirnment(HashMap<Symbol, Ast>);
//
//impl CompileTimeEnvoirnment {
//    pub(crate) fn new() -> Self {
//        Self(HashMap::new())
//    }
//
//    pub(crate) fn extend(&self, key: Symbol, value: Ast) -> Self {
//        let mut map = self.0.clone();
//        map.insert(key, value);
//        Self(map)
//    }
//
//    pub(crate) fn lookup(&self, key: &Symbol) -> Option<Ast> {
//        self.0.get(key).cloned()
//    }
//}
//
//// or maybe return error in resolve, instead of option
//pub fn check_unambiguous<'a>(
//    id: &Syntax,
//    mut candidate_ids: impl Iterator<Item = &'a Syntax>,
//) -> bool {
//    candidate_ids.all(|c_id| c_id.1.is_subset(&id.1))
//}
//
#[macro_export]
macro_rules! list {
    () => {$crate::ast::Ast::TheEmptyList};
    ($car:expr $(,)?) => {
        $crate::ast::Ast::Pair(Box::new($crate::ast::Pair($car, $crate::ast::Ast::TheEmptyList)))
    };
    ($car:expr, $($cdr:tt)+) => {
        $crate::ast::Ast::Pair(Box::new($crate::ast::Pair($car, list!($($cdr)+))))
    };
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
//#[cfg(test)]
//mod tests {
//    use core::panic;
//
//    use crate::{ast::Ast, evaluator::Evaluator, reader::Reader};
//
//    use super::{Binding, CompileTimeEnvoirnment, Expander};
//
//    impl Expander<Binding> {
//        fn expand_expression(&mut self, e: Ast) -> Result<Ast, String> {
//            self.expand(
//                self.namespace_syntax_introduce(e.datum_to_syntax(None)),
//                CompileTimeEnvoirnment::new(),
//            )
//        }
//
//        fn compile_eval_expression(&mut self, e: Ast) -> (Ast, Ast) {
//            let c = self
//                .expand_expression(e)
//                .and_then(|e| self.compile(e))
//                .and_then(|e| Evaluator::eval(e.clone(), self.env.clone()).map(|v| (e, v)));
//            match c {
//                Ok(v) => v,
//                Err(e) => panic!("{}", e),
//            }
//        }
//        fn eval_expression(&mut self, e: Ast, check: Option<Ast>) -> Ast {
//            let (_, v) = self.compile_eval_expression(e);
//            check.inspect(|check| assert_eq!(&v, check));
//            v
//        }
//    }
//
//    fn add_let(e: &str) -> String {
//        format!(
//            "(let-syntax ((let (lambda (stx)
//                       (datum->syntax
//                        (cons
//                         (list (quote-syntax lambda)
//                               (map car (car (cdr stx)))
//                               (car (cdr (cdr stx))))
//                         (map (lambda (b)
//                                (car (cdr b)))
//                              (car (cdr stx))))))))
//                {e})"
//        )
//    }
//
//    #[test]
//    fn expander_test_lambda() {
//        let mut expander = Expander::new();
//        expander.compile_eval_expression(list!(
//            Ast::Symbol("lambda".into()),
//            list!(Ast::Symbol("x".into())),
//            Ast::Symbol("x".into())
//        ));
//    }
//
//    #[test]
//    fn expander_test_basic_let() {
//        let mut expander = Expander::new();
//        let mut reader = Reader::new_with_input(&add_let("(lambda (x) (let ((y x)) y))"));
//        expander.compile_eval_expression(reader.read().unwrap());
//    }
//    #[test]
//    fn expander_test_basic_macro() {
//        let mut expander = Expander::new();
//        let mut reader = Reader::new_with_input(
//            &"(lambda (x)
//                (let-syntax ((y (lambda (stx) (quote-syntax 7))))
//     y))",
//        );
//        expander.compile_eval_expression(reader.read().unwrap());
//    }
//    #[test]
//    fn expander_test_complex_let() {
//        let mut expander = Expander::new();
//        let mut reader = Reader::new_with_input(&add_let(
//            "(let ((z 9))
//    (let-syntax (( m (lambda (stx) (car (cdr stx))) ))
//      (let (( x 5 )
//            ( y (lambda (z) z) ))
//        (let (( z 10 ))
//          (list z (m 10))))))",
//        ));
//        expander.compile_eval_expression(reader.read().unwrap());
//    }
//
//    #[test]
//    fn expander_test_expansion_not_captured() {
//        let mut expander = Expander::new();
//        let mut reader = Reader::new_with_input(&add_let(
//            &"(let ((x 'x-1))
//    (let-syntax ((m (lambda (stx) (quote-syntax x))))
//      (let ((x 'x-3))
//        (m))))",
//        ));
//        expander.eval_expression(reader.read().unwrap(), Some(Ast::Symbol("x-1".into())));
//    }
//
//    #[test]
//    fn expander_test_not_capturing_expansion() {
//        let mut expander = Expander::new();
//        let mut reader = Reader::new_with_input(&add_let(
//            &"(let (( x 'x-1 ))
//    (let-syntax (( m (lambda (stx)
//                      (datum->syntax
//                       (list (quote-syntax let)
//                             (list (list (quote-syntax x)
//                                         (quote-syntax 'x-2)))
//                             (car (cdr stx))))) ))
//      (let (( x 'x-3 ))
//        (m x))))",
//        ));
//        expander.eval_expression(reader.read().unwrap(), Some(Ast::Symbol("x-3".into())));
//    }
//
//    #[test]
//    fn expander_test_distinct_generated_variables_via_introduction_scope() {
//        let mut expander = Expander::new();
//        let mut reader = Reader::new_with_input(&add_let(
//            &"(let-syntax (( gen2 (lambda (stx)
//                        (datum->syntax
//                         (list (quote-syntax let)
//                               (list (list (car (cdr (cdr stx)))
//                                           (car (cdr (cdr (cdr (cdr stx))))))
//                                     (list (car (cdr (cdr (cdr stx))))
//                                           (car (cdr (cdr (cdr (cdr (cdr stx))))))))
//                               (list (quote-syntax list)
//                                     (car (cdr (cdr stx)))
//                                     (car (cdr (cdr (cdr stx)))))))) ))
//    (let-syntax (( gen1 (lambda (stx)
//                         (datum->syntax
//                          (cons (car (cdr stx))
//                                (cons (quote-syntax gen2)
//                                      (cons (quote-syntax x)
//                                            (cdr (cdr stx))))))) ))
//      (gen1 gen1 1 2)))",
//        ));
//        expander.eval_expression(
//            reader.read().unwrap(),
//            Some(list!(Ast::Number(1.), Ast::Number(2.))),
//        );
//    }
//    #[test]
//    fn expander_test_non_transformer_binding_misuse() {
//        let mut expander = Expander::new();
//        let mut reader = Reader::new_with_input(
//            &"(let-syntax ((v 1))
//                            v)",
//        );
//        assert!(expander
//            .expand(
//                expander.namespace_syntax_introduce(reader.read().unwrap().datum_to_syntax(None)),
//                CompileTimeEnvoirnment::new()
//            )
//            .is_err_and(|e| e.contains("illegal use of syntax")))
//    }
//}
