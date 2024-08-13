use crate::{
    ast::{AdjustScope, Ast, Function, Pair, Scope, Symbol, Syntax},
    evaluator::{self, Env},
    DEPTH,
};

use super::UniqueNumberManager;

use std::{
    collections::{BTreeSet, HashMap},
    fmt,
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Binding {
    Lambda,
    LetSyntax,
    Quote,
    QuoteSyntax,
    App,
    Variable(Symbol),
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Variable(s) => format!("{s}"),
                Self::Lambda => "lambda".to_string(),
                Self::LetSyntax => "let-syntax".to_string(),
                Self::Quote => "quote".to_string(),
                Self::QuoteSyntax => "quote-syntax".to_string(),
                Self::App => "%app".to_string(),
            }
        )
    }
}

impl From<Binding> for Symbol {
    fn from(value: Binding) -> Self {
        match value {
            Binding::Variable(s) => s,
            Binding::Lambda => "lambda".into(),
            Binding::LetSyntax => "let-syntax".into(),
            Binding::Quote => "quote".into(),
            Binding::QuoteSyntax => "quote-syntax".into(),
            Binding::App => "%app".into(),
        }
    }
}

#[derive(Debug)]
pub struct Expander<T> {
    pub(crate) all_bindings: HashMap<Syntax, T>,
    pub(crate) core_forms: BTreeSet<Binding>,
    pub(crate) core_primitives: BTreeSet<Binding>,
    pub(crate) core_scope: Scope,
    pub(crate) scope_creator: UniqueNumberManager,
    pub(crate) env: evaluator::EnvRef,
}

impl Default for Expander<Binding> {
    fn default() -> Self {
        Self::new()
    }
}

impl Expander<Binding> {
    #[must_use]
    pub fn new() -> Self {
        let mut scope_creator = UniqueNumberManager::new();
        let core_scope = scope_creator.new_scope();
        let core_forms = BTreeSet::from([
            Binding::Lambda,
            Binding::LetSyntax,
            Binding::Quote,
            Binding::QuoteSyntax,
            Binding::App,
        ]);
        let core_primitives = BTreeSet::from([
            Binding::Variable("datum->syntax".into()),
            Binding::Variable("syntax->datum".into()),
            Binding::Variable("syntax-e".into()),
            Binding::Variable("list".into()),
            Binding::Variable("cons".into()),
            Binding::Variable("car".into()),
            Binding::Variable("cdr".into()),
            Binding::Variable("map".into()),
        ]);
        let mut this = Self {
            scope_creator,
            core_scope,
            core_primitives,
            core_forms,
            all_bindings: HashMap::new(),
            env: Env::new_env(),
        };
        this.core_forms
            .clone()
            .union(&this.core_primitives.clone())
            .for_each(|core| {
                this.add_binding(
                    Syntax(core.clone().into(), BTreeSet::from([this.core_scope])),
                    core.clone(),
                );
            });
        this
    }
    pub(crate) fn add_binding(&mut self, id: Syntax, binding: Binding) {
        self.all_bindings.insert(id, binding);
    }

    pub(crate) fn add_local_binding(&mut self, id: Syntax) -> Symbol {
        let symbol = self.scope_creator.gen_sym(&id.0 .0);
        self.add_binding(id, Binding::Variable(symbol.clone()));
        symbol
    }

    pub(crate) fn resolve(&self, id: &Syntax) -> Result<&Binding, String> {
        let candidate_ids = self.find_all_matching_bindings(id);
        let id = candidate_ids
            .clone()
            .max_by_key(|id| id.1.len())
            .ok_or(format!("free variable {id:?}"))?;
        if check_unambiguous(id, candidate_ids) {
            self.all_bindings
                .get(id)
                .ok_or(format!("free variable {}", id.0 .0))
        } else {
            Err(format!("ambiguous binding {}", id.0 .0))
        }
    }

    pub(crate) fn free_identifier(&self, a: Ast, b: Ast) -> bool {
        matches!((a, b), (Ast::Syntax(a), Ast::Syntax(b)) if self.resolve( &a).is_ok_and(|a| self.resolve(&b).is_ok_and(|b| a == b )))
    }

    pub(crate) fn find_all_matching_bindings<'a>(
        &'a self,
        id: &'a Syntax,
    ) -> impl Iterator<Item = &Syntax> + Clone + 'a {
        self.all_bindings
            .keys()
            .filter(move |c_id| c_id.0 == id.0 && c_id.1.is_subset(&id.1))
    }

    pub fn namespace_syntax_introduce<T: AdjustScope>(&self, s: T) -> T {
        s.add_scope(self.core_scope)
    }

    #[trace::trace()]
    pub fn expand(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        match s {
            Ast::Syntax(s) => self.expand_identifier(s, env),
            Ast::Pair(l) if matches!(&l.0, Ast::Syntax(_)) => {
                self.expand_id_application_form(*l, env)
            }
            Ast::Pair(l) => self.expand_app(*l, env),
            _ => Ok(Ast::Pair(Box::new(Pair(
                Ast::Syntax(Syntax("quote".into(), BTreeSet::from([self.core_scope]))),
                Ast::Pair(Box::new(Pair(s, Ast::TheEmptyList))),
            )))),
        }
    }

    pub(crate) fn expand_identifier(
        &mut self,
        s: Syntax,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let binding = self.resolve(&s)?;
        if self.core_forms.contains(binding) {
            Err(format!("bad syntax dangling core form {}", s.0))
        } else if self.core_primitives.contains(binding) {
            Ok(Ast::Syntax(s))
        } else {
            //println!("lookup {s:?} {:?}", env);
            let Binding::Variable(binding) = binding else {
                panic!()
            };
            let v = env.lookup(binding).ok_or(format!("out of context {s:?}"))?;
            match v {
                CompileTimeBinding::Symbol(_) => Err(format!("illegal use of syntax {s:?}")),
                CompileTimeBinding::Macro(m) => self.apply_transformer(m, Ast::Syntax(s)), //_ => Err(format!("bad syntax non function call macro {}", s.0)),
            }
        }
    }

    // constraints = s.len() > 0
    // constraints = s[0] == Ast::Syntax(_)
    pub(crate) fn expand_id_application_form(
        &mut self,
        s: Pair,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let Ast::Syntax(ref id) = s.0 else {
            unreachable!()
        };
        let binding = self.resolve(id)?;
        match binding {
            Binding::Lambda => self.expand_lambda(s, env),
            Binding::LetSyntax => self.expand_let_syntax(s, env),
            Binding::Quote | Binding::QuoteSyntax => Ok(Ast::Pair(Box::new(s))),
            Binding::App => {
                if !s.list() {
                    Err("%app form's arguements must be a list".to_string())?;
                }
                // TODO: empty list
                let Ast::Pair(p) = s.1 else { unreachable!() };
                self.expand_app(*p, env)
            }
            Binding::Variable(binding) => match env.lookup(binding) {
                Some(CompileTimeBinding::Macro(m)) => {
                    //println!("{binding} in {env:?}");
                    let apply_transformer = self.apply_transformer(m, Ast::Pair(Box::new(s)))?;
                    //println!("app {apply_transformer}");
                    self.expand(apply_transformer, env)
                }
                _ => self.expand_app(s, env),
            },
        }
    }
    pub(crate) fn apply_transformer(&mut self, m: Function, s: Ast) -> Result<Ast, String> {
        let intro_scope = self.scope_creator.new_scope();
        //println!("apply_transformer {s:?}");
        let intro_s = s.add_scope(intro_scope);
        let transformed_s = m.apply(Ast::Pair(Box::new(Pair(intro_s, Ast::TheEmptyList))))?;

        Ok(transformed_s.flip_scope(intro_scope))
    }
    pub(crate) fn expand_app(
        &mut self,
        s: Pair,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let Pair(rator, rands) = s;

        Ok(Ast::Pair(Box::new(Pair(
            Ast::Syntax(Syntax("%app".into(), BTreeSet::from([self.core_scope]))),
            Ast::Pair(Box::new(Pair(
                self.expand(rator, env.clone())?,
                rands.map(|rand| self.expand(rand, env.clone()))?,
            ))),
        ))))
    }

    pub(crate) fn expand_lambda(
        &mut self,
        s: Pair,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        //println!("lambda body {s:?}");
        let Pair(ref lambda_id, Ast::Pair(ref inner)) = s else {
            Err(format!("invalid syntax {s:?} bad lambda"))?
        };
        let Pair(ref args, Ast::Pair(ref body)) = **inner else {
            Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
        };
        let sc = self.scope_creator.new_scope();
        let args = args.clone().map_pair(|term, base| match term {
            Ast::Syntax(id) => {
                let id = id.add_scope(sc);
                Ok(Ast::Syntax(id))
            }
            Ast::TheEmptyList if base => Ok(Ast::TheEmptyList),
            _ => Err(format!(
                "{term} is not a symbol so it cannot be a parameter"
            )),
        })?;
        let body_env = args.clone().foldl_pair(
            |term, base, env: Result<CompileTimeEnvoirnment, String>| match term {
                Ast::Syntax(id) => {
                    let binding = self.add_local_binding(id);
                    env.map(|env| env.extend(binding.clone(), CompileTimeBinding::Symbol(binding)))
                }
                Ast::TheEmptyList if base => env,
                _ => Err(format!(
                    "{term} is not a symbol so it cannot be a parameter"
                )),
            },
            Ok(env),
        )?;
        let Pair(ref body, Ast::TheEmptyList) = **body else {
            Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
        };
        let exp_body = self.expand(body.clone().add_scope(sc), body_env)?;
        Ok(Ast::Pair(Box::new(Pair(
            lambda_id.clone(),
            Ast::Pair(Box::new(Pair(
                args,
                Ast::Pair(Box::new(Pair(exp_body, Ast::TheEmptyList))),
            ))),
        ))))
    }

    pub(crate) fn expand_let_syntax(
        &mut self,
        s: Pair,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        // `(,let-syntax-id ([,lhs-id ,rhs] ...)
        //            ,body)
        // (cons 'let-syntax (cons (cons (cons 'lhs (cons 'rhs '())) '()) (cons 'body '())))
        // (let-syntax (...) ...)
        let Pair(ref _let_syntax_id, Ast::Pair(ref inner)) = s else {
            Err(format!("invalid syntax {s:?} bad let-syntax"))?
        };
        let Pair(ref binder_list, Ast::Pair(ref body)) = **inner else {
            Err(format!("invalid syntax {s:?} bad let-syntax {:?}", inner.0))?
        };
        let Pair(ref body, Ast::TheEmptyList) = **body else {
            Err(format!(
                "invalid syntax {s:?}, bad binder list for let-syntax {body:?}"
            ))?
        };
        let sc = self.scope_creator.new_scope();
        let binders = binder_list.clone().foldl(
            |binder, env: Result<CompileTimeEnvoirnment, String>| {
                let env = env?;
                let Ast::Pair(binder_list) = binder else {
                    Err(format!(
                        "invalid syntax {s:?}, bad binder list for let-syntax {binder_list:?}"
                    ))?
                };
                let Pair(Ast::Syntax(ref lhs_id), Ast::Pair(ref rhs_list)) = *binder_list else {
                    Err(format!(
                        "invalid syntax {s:?}, bad binder for let-syntax {binder_list:?}"
                    ))?
                };
                let Pair(ref rhs, Ast::TheEmptyList) = **rhs_list else {
                    Err(format!(
                        "invalid syntax {s:?}, bad binder list for let-syntax {rhs_list:?}"
                    ))?
                };
                let id = lhs_id.clone().add_scope(sc);
                let binding = self.add_local_binding(id);
                let rhs_val = self.eval_for_syntax_binding(rhs.clone())?;
                let body_env = env.extend(binding, rhs_val);
                Ok(body_env)
            },
            Ok(env),
        )??;
        //println!("found macro {binding}");
        //println!("expand {body} in {body_env:?}");
        self.expand(body.clone().add_scope(sc), binders)
    }

    pub(crate) fn eval_for_syntax_binding(
        &mut self,
        rhs: Ast,
    ) -> Result<CompileTimeBinding, String> {
        // let var_name = format!("problem `evaluating` macro {rhs}");
        //println!("macro body {rhs}");
        let expand = self.expand(rhs, CompileTimeEnvoirnment::new())?;
        //println!("macro body {expand}");
        self.eval_compiled(self.compile(expand)?).and_then(|e| {
            if let Ast::Function(f) = e {
                Ok(CompileTimeBinding::Macro(f))
            } else {
                Err(format!("{e} is not a macro"))
            }
        })
    }

    #[trace::trace()]
    pub(crate) fn compile(&self, rhs: Ast) -> Result<Ast, String> {
        //println!("compile {rhs}");
        match rhs {
            Ast::Pair(l) => {
                let core_sym = if let Ast::Syntax(ref s) = l.0 {
                    self.resolve(s)
                } else {
                    Err("just for _ case in next match does not actually error".to_string())
                };
                match core_sym {
                    Ok(Binding::Lambda) => {
                        let Pair(ref _lambda_id, Ast::Pair(ref inner)) = *l else {
                            Err(format!("invalid syntax {l:?} bad lambda"))?
                        };
                        let Pair(ref args, Ast::Pair(ref body)) = **inner else {
                            Err(format!("invalid syntax {inner:?}, bad form for lambda"))?
                        };

                        let args = args.clone().map_pair(|term, base| match term {
                            Ast::Syntax(id) => {
                                let Binding::Variable(id) = self.resolve(&id)? else {
                                    Err("bad syntax cannot play with core form")?
                                };
                                Ok(Ast::Symbol(id.clone()))
                            }
                            Ast::TheEmptyList if base => Ok(Ast::TheEmptyList),
                            _ => Err(format!(
                                "{term} is not a symbol so it cannot be a parameter"
                            )),
                        })?;
                        let Pair(ref body, Ast::TheEmptyList) = **body else {
                            Err(format!("invalid syntax {body:?}, bad body for lambda"))?
                        };

                        // (list 'lambda (list 'x) 'body)
                        Ok(Ast::Pair(Box::new(Pair(
                            Ast::Symbol(Symbol("lambda".into(), 0)),
                            Ast::Pair(Box::new(Pair(
                                args,
                                Ast::Pair(Box::new(Pair(
                                    self.compile(body.clone())?,
                                    Ast::TheEmptyList,
                                ))),
                            ))),
                        ))))
                    }
                    Ok(Binding::Quote) => {
                        let Pair(_, Ast::Pair(datum)) = *l else {
                            Err("bad syntax, quote requires one expression")?
                        };
                        let Pair(datum, Ast::TheEmptyList) = *datum else {
                            Err("bad syntax, quote requires one expression")?
                        };
                        Ok(Ast::Pair(Box::new(Pair(
                            Ast::Symbol(Symbol("quote".into(), 0)),
                            Ast::Pair(Box::new(Pair(datum.syntax_to_datum(), Ast::TheEmptyList))),
                        ))))
                    }
                    Ok(Binding::QuoteSyntax) => {
                        let Pair(_, Ast::Pair(datum)) = *l else {
                            Err("bad syntax, quote-syntax requires one expression")?
                        };
                        let Pair(datum, Ast::TheEmptyList) = *datum else {
                            Err("bad syntax, quote-syntax requires one expression")?
                        };
                        Ok(Ast::Pair(Box::new(Pair(
                            Ast::Symbol(Symbol("quote".into(), 0)),
                            Ast::Pair(Box::new(Pair(datum, Ast::TheEmptyList))),
                        ))))
                    }
                    Ok(Binding::App) => {
                        let Pair(_, Ast::Pair(app)) = *l else {
                            Err("bad syntax, %app requires at least a function")?
                        };
                        if !app.1.list() {
                            Err("bad syntax, %app arguments must be a list")?;
                        }
                        Ok(Ast::Pair(Box::new(Pair(
                            self.compile(app.0)?,
                            app.1.map(|e| self.compile(e))?,
                        ))))
                    }
                    _ => Err(format!("unrecognized core form {}", l.0)),
                }
            }
            Ast::Syntax(s) => {
                if let Binding::Variable(s) = self.resolve(&s)? {
                    Ok(Ast::Symbol(s.clone()))
                } else {
                    Err("bad syntax cannot play with core form")?
                }
            }
            Ast::Number(_) | Ast::Function(_) => Ok(rhs),
            Ast::Symbol(_) | Ast::TheEmptyList => unreachable!(),
        }
    }

    pub(crate) fn eval_compiled(&self, new: Ast) -> Result<Ast, String> {
        //println!("body {new}");
        evaluator::Evaluator::eval(new, self.env.clone())
    }
}

#[derive(Clone, Debug)]
pub enum CompileTimeBinding {
    Symbol(Symbol),
    Macro(Function),
}

#[derive(Clone, Debug)]
pub struct CompileTimeEnvoirnment(HashMap<Symbol, CompileTimeBinding>);

impl CompileTimeEnvoirnment {
    pub(crate) fn new() -> Self {
        Self(HashMap::new())
    }

    pub(crate) fn extend(&self, key: Symbol, value: CompileTimeBinding) -> Self {
        let mut map = self.0.clone();
        map.insert(key, value);
        Self(map)
    }

    pub(crate) fn lookup(&self, key: &Symbol) -> Option<CompileTimeBinding> {
        self.0.get(key).cloned()
    }
}

// TODO: return error if ambiguous
// or maybe return error in resolve, instead of option
pub fn check_unambiguous<'a>(
    id: &Syntax,
    mut candidate_ids: impl Iterator<Item = &'a Syntax>,
) -> bool {
    candidate_ids.all(|c_id| c_id.1.is_subset(&id.1))
}

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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::ast::{bound_identifier, Ast, Scope, Symbol, Syntax};

    #[test]
    fn bound_identifier_same() {
        list!(Ast::Symbol("a".into()), Ast::Symbol("b".into()));
        assert!(bound_identifier(
            Ast::Syntax(Syntax("a".into(), BTreeSet::from([Scope(0)]))),
            Ast::Syntax(Syntax("a".into(), BTreeSet::from([Scope(0)])))
        ))
    }
    #[test]
    fn bound_identifier_different_symbol() {
        assert!(!bound_identifier(
            Ast::Syntax(Syntax("a".into(), BTreeSet::from([Scope(0)]))),
            Ast::Syntax(Syntax("b".into(), BTreeSet::from([Scope(0)])))
        ))
    }
    #[test]
    fn bound_identifier_different_scope() {
        assert!(!bound_identifier(
            Ast::Syntax(Syntax("a".into(), BTreeSet::from([Scope(0)]))),
            Ast::Syntax(Syntax("a".into(), BTreeSet::from([Scope(1)])))
        ))
    }

    #[test]
    fn datum_to_syntax_with_identifier() {
        assert_eq!(
            Ast::Symbol("a".into()).datum_to_syntax(),
            Ast::Syntax(Syntax("a".into(), BTreeSet::new()))
        );
    }

    #[test]
    fn datum_to_syntax_with_number() {
        assert_eq!(Ast::Number(1.0).datum_to_syntax(), Ast::Number(1.0));
    }

    #[test]
    fn datum_to_syntax_with_list() {
        assert_eq!(
            list![
                Ast::Symbol(Symbol("a".into(), 0)),
                Ast::Symbol(Symbol("b".into(), 0)),
                Ast::Symbol(Symbol("c".into(), 0)),
            ]
            .datum_to_syntax(),
            list![
                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("b".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
            ]
        );
    }
    #[test]
    fn datum_to_syntax_with_list_and_syntax() {
        assert_eq!(
            list![
                Ast::Symbol(Symbol("a".into(), 0)),
                Ast::Syntax(Syntax("b".into(), BTreeSet::new())),
                Ast::Symbol(Symbol("c".into(), 0)),
            ]
            .datum_to_syntax(),
            list![
                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("b".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
            ]
        );
    }
}
