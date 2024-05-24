#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![deny(static_mut_refs)]
#![deny(clippy::use_self, rust_2018_idioms, clippy::missing_panics_doc)]
use crate::binding::CompileTimeBinding;
use crate::binding::CompileTimeEnvoirnment;
use crate::binding::Binding;
use crate::scope::AdjustScope;
use core::panic;
use std::collections::HashMap;
use std::fmt::{self, Debug};
use std::io::{BufRead, BufReader, Write};
use std::iter::Peekable;
use std::{cell::RefCell, cmp::Ordering};
use std::{collections::BTreeSet, rc::Rc};

use scope::Scope;
use syntax::Syntax;
mod binding;
mod expand;
mod scope;
mod syntax;
mod r#match;

// use trace::trace;
// #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
// struct Scope(usize);
#[derive(Debug)]
struct UniqueNumberManager(usize);

// static mut UNIQUE_NUMBER_GENERATOR: usize = 1;
// fn unique_number_generator() -> usize {
//     unsafe {
//         let current = UNIQUE_NUMBER_GENERATOR;
//         UNIQUE_NUMBER_GENERATOR += 1;
//         current
//     }
// }
impl UniqueNumberManager {
    fn new() -> Self {
        Self(1)
    }

    fn next(&mut self) -> usize {
        let current = self.0;
        self.0 += 1;
        current
    }

    fn new_scope(&mut self) -> Scope {
        Scope(self.next())
    }

    fn gen_sym(&mut self, name: impl ToString) -> Symbol {
        Symbol(name.to_string().into(), self.next())
    }
}

type ScopeSet = BTreeSet<Scope>;
// #[derive(Clone, PartialEq, Eq, Debug, Hash)]
// pub struct Syntax(Symbol, ScopeSet);

// trait AdjustScope: Sized {
//     fn adjust_scope(
//         self,
//         other_scope: Scope,
//         operation: fn(ScopeSet, Scope) -> BTreeSet<Scope>,
//     ) -> Self;
//
//     fn add_scope(self, other_scope: Scope) -> Self {
//         self.adjust_scope(other_scope, |mut scopes, other_scope| {
//             scopes.insert(other_scope);
//             scopes
//         })
//     }
//
//     fn flip_scope(self, other_scope: Scope) -> Self {
//         self.adjust_scope(other_scope, |mut scopes, other_scope| {
//             if !scopes.remove(&other_scope) {
//                 scopes.insert(other_scope);
//             }
//             scopes
//         })
//     }
// }

// impl Syntax {
//     #[must_use]
//     pub fn new(symbol: Symbol) -> Self {
//         Self(symbol, BTreeSet::new())
//     }
// }

// impl AdjustScope for Syntax {
//     fn adjust_scope(
//         self,
//         other_scope_set: Scope,
//         operation: fn(ScopeSet, Scope) -> BTreeSet<Scope>,
//     ) -> Self {
//         Self(self.0, operation(self.1, other_scope_set))
//     }
// }

pub type AnalyzedResult = Result<Box<dyn AnalyzeFn>, String>;
pub trait AnalyzeFn: Fn(EnvRef) -> Result<Ast, String> {
    fn clone_box<'a>(&self) -> Box<dyn 'a + AnalyzeFn>
    where
        Self: 'a;
}

impl<F> AnalyzeFn for F
where
    F: Fn(EnvRef) -> Result<Ast, String> + Clone,
{
    fn clone_box<'a>(&self) -> Box<dyn 'a + AnalyzeFn>
    where
        Self: 'a,
    {
        Box::new(self.clone())
    }
}
impl<'a> Clone for Box<dyn 'a + AnalyzeFn> {
    fn clone(&self) -> Self {
        (**self).clone_box()
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Function {
    Lambda(Lambda),
    Primitive(Primitive),
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lambda(_) => write!(f, "(procedure)"),
            Self::Primitive(_) => write!(f, "(primitive-procedure)"),
        }
    }
}

impl Function {
    fn apply(&self, args: Vec<Ast>) -> Result<Ast, String> {
        match self {
            Self::Lambda(Lambda(body, env, params)) => {
                let env = Env::extend_envoirnment(env.clone(), params, args)?;
                body(env)
            }
            Self::Primitive(p) => p(args),
        }
    }
}

#[derive(Clone)]
pub struct Lambda(Box<dyn AnalyzeFn>, EnvRef, Vec<Symbol>);

impl PartialEq for Lambda {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}
impl fmt::Debug for Lambda {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(procedure)")
    }
}
type Primitive = fn(Vec<Ast>) -> Result<Ast, String>;
#[derive(Clone, PartialEq, Debug)]
pub enum Ast {
    List(Vec<Ast>),
    Syntax(Box<Syntax<Ast>>),
    Number(f64),
    Boolean(bool),
    Symbol(Symbol),
    Function(Function),
}
impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::List(l) => write!(
                f,
                "({})",
                l.into_iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" "),
            ),
            Self::Syntax(s) => write!(f, "#'{}", s.0),
            Self::Number(n) => write!(f, "{n}"),
            Self::Symbol(s) => write!(f, "{s}"),
            Self::Function(function) => write!(f, "{function}"),
            Self::Boolean(b) => write!(f, "{b}"),
        }
    }
}
impl Ast {
    // pub fn datum_to_syntax(self) -> Self {
    //     match self {
    //         Self::List(l) => Self::List(l.into_iter().map(Self::datum_to_syntax).collect()),
    //         Self::Syntax(_) => self,
    //         Self::Symbol(s) => Self::Syntax(Syntax::new(s)),
    //         _ => self,
    //     }
    // }
    // fn syntax_to_datum(self) -> Self {
    //     match self {
    //         Self::List(l) => Self::List(l.into_iter().map(Self::syntax_to_datum).collect()),
    //         Self::Syntax(Syntax(s, _)) => Self::Symbol(s),
    //         _ => self,
    //     }
    // }
    // fn identifier(&self) -> bool {
    //         matches!(self, Self::Syntax(_))
    //     }
}

#[derive(Debug)]
pub struct Expander {
    core_forms: BTreeSet<Binding>,
    core_primitives: BTreeSet<Binding>,
    core_scope: Scope,
    scope_creator: UniqueNumberManager,
    all_bindings: HashMap<Syntax<Symbol>, Binding>,
    env: EnvRef,
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
        let core_forms = BTreeSet::from([
            Binding::Lambda,
            Binding::LetSyntax,
            Binding::Quote,
            Binding::QuoteSyntax,
        ]);
        let core_primitives = BTreeSet::from([
            Binding::Variable("datum->syntax".into()),
            Binding::Variable("syntax->datum".into()),
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
            env: new_env(),
        };
        this.core_forms
            .clone()
            .union(&this.core_primitives.clone())
            .for_each(|core| {
                this.all_bindings.add_binding(
                    Syntax(core.clone().into(), BTreeSet::from([this.core_scope])),
                    core.clone(),
                );
            });
        this
    }

    

    pub fn introduce<T: AdjustScope>(&self, s: T) -> T {
        s.add_scope(self.core_scope)
    }

    pub fn expand(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        match s {
            Ast::List(l) if matches!(&l[..], [s, ..] if s.identifier()) => {
                self.expand_id_application_form(l, env)
            }
            Ast::Syntax(s) => self.expand_identifier(s, env),
            Ast::Number(_) | Ast::Function(_) | Ast::Boolean(_) => Ok(s),
            Ast::Symbol(_) => unreachable!(),
            Ast::List(l) => self.expand_app(l, env),
        }
    }

    fn expand_identifier(&self, s: Syntax, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        let binding = self.resolve(&s)?;
        if self.core_forms.contains(binding) {
            Err(format!("bad syntax dangling core form {}", s.0))
        } else if self.core_primitives.contains(binding) {
            Ok(Ast::Syntax(s))
        } else {
            println!("{:?}", self.core_primitives);
            let Binding::Variable(binding) = binding else {
                panic!()
            };
            let v = env
                .lookup(binding)
                .ok_or(format!("out of context {}", s.0))?;
            if let CompileTimeBinding::Variable(_) = v {
                Ok(Ast::Syntax(s))
            } else {
                Err(format!("bad syntax non function call macro {}", s.0))
            }
        }
    }

    // constraints = s.len() > 0
    // constraints = s[0] == Ast::Syntax(_)
    fn expand_id_application_form(
        &mut self,
        s: Vec<Ast>,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let Some(a) = s.first() else { unreachable!() };
        // let try_into = TryFrom::<Syntax<Ast>>::try_from(a)?;
        let binding = self.resolve(&(*a).clone().try_into()?)?;
        match binding {
            Binding::Lambda => self.expand_lambda(s, env),
            Binding::LetSyntax => self.expand_let_syntax(s, env),
            Binding::Quote | Binding::QuoteSyntax => match &s[..] {
                [_, _] => Ok(Ast::List(s)),
                _ => Err(format!("bad syntax to many expression in quote {s:?}")),
            },
            Binding::Variable(binding) => match env.lookup(binding) {
                Some(CompileTimeBinding::Procedure(m)) => {
                    let apply_transformer = self.apply_transformer(m, Ast::List(s));
                    self.expand(apply_transformer?, env)
                }
                _ => self.expand_app(s, env),
            },
        }
    }

    fn expand_app(&mut self, s: Vec<Ast>, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        s.into_iter()
            .map(|sub_s| self.expand(sub_s, env.clone()))
            .collect::<Result<Vec<_>, _>>()
            .map(Ast::List)
    }

    fn expand_lambda(&mut self, s: Vec<Ast>, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        let [lambda_id, Ast::List(arg), body] = &s[..] else {
            Err(format!("invalid syntax {s:?} bad lambda"))?
        };
        let [Ast::Syntax(arg_id)] = &arg[..] else {
            Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
        };
        let sc = self.scope_creator.new_scope();
        let id = arg_id.clone().add_scope(sc);
        let binding = self.add_local_binding(id.clone());
        let body_env = env.extend(binding.clone(), CompileTimeBinding::Variable(binding));
        let exp_body = self.expand(body.clone().add_scope(sc), body_env)?;
        Ok(Ast::List(vec![
            lambda_id.clone(),
            Ast::List(vec![Ast::Syntax(id)]),
            exp_body,
        ]))
    }

    fn expand_let_syntax(
        &mut self,
        s: Vec<Ast>,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let [_let_syntax_id, Ast::List(arg), body] = &s[..] else {
            Err(format!("invalid syntax {s:?} bad let-syntax"))?
        };
        let [Ast::List(arg)] = &arg[..] else {
            Err(format!(
                "invalid syntax {s:?}, bad binder list for let-syntax {arg:?}"
            ))?
        };
        let [Ast::Syntax(lhs_id), rhs] = &arg[..] else {
            Err(format!(
                "invalid syntax {s:?}, bad binder for let-syntax {arg:?}"
            ))?
        };
        let sc = self.scope_creator.new_scope();
        let id = lhs_id.clone().add_scope(sc);
        let binding = self.add_local_binding(id);
        let rhs_val = self.eval_for_syntax_binding(rhs.clone())?;
        let body_env = env.extend(binding, rhs_val);
        self.expand(body.clone().add_scope(sc), body_env)
    }

    fn eval_for_syntax_binding(&mut self, rhs: Ast) -> Result<CompileTimeBinding, String> {
        // let var_name = format!("problem `evaluating` macro {rhs}");
        let expand = self.expand(rhs, CompileTimeEnvoirnment::new());
        self.eval_compiled(self.compile(expand?)?).and_then(|e| {
            if let Ast::Function(f) = e {
                Ok(CompileTimeBinding::Procedure(f))
            } else {
                Err(format!("{e} is not a macro"))
            }
        })
    }

    fn compile(&self, rhs: Ast) -> Result<Ast, String> {
        match rhs {
            Ast::List(l) => {
                let s = l
                    .first()
                    .ok_or("bad syntax empty application".to_string())?;
                let core_sym = if let Ast::Syntax(s) = s {
                    self.resolve(s)
                } else {
                    Err("just for _ case in next match does not actually error".to_string())
                };
                match core_sym {
                    Ok(Binding::Lambda) => {
                        let [_, Ast::List(arg), body] = &l[..] else {
                            Err("bad syntax lambda")?
                        };
                        let [Ast::Syntax(id)] = &arg[..] else {
                            Err("bad syntax lambda arg")?
                        };
                        let Binding::Variable(id) = self.resolve(id)? else {
                            Err("bad syntax cannot play with core form")?
                        };
                        Ok(Ast::List(vec![
                            Ast::Symbol(Symbol("lambda".into(), 0)),
                            Ast::List(vec![Ast::Symbol(id.clone())]),
                            self.compile(body.clone())?,
                        ]))
                    }
                    Ok(Binding::Quote) => {
                        if let [_, datum] = &l[..] {
                            Ok(Ast::List(vec![
                                Ast::Symbol(Symbol("quote".into(), 0)),
                                datum.clone().syntax_to_datum(),
                            ]))
                        } else {
                            Err("bad syntax, quote requires one expression")?
                        }
                    }
                    Ok(Binding::QuoteSyntax) => {
                        if let [_, datum] = &l[..] {
                            Ok(Ast::List(vec![
                                Ast::Symbol(Symbol("quote".into(), 0)),
                                datum.clone(),
                            ]))
                        } else {
                            Err("bad syntax, quote-syntax requires one expression")?
                        }
                    }
                    _ => Ok(Ast::List(
                        l.into_iter()
                            .map(|e| self.compile(e))
                            .collect::<Result<Vec<_>, _>>()?,
                    )),
                }
            }
            Ast::Syntax(s) => {
                if let Binding::Variable(s) = self.resolve(&s)? {
                    Ok(Ast::Symbol(s.clone()))
                } else {
                    Err("bad syntax cannot play with core form")?
                }
            }
            Ast::Boolean(_) | Ast::Number(_) | Ast::Function(_) => Ok(rhs),

            Ast::Symbol(_) => unreachable!(),
        }
    }

    fn eval_compiled(&self, new: Ast) -> Result<Ast, String> {
        Evaluator::eval(new, self.env.clone())
    }

    fn apply_transformer(&mut self, m: Function, s: Ast) -> Result<Ast, String> {
        let intro_scope = self.scope_creator.new_scope();
        let intro_s = s.add_scope(intro_scope);
        let transformed_s = m.apply(vec![intro_s])?;

        Ok(transformed_s.flip_scope(intro_scope))
    }
}

fn new_env() -> Rc<RefCell<Env>> {
    let env = Env::new();
    env.borrow_mut().define(
        Symbol("datum->syntax".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let [e] = &e[..] else {
                Err(format!("arity error: expected 1 argument, got {}", e.len()))?
            };
            Ok(e.clone().datum_to_syntax(None))
        })),
    );
    env.borrow_mut().define(
        Symbol("syntax->datum".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let [e] = &e[..] else {
                Err(format!("arity error: expected 1 argument, got {}", e.len()))?
            };
            Ok(e.clone().syntax_to_datum())
        })),
    );
    env.borrow_mut().define(
        Symbol("syntax-e".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let [Ast::Syntax(s)] = &e[..] else {
                Err(format!("arity error: expected 1 argument, got {}", e.len()))?
            };
            Ok(s.0.clone())
        })),
    );
    env.borrow_mut().define(
        Symbol("cons".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            if e.len() != 2 {
                Err(format!("arity error: expected 2 argument, got {}", e.len()))?
            };
            Ok(Ast::List(e))
        })),
    );
    env.borrow_mut().define(
        Symbol("car".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let [Ast::List(cons)] = &e[..] else {
                Err(format!(
                    "arity error: expected 1 argument, got {}, or was not cons",
                    e.len()
                ))?
            };
            let [fst, ..] = &cons[..] else {
                Err(format!("arity error: expected 1 argument, got {}", e.len()))?
            };
            Ok(fst.clone())
        })),
    );
    env.borrow_mut().define(
        Symbol("cdr".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let [Ast::List(cons)] = &e[..] else {
                Err(format!(
                    "arity error: expected 1 argument, got {}, or was not cons",
                    e.len()
                ))?
            };
            let [_, rest @ ..] = &cons[..] else {
                Err(format!("arity error: expected 1 argument, got {}", e.len()))?
            };
            Ok(Ast::List(rest.to_vec()))
        })),
    );
    env.borrow_mut().define(
        Symbol("list".into(), 0),
        Ast::Function(Function::Primitive(move |e| Ok(Ast::List(e)))),
    );
    env.borrow_mut().define(
        Symbol("map".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let [Ast::Function(f), Ast::List(cons)] = &e[..] else {
                Err(format!(
                    "arity error: expected 2 argument, got {}, or was not function, cons",
                    e.len()
                ))?
            };
            Ok(Ast::List(
                cons.into_iter()
                    .map(|a| f.apply(vec![a.clone()]))
                    .collect::<Result<Vec<_>, _>>()?,
            ))
        })),
    );
    env
}

#[derive(Clone, PartialEq, Debug)]
pub struct Env {
    scope: HashMap<Symbol, Ast>,
    parent: Option<EnvRef>,
}

impl Env {
    fn lookup(&self, symbol: &Symbol) -> Option<Ast> {
        self.scope.get(symbol).cloned().or_else(|| {
            self.parent
                .as_ref()
                .and_then(|parent| parent.borrow().lookup(symbol))
        })
    }
    fn set(&mut self, symbol: Symbol, mut expr: Ast) -> Option<Ast> {
        {
            match self.scope.get_mut(&symbol) {
                Some(s) => {
                    std::mem::swap(s, &mut expr);
                    Some(expr)
                }
                None => self
                    .parent
                    .as_ref()
                    .and_then(|parent| parent.borrow_mut().set(symbol, expr)),
            }
        }
    }
    fn define(&mut self, symbol: Symbol, expr: Ast) -> bool {
        self.scope.insert(symbol, expr).is_some()
    }
    fn new_scope(env: EnvRef) -> EnvRef {
        let parent = Some(env);
        let scope = HashMap::new();
        Rc::new(RefCell::new(Self { scope, parent }))
    }

    fn extend_envoirnment(
        env: EnvRef,
        params: &[Symbol],
        args: Vec<Ast>,
    ) -> Result<EnvRef, String> {
        let new_envoirnment = Self::new_scope(env);
        match params.len().cmp(&args.len()) {
            Ordering::Less => Err("arity error to many arguments passed in".to_string()),
            Ordering::Greater => Err("arity error to little arguments passed in".to_string()),
            Ordering::Equal => {
                for (param, arg) in params.iter().zip(args.into_iter()) {
                    new_envoirnment.borrow_mut().define(param.clone(), arg);
                }
                Ok(new_envoirnment)
            }
        }
    }

    fn new() -> EnvRef {
        let scope = HashMap::new();
        // TODO: primitive environment
        let parent = None;
        Rc::new(RefCell::new(Self { scope, parent }))
    }
}

type EnvRef = Rc<RefCell<Env>>;

pub struct Evaluator {}

impl Evaluator {
    fn eval(expr: Ast, env: EnvRef) -> Result<Ast, String> {
        Self::analyze(expr)?(env)
    }
    fn analyze(expr: Ast) -> AnalyzedResult {
        match expr {
            Ast::List(list) => match list.first() {
                Some(Ast::Symbol(Symbol(lambda, 0))) if **lambda == *"lambda" => {
                    let mut list = list.clone().into_iter().skip(1);
                    let (Some(Ast::List(arg)), Some(body), None) =
                        (list.next(), list.next(), list.next())
                    else {
                        Err(format!(
                            "bad syntax {list:?}, lambda not in form (lambda (args) body)"
                        ))?
                    };
                    let args = arg
                        .into_iter()
                        .map(|arg| {
                            if let Ast::Symbol(s) = arg {
                                Ok(s)
                            } else {
                                Err(format!("bad syntax {arg} is not a valid paramter"))
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let body = Self::analyze(body)?;
                    Ok(Box::new(move |env| {
                        Ok(Ast::Function(Function::Lambda(Lambda(
                            body.clone(),
                            env,
                            args.clone(),
                        ))))
                    }))
                }
                Some(Ast::Symbol(Symbol(quote, 0))) if **quote == *"quote" => {
                    if list.len() == 2 {
                        Ok(Box::new(move |_| Ok(list[1].clone())))
                    } else {
                        Err(format!(
                            "bad syntax {list:?}, quote requires one expression"
                        ))
                    }
                }
                Some(f) => {
                    let f = Self::analyze(f.clone())?;
                    let rest = list[1..]
                        .iter()
                        .cloned()
                        .map(Self::analyze)
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(Box::new(move |env| {
                        Self::execute_application(
                            f.clone()(env.clone())?,
                            rest.clone()
                                .into_iter()
                                .map(|a| a(env.clone()))
                                .collect::<Result<Vec<_>, _>>()?,
                        )
                    }))
                }
                None => Err(format!("bad syntax {list:?}, empty application")),
            },
            Ast::Symbol(s) => Ok(Box::new(move |env| {
                env.borrow().lookup(&s).ok_or(format!("free variable {s}"))
            })),
            _ => Ok(Box::new(move |_| Ok(expr.clone()))),
        }
    }

    fn execute_application(f: Ast, args: Vec<Ast>) -> Result<Ast, String> {
        if let Ast::Function(f) = f {
            f.apply(args)
        } else {
            Err(format!(
                "cannot not apply {f} to {args:?}, because {f} is not a function"
            ))
        }
    }
}

pub struct Reader(String);
#[derive(Debug)]
struct OwnedChars {
    string: String,
    position: usize,
}

impl Iterator for OwnedChars {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        let c = self.string[self.position..].chars().next()?;
        self.position += c.len_utf8();
        Some(c)
    }
}

trait OwnedCharsExt {
    fn chars(self) -> OwnedChars;
}
impl OwnedCharsExt for String {
    fn chars(self) -> OwnedChars {
        OwnedChars {
            string: self,
            position: 0,
        }
    }
}
trace::init_depth_var!();
type Input = Peekable<OwnedChars>;
type ReaderInnerResult = Result<(Ast, Input), (String, Input)>;
impl Reader {
    // we have empty continuations for if we run out of input, but we can recover if we get more
    // input
    pub fn read(&mut self) -> Result<Ast, String> {
        let input = <String as Clone>::clone(&self.0).chars().peekable();
        match Self::read_inner(input, &mut || None) {
            Ok((ast, rest)) => {
                self.0 = rest.collect();
                Ok(ast)
            }
            Err((reason, rest)) => {
                self.0 = rest.collect();
                Err(reason)
            }
        }
    }
    pub fn read_with_continue(
        &mut self,
        mut empty_continuation: impl FnMut() -> String,
    ) -> Result<Ast, String> {
        let input = <String as Clone>::clone(&self.0).chars().peekable();
        match Self::read_inner(input, &mut || Some(empty_continuation())) {
            Ok((ast, rest)) => {
                self.0 = rest.collect();
                Ok(ast)
            }
            Err((reason, rest)) => {
                self.0 = rest.collect();
                Err(reason)
            }
        }
    }
    // #[trace(format_enter = "", format_exit = "")]
    fn read_inner(
        input: Input,
        empty_continuation: &mut impl FnMut() -> Option<String>,
    ) -> ReaderInnerResult {
        let mut input = Self::read_whitespace_and_comments(input).1;
        match input.peek() {
            // TODO: quote
            Some('(') => Self::read_list(input, empty_continuation),
            Some(')') => {
                input.next();
                Err(("unfinished pair".to_string(), input))
            }

            Some(n) if n.is_ascii_digit() => Self::read_number(input),
            Some(_) => Self::read_symbol(input),
            None => empty_continuation()
                .ok_or((String::from("empty input"), input))
                .and_then(|input| {
                    let input = input.chars().peekable();
                    Self::read_inner(input, empty_continuation)
                }),
        }
    }

    // #[trace(format_enter = "", format_exit = "")]
    fn read_whitespace_and_comments(mut input: Input) -> (bool, Input) {
        let mut found = false;
        while let Some(c) = input.peek() {
            match c {
                ';' => {
                    found = true;
                    // we do find to skip untill we find newline, this is essentially
                    // what skip while does, but skip while returns a new type and we
                    // cannot do impl trait in type alias so this does not work for with
                    // my input type
                    input.find(|c| *c != '\n');
                }
                c if c.is_whitespace() => {
                    found = true;
                    input.next();
                }
                _ => break,
            }
        }
        (found, input)
    }

    // #[trace(format_enter = "", format_exit = "")]
    // parse symbol if not followed by space paren or comment
    // invariant Some('.') | Some(c) if c.is_ascci_digit() = input.peek()
    fn read_number(input: Input) -> ReaderInnerResult {
        let (first, mut input) = Self::read_digit(input);
        let (second, input) = {
            if input.peek().copied().filter(|c| *c == '.').is_some() {
                input.next();
                let (digits, input) = Self::read_digit(input);
                (format!(".{digits}"), input)
            } else {
                (String::new(), input)
            }
        };
        let (last, input) = Self::read_symbol_inner(input);
        match (first.as_str(), second.as_str(), last.as_str()) {
            ("", "." | "", "") => Err(("invalid syntax dangling dot".to_owned(), input)),
            (_, _, "") => match format!("{first}{second}").parse::<f64>() {
                Ok(n) => Ok((Ast::Number(n), input)),
                Err(e) => Err((e.to_string(), input)),
            },

            (first, second, _) => {
                let (last, input) = Self::read_symbol_inner(input);
                Ok((
                    Ast::Symbol(Symbol(format!("{first}{second}{last}").into(), 0)),
                    input,
                ))
            }
        }
    }
    fn read_digit(mut input: Input) -> (String, Input) {
        let mut number = String::new();
        while let Some(n) = input.peek().copied().filter(char::is_ascii_digit) {
            input.next();
            number.push(n);
        }
        (number, input)
    }
    // constraints input.next() == Some(c) if c != whitespace or comment or paren
    // #[trace(format_enter = "", format_exit = "")]
    fn read_symbol(input: Input) -> ReaderInnerResult {
        let (symbol, input) = Self::read_symbol_inner(input);
        Ok((Ast::Symbol(Symbol(symbol.into(), 0)), input))
    }

    // invariant input.next() == Some('(')
    // #[trace(format_enter = "", format_exit = "")]
    fn read_list(
        mut input: Input,
        empty_continuation: &mut impl FnMut() -> Option<String>,
    ) -> ReaderInnerResult {
        input.next();
        let mut list = vec![];
        loop {
            input = Self::read_whitespace_and_comments(input).1;
            match input.peek() {
                // TODO: dot tailed list and pair instead of list
                Some(')') => {
                    input.next();
                    break Ok((Ast::List(list), input));
                }
                Some(_) => {
                    let item: Ast;
                    (item, input) = Self::read_inner(input, empty_continuation)?;
                    list.push(item);
                }
                None => {
                    input = empty_continuation()
                        .ok_or(("unfinished list".to_string(), input))
                        .map(|input| input.chars().peekable())?;
                }
            }
        }
    }

    fn read_symbol_inner(mut input: Input) -> (String, Input) {
        let mut str = String::new();
        while let Some(char) = input.peek().cloned() {
            if char.is_whitespace() || ['(', ')', ';', '"', '\''].contains(&char) {
                break;
            }
            input.next();
            str.push(char);
        }
        (str, input)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Symbol(pub Rc<str>, pub usize);

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.0, self.1)
    }
}

impl From<Rc<str>> for Symbol {
    fn from(value: Rc<str>) -> Self {
        Self(value, 0)
    }
}
impl From<&str> for Symbol {
    fn from(value: &str) -> Self {
        Self(value.into(), 0)
    }
}



fn main() {
    let mut reader = Reader(String::new());
    let newline = || {
        let mut stdin = BufReader::new(std::io::stdin());
        let mut input = String::new();
        // flush the screen
        std::io::stdout().flush().unwrap();
        stdin.read_line(&mut input).unwrap();
        input
    };
    let mut expander = Expander::new();
    loop {
        print!("\n>> ",);

        let ast = reader
            .read_with_continue(newline)
            .inspect(|e| println!("after reader: {e}"))
            .and_then(|ast| {
                expander.expand(
                    expander.introduce(ast.datum_to_syntax(None)),
                    CompileTimeEnvoirnment::new(),
                )
            })
            .inspect(|e| println!("after expansion: {e}"))
            .and_then(|ast| expander.compile(ast))
            .inspect(|e| println!("after expansion part 2: {e}"))
            .and_then(|ast| expander.eval_compiled(ast));
        match ast {
            Ok(expr) => println!("{expr}"),
            Err(e) => println!("{e}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::scope::AdjustScope;
    use crate::Scope;
    use std::collections::BTreeSet;

    use crate::{Ast, Binding, Expander, Symbol, Syntax, UniqueNumberManager};

    #[test]
    fn identifier_test_with_empty_syntax() {
        assert!(Ast::Syntax(Syntax::new("a".into())).identifier());
    }

    #[test]
    fn datum_to_syntax_with_identifier() {
        assert_eq!(
            Ast::Symbol(Symbol("a".into(), 0)).datum_to_syntax(None),
            Ast::Syntax(Syntax("a".into(), BTreeSet::new()))
        );
    }

    #[test]
    fn datum_to_syntax_with_number() {
        assert_eq!(Ast::Number(1.0).datum_to_syntax(None), Ast::Number(1.0));
    }

    #[test]
    fn datum_to_syntax_with_list() {
        assert_eq!(
            Ast::List(vec![
                Ast::Symbol(Symbol("a".into(), 0)),
                Ast::Symbol(Symbol("b".into(), 0)),
                Ast::Symbol(Symbol("c".into(), 0)),
            ])
            .datum_to_syntax(None),
            Ast::List(vec![
                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("b".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
            ])
        );
    }

    #[test]
    fn datum_to_syntax_with_list_and_syntax() {
        assert_eq!(
            Ast::List(vec![
                Ast::Symbol(Symbol("a".into(), 0)),
                Ast::Syntax(Syntax("b".into(), BTreeSet::from([Scope(0), Scope(1)]))),
                Ast::Symbol(Symbol("c".into(), 0)),
            ])
            .datum_to_syntax(None),
            Ast::List(vec![
                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("b".into(), BTreeSet::from([Scope(0), Scope(1)]))),
                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
            ])
        );
    }
    #[test]
    fn syntax_to_datum_with_identifier() {
        assert_eq!(
            Ast::Syntax(Syntax("a".into(), BTreeSet::new())).syntax_to_datum(),
            Ast::Symbol(Symbol("a".into(), 0)),
        );
    }

    #[test]
    fn syntax_to_datum_with_number() {
        assert_eq!(Ast::Number(1.0).syntax_to_datum(), Ast::Number(1.0));
    }

    #[test]
    fn syntax_to_datum_with_list() {
        assert_eq!(
            Ast::List(vec![
                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("b".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
            ])
            .syntax_to_datum(),
            Ast::List(vec![
                Ast::Symbol(Symbol("a".into(), 0)),
                Ast::Symbol(Symbol("b".into(), 0)),
                Ast::Symbol(Symbol("c".into(), 0)),
            ])
        );
    }

    #[test]
    fn scope_equality_test() {
        let mut scope_creator = UniqueNumberManager::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_ne!(sc1, sc2);
        assert_eq!(sc2, sc2);
    }

    #[test]
    fn add_scope_test_empty_scope() {
        let mut scope_creator = UniqueNumberManager::new();
        let sc1 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), BTreeSet::new())).add_scope(sc1),
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1])))
        );
    }

    #[test]
    fn add_scope_test_empty_scope_list() {
        let mut scope_creator = UniqueNumberManager::new();
        let sc1 = scope_creator.new_scope();
        assert_eq!(
            Ast::List(vec![
                Ast::Symbol(Symbol("x".into(), 0)),
                Ast::Symbol(Symbol("y".into(), 0)),
            ])
            .datum_to_syntax(None)
            .add_scope(sc1),
            Ast::List(vec![
                Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))),
                Ast::Syntax(Syntax("y".into(), BTreeSet::from([sc1]))),
            ])
        );
    }

    #[test]
    fn add_scope_test_non_empty_scope() {
        let mut scope_creator = UniqueNumberManager::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).add_scope(sc2),
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2])))
        );
    }

    #[test]
    fn add_scope_test_add_duplicate() {
        let mut scope_creator = UniqueNumberManager::new();
        let sc1 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).add_scope(sc1),
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1,])))
        );
    }

    #[test]
    fn flip_scope_test_different() {
        let mut scope_creator = UniqueNumberManager::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).flip_scope(sc2),
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2])))
        );
    }

    #[test]
    fn flip_scope_test_same() {
        let mut scope_creator = UniqueNumberManager::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2]))).flip_scope(sc2),
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1,])))
        );
    }

    #[test]
    fn resolve_test_lambda_empty() {
        let expander = Expander::new();

        assert_eq!(
            expander.resolve(&Syntax("lambda".into(), BTreeSet::new())),
            Err("free variable lambda".to_string())
        );
    }

    #[test]
    fn resolve_test_lambda_core() {
        let expander = Expander::new();

        println!("{expander:?}");
        assert_eq!(
            expander.resolve(&expander.introduce(Syntax("lambda".into(), BTreeSet::new()))),
            Ok(&Binding::Lambda)
        );
    }
}
