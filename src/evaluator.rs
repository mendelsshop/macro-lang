use crate::{
    ast::{Ast, Function, Lambda, Pair, Symbol }, DEPTH
};

use trace::trace;

use std::{cell::RefCell, collections::HashMap, rc::Rc};

#[derive(Clone, PartialEq, Debug)]
pub struct Env {
    scope: HashMap<Symbol, Ast>,
    parent: Option<EnvRef>,
}

impl Env {
    pub fn new_env() -> Rc<RefCell<Self>> {
        let env = Self::new();
        env.borrow_mut().define(
            Symbol("datum->syntax".into(), 0),
            Ast::Function(Function::Primitive(move |e| {
                let Ast::Pair(e) = e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };
                let Pair(e, Ast::TheEmptyList) = *e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };
                Ok(e.datum_to_syntax(None))
            })),
        );
        env.borrow_mut().define(
            Symbol("syntax->datum".into(), 0),
            Ast::Function(Function::Primitive(move |e| {
                let Ast::Pair(e) = e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };
                let Pair(e, Ast::TheEmptyList) = *e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };
                Ok(e.syntax_to_datum())
            })),
        );
        env.borrow_mut().define(
            Symbol("syntax-e".into(), 0),
            Ast::Function(Function::Primitive(move |e| {
                let Ast::Pair(e) = e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };
                let Pair(Ast::Syntax(e), Ast::TheEmptyList) = *e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };
                Ok(e.0)
            })),
        );
        env.borrow_mut().define(
            Symbol("cons".into(), 0),
            Ast::Function(Function::Primitive(move |e| {
                let Ast::Pair(e) = e else {
                    Err(format!(
                        "arity error: expected 2 argument, got {}",
                        e.size()
                    ))?
                };
                let Pair(ref fst, Ast::Pair(ref last)) = *e else {
                    Err(format!(
                        "arity error: expected 2 argument, got {}",
                        e.size()
                    ))?
                };
                let Pair(ref snd, Ast::TheEmptyList) = **last else {
                    Err(format!(
                        "arity error: expected 2 argument, got {}",
                        e.size()
                    ))?
                };
                Ok(Ast::Pair(Box::new(Pair(fst.clone(), snd.clone()))))
            })),
        );
        env.borrow_mut().define(
            Symbol("car".into(), 0),
            Ast::Function(Function::Primitive(move |e| {
                let Ast::Pair(e) = e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };

                let Pair(Ast::Pair(e), Ast::TheEmptyList) = *e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };
                let Pair(fst, _) = *e;
                Ok(fst)
            })),
        );
        env.borrow_mut().define(
            Symbol("cdr".into(), 0),
            Ast::Function(Function::Primitive(move |e| {
                //println!("cdr {e}");
                let Ast::Pair(e) = e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };
                let Pair(Ast::Pair(e), Ast::TheEmptyList) = *e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };
                let Pair(_, snd) = *e;
                Ok(snd)
            })),
        );
        env.borrow_mut().define(
            Symbol("list".into(), 0),
            Ast::Function(Function::Primitive(Ok)),
        );
        env.borrow_mut().define(
            Symbol("map".into(), 0),
            Ast::Function(Function::Primitive(move |e| {
                let Ast::Pair(e) = e else {
                    Err(format!(
                        "arity error: expected 1 argument, got {}",
                        e.size()
                    ))?
                };

                let Pair(Ast::Function(ref f), Ast::Pair(ref last)) = *e else {
                    Err(format!(
                        "arity error: expected 2 argument, got {}",
                        e.size()
                    ))?
                };
                let Pair(ref l, Ast::TheEmptyList) = **last else {
                    Err(format!(
                        "arity error: expected 2 argument, got {}",
                        e.size()
                    ))?
                };
                l.map(|a| f.apply(Ast::Pair(Box::new(Pair(a, Ast::TheEmptyList)))))
            })),
        );
        env
    }
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

    pub fn extend_envoirnment(env: EnvRef, params: Ast, args: Ast) -> Result<EnvRef, String> {
        let new_envoirnment = Self::new_scope(env);
        fn extend_envoirnment(env: Rc<RefCell<Env>>, params: Ast, args: Ast) -> Result<(), String> {
            match (params, args) {
                (Ast::Pair(param), Ast::Pair(arg)) => {
                    let Ast::Symbol(p) = param.0 else {
                        return Err(format!(
                            "{} is not a symbol (cannot be function arguement)",
                            param.1
                        ));
                    };
                    env.borrow_mut().define(p, arg.0);
                    extend_envoirnment(env, param.1, arg.1)
                }
                (Ast::Symbol(s), rest) => {
                    env.borrow_mut().define(s, rest);
                    Ok(())
                }
                (Ast::TheEmptyList, Ast::TheEmptyList) => Ok(()),
                (Ast::TheEmptyList, rest) => Err(format!(
                    "arity mismatch these arguments do not have any coresponding parameters {rest}"
                )),
                (rest, Ast::TheEmptyList) => Err(format!(
                    "arity mismatch these parameters do not have any coresponding aruments {rest}"
                )),
                (arg, _) => Err(format!("bad argument expected symbol found: {arg}")),
            }
        }
        extend_envoirnment(new_envoirnment.clone(), params, args).map(|()| new_envoirnment)
    }

    pub(crate) fn new() -> EnvRef {
        let scope = HashMap::new();
        // TODO: primitive environment
        let parent = None;
        Rc::new(RefCell::new(Self { scope, parent }))
    }
}
pub type EnvRef = Rc<RefCell<Env>>;

pub struct Evaluator {}

impl Evaluator {
    #[trace]
    pub(crate) fn eval(expr: Ast, env: EnvRef) -> Result<Ast, String> {
        //println!("eval {expr}");
        match expr {
            Ast::Pair(list) => match list.0 {
                Ast::Symbol(Symbol(ref lambda, 0)) if **lambda == *"lambda" => {
                    let Pair(ref lambda_id, Ast::Pair(ref inner)) = *list else {
                        Err(format!("invalid syntax {list:?} bad lambda"))?
                    };
                    let Pair(ref arg, Ast::Pair(ref body)) = **inner else {
                        Err(format!("invalid syntax {list:?}, bad argument for lambda"))?
                    };

                    // TODO: variadic function with dot notation
                    let args = arg.clone().map_pair(|arg, base| match arg {
                        Ast::Symbol(s) => Ok(Ast::Symbol(s)),
                        Ast::TheEmptyList if base => Ok(Ast::TheEmptyList),
                        _ => Err(format!("bad syntax {arg} is not a valid paramter")),
                    })?;
                    Ok(Ast::Function(Function::Lambda(Lambda(
                        Box::new(Ast::Pair(body.clone())),
                        env,
                        Box::new(args),
                    ))))
                }
                Ast::Symbol(Symbol(quote, 0)) if *quote == *"quote" => {
                    let Pair(_, Ast::Pair(datum)) = *list else {
                        Err("bad syntax, quote requires one expression")?
                    };
                    let Pair(datum, Ast::TheEmptyList) = *datum else {
                        Err("bad syntax, quote requires one expression")?
                    };
                    Ok(datum)
                }
                f => {
                    let f = Self::eval(f, env.clone())?;
                    let rest = list.1.map(|arg| Self::eval(arg, env.clone()))?;
                    Self::execute_application(f, rest)
                } //Ast::TheEmptyList => Err(format!("bad syntax {list:?}, empty application")),
            },
            Ast::Symbol(s) =>
            //println!("variable {s})");
            {
                env.borrow().lookup(&s).ok_or(format!("free variable {s}"))
            }
            //.inspect(|x|println!("variable {x}"))
            ,
            _ => Ok(expr.clone()),
        }
    }

    pub(crate) fn execute_application(f: Ast, args: Ast) -> Result<Ast, String> {
        if let Ast::Function(f) = f {
            f.apply(args)
            //.inspect(|x|println!("application {x}"))
        } else {
            Err(format!(
                "cannot not apply {f} to {args:?}, because {f} is not a function"
            ))
        }
    }

    pub(crate) fn eval_sequence(body: Ast, env: Rc<RefCell<Env>>) -> Result<Ast, String> {
        let Ast::Pair(pair) = body else {
            return Err(format!("not a sequence {body}"));
        };
        if pair.1 == Ast::TheEmptyList {
            Self::eval(pair.0, env)
        } else {
            Self::eval(pair.0, env.clone())?;
            Self::eval_sequence(pair.1, env)
        }
    }
}
