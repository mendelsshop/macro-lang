use crate::{
    ast::{Ast, Function, Lambda, Pair, Symbol},
    primitives::new_primitive_env,
};

use itertools::Itertools;

use std::{cell::RefCell, collections::HashMap, fmt, rc::Rc};

#[derive(Clone, PartialEq, Debug)]
pub struct Env {
    scope: HashMap<Symbol, Ast>,
    parent: Option<EnvRef>,
}

impl Env {
    pub fn new_env() -> Rc<RefCell<Self>> {
        let env = Self::new();
        new_primitive_env(|name, primitive| {
            env.borrow_mut().define(name.into(), primitive);
        });
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
    fn define_values(
        &mut self,
        symbols: impl IntoIterator<Item = Symbol>,
        values: impl IntoIterator<Item = Ast>,
    ) {
        self.scope.extend(symbols.into_iter().zip(values));
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
        extend_envoirnment(new_envoirnment.clone(), params.clone(), args.clone())
            .map(|()| new_envoirnment)
            .map_err(|e| format!("{e} {params} {args}"))
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

#[derive(Debug)]
pub enum Values {
    Many(Vec<Ast>),
    Single(Ast),
}

impl PartialEq for Values {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Many(l0), Self::Many(r0)) => l0 == r0,
            (Self::Single(l0), Self::Single(r0)) => l0 == r0,
            (Self::Single(l0), Self::Many(r0)) if r0.len() == 1 => {
                r0.first().is_some_and(|r0| r0 == l0)
            }
            (Self::Many(l0), Self::Single(r0)) if l0.len() == 1 => {
                l0.first().is_some_and(|l0| l0 == r0)
            }
            _ => false,
        }
    }
}
impl Values {
    pub fn into_single(self) -> Result<Ast, Vec<Ast>> {
        match self {
            Self::Many(mut vec) if vec.len() == 1 => {
                let ast = vec.remove(0);
                Ok(ast)
            }
            Self::Many(vec) => Err(vec),
            Self::Single(ast) => Ok(ast),
        }
    }
}

impl fmt::Display for Values {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Many(vec) => write!(
                f,
                "{}",
                vec.iter().map(ToString::to_string).collect_vec().join("\n")
            ),
            Self::Single(ast) => write!(f, "{ast}"),
        }
    }
}
impl Evaluator {
    pub(crate) fn eval_single_value(expr: Ast, env: EnvRef) -> Result<Ast, String> {
        Self::eval(expr, env).and_then(|values| {
            values
                .into_single()
                .map_err(|_| "arity error expected one value".to_string())
        })
    }
    pub(crate) fn eval(expr: Ast, env: EnvRef) -> Result<Values, String> {
        match expr {
            Ast::Pair(list) => match list.0 {
                Ast::Symbol(Symbol(ref lambda)) if **lambda == *"lambda" => {
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
                    Ok(Values::Single(Ast::Function(Function::Lambda(Lambda(
                        Box::new(Ast::Pair(body.clone())),
                        env,
                        Box::new(args),
                    )))))
                }
                Ast::Symbol(Symbol(quote)) if *quote == *"quote" => {
                    let Pair(_, Ast::Pair(datum)) = *list else {
                        Err("bad syntax, quote requires one expression")?
                    };
                    let Pair(datum, Ast::TheEmptyList) = *datum else {
                        Err("bad syntax, quote requires one expression")?
                    };
                    Ok(Values::Single(datum))
                }
                Ast::Symbol(Symbol(begin)) if *begin == *"begin" => {
                    Self::eval_sequence(list.1, env)
                }
                Ast::Symbol(Symbol(begin)) if *begin == *"begin0" => {
                    let vec = list.1.to_list_checked()?;
                    if vec.is_empty() {
                        return Err("expected at least one expression in begin".to_string());
                    }
                    let mut results: Vec<Values> = vec
                        .into_iter()
                        .map(|e| Self::eval(e, Rc::clone(&env)))
                        .try_collect()?;
                    Ok(results.remove(0))
                }
                Ast::Symbol(Symbol(expression)) if *expression == *"#%expression" => {
                    let Pair(_, Ast::Pair(datum)) = *list else {
                        Err("bad syntax, #%expression requires one expression")?
                    };
                    let Pair(datum, Ast::TheEmptyList) = *datum else {
                        Err("bad syntax, #%expression requires one expression")?
                    };
                    Self::eval(datum, env)
                }
                Ast::Symbol(Symbol(letrec_values)) if &*letrec_values == "letrec-values" => {
                    let (values, bodies) = Self::check_let(&letrec_values, list.1)?;
                    let env = Env::new_scope(env);
                    values.into_iter().try_for_each(|(mut ids, value)| {
                        let value = Self::eval(value, Rc::clone(&env))?;
                        match value {
                            Values::Many(vec) if vec.len() == ids.len() => {
                                env.borrow_mut().define_values(ids, vec);
                                Ok(())
                            },
                            Values::Single(ast) if ids.len() == 1 => {
                                env.borrow_mut().define(ids.remove(0), ast);
                                Ok(())
                            },
                            _ => Err("let-values error: number of values is not the same as the number of ids".to_string()),
                        }
                    })?;
                    Self::eval(bodies, env)
                }
                Ast::Symbol(Symbol(let_values)) if &*let_values == "let-values" => {
                    let (values, bodies) = Self::check_let(&let_values, list.1)?;
                    let values = values.into_iter().map(|(mut ids, value)| {
                        let value = Self::eval(value, Rc::clone(&env))?;
                        match value {
                            Values::Many(vec) if vec.len() == ids.len() => {
                                Ok(ids.into_iter().zip(vec).collect_vec())
                            },
                            Values::Single(ast) if ids.len() == 1 => Ok(vec![(ids.remove(0), ast)]),
                            _ => Err("let-values error: number of values is not the same as the number of ids".to_string()),
                        }
                    }).try_collect::<_, Vec<_>, _>()?.concat();
                    let env = Rc::new(RefCell::new(Env {
                        scope: HashMap::from_iter(values),
                        parent: Some(env),
                    }));
                    Self::eval(bodies, env)
                }
                f => {
                    let f: Ast = Self::eval_single_value(f, env.clone())?;
                    let rest = list
                        .1
                        .map(|arg| Self::eval_single_value(arg, env.clone()))?;
                    Self::execute_application(f, rest)
                } //Ast::TheEmptyList => Err(format!("bad syntax {list:?}, empty application")),
            },
            Ast::Symbol(s) => env
                .borrow()
                .lookup(&s)
                .map(Values::Single)
                .ok_or(format!("free variable {s} eval")),
            _ => Ok(Values::Single(expr.clone())),
        }
    }

    pub(crate) fn execute_application(f: Ast, args: Ast) -> Result<Values, String> {
        if let Ast::Function(f) = f {
            f.apply(args)
        } else {
            Err(format!(
                "cannot not apply {f} to {args:?}, because {f} is not a function"
            ))
        }
    }

    pub(crate) fn eval_sequence(body: Ast, env: Rc<RefCell<Env>>) -> Result<Values, String> {
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
    pub fn to_id_list(ids: Ast) -> Result<Vec<Symbol>, String> {
        let ids = ids.to_list_checked()?;
        let ids = ids
            .into_iter()
            .map(std::convert::TryInto::try_into)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ids)
    }
    fn check_let(letrec_values: &str, list: Ast) -> Result<(Vec<(Vec<Symbol>, Ast)>, Ast), String> {
        let Ast::Pair(pair) = list else {
            return Err(format!("error {letrec_values}: expected key values pairs"));
        };
        let values = pair.0;
        let values: Vec<(Vec<Symbol>, Ast)> = values
            .to_list_checked()?
            .into_iter()
            .map(|value| {
                let Ast::Pair(value) = value else {
                    return Err(format!(
                        "error {letrec_values}: expected [(ids) value], got {value}"
                    ));
                };
                let ids = Self::to_id_list(value.0)?;
                let Ast::Pair(value) = value.1 else {
                    return Err(format!(
                        "error {letrec_values}: expected [(ids) value], missing value {}",
                        value.1
                    ));
                };
                if value.1 != Ast::TheEmptyList {
                    return Err(format!(
                        "error {letrec_values}: expected [(ids) value], it is unclosed, got {}",
                        value.1
                    ));
                };
                Ok((ids, value.0))
            })
            .try_collect()?;
        let Ast::Pair(pair) = pair.1 else {
            return Err(format!("error {letrec_values}: expected body"));
        };
        let body = pair.0;
        if pair.1 != Ast::TheEmptyList {
            return Err(format!("error {letrec_values}: unclosed body"));
        }
        Ok((values, body))
    }
}
