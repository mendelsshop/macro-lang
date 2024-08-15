#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![deny(static_mut_refs)]
#![deny(clippy::use_self, rust_2018_idioms, clippy::missing_panics_doc)]
use std::io::{BufRead, BufReader, Write};

use ast::{ Ast, Function,  Symbol};
use evaluator::{Env, EnvRef, Evaluator};
use expander::CompileTimeEnvoirnment;

trace::init_depth_var!();

mod ast;
mod evaluator;
mod expander;
mod reader;
use binding::{Binding, CompileTimeBinding, CoreForm};
use scope::{AdjustScope, Scope};
use std::{
    collections::{BTreeSet, HashMap},
    rc::Rc,
};
use syntax::Syntax;

mod binding;
mod compile;
mod core;
mod expand;
mod r#match;
mod scope;
mod syntax;

// use trace::trace;
// #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
// struct Scope(usize);
#[derive(Debug)]
struct UniqueNumberManager(usize);

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

impl Ast {
    // pub fn list_with_length(self, length: usize) -> Result<Vec<Ast>, Ast> {
    //     match self {
    //         Self::List(l) if l.len() == length => Ok(l),
    //         _ => Err(self),
    //     }
    // }

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
    core_forms: HashMap<Rc<str>, CoreForm>,
    core_primitives: HashMap<Rc<str>, Function>,
    core_scope: Scope,
    scope_creator: UniqueNumberManager,
    all_bindings: HashMap<Syntax<Symbol>, Binding>,
    env: EnvRef,
    core_syntax: Syntax<Ast>,
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
            Binding::CoreBinding("datum->syntax".into()),
            Binding::CoreBinding("syntax->datum".into()),
            Binding::CoreBinding("list".into()),
            Binding::CoreBinding("cons".into()),
            Binding::CoreBinding("car".into()),
            Binding::CoreBinding("cdr".into()),
            Binding::CoreBinding("map".into()),
        ]);
        let mut this = Self {
            core_syntax: Syntax(Ast::Boolean(false), BTreeSet::from([core_scope])),
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









fn main() {
    let mut reader = reader::Reader::new();
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
                    expander.namespace_syntax_introduce(ast.datum_to_syntax(None)),
                    expander.introduce(ast.datum_to_syntax(None)),
                    CompileTimeEnvoirnment::new()
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
