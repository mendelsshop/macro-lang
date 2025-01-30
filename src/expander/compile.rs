use std::{mem, rc::Rc};

use crate::{
    ast::{syntax::Syntax, Ast, Pair, Symbol},
    evaluator::{Evaluator, Values},
    list, sexpr,
};

use super::{
    binding::Binding,
    namespace::NameSpace,
    phase::{self, Phase},
    r#match::match_syntax,
    Expander,
};

impl Expander {
    pub fn compile(&self, s: Ast, ns: &NameSpace, phase: Phase) -> Result<Ast, String> {
        let compile = |s| self.compile(s, ns);
        let Ast::Syntax(syntax) = s.clone() else {
            panic!()
        };
        match syntax.0 {
            Ast::Pair(_) => {
                let core_sym = self
                    .core_form_symbol(s.clone())
                    .map_err(|_| format!("not a core form {s}"))?;
                match core_sym.to_string().as_str() {
                    "lambda" => {
                        let m = match_syntax(
                            s,
                            list!("lambda".into(), "formals".into(), "body".into()),
                        )?;
                        self.compile_lambda(
                            m("formals".into()).ok_or("internal error")?,
                            m("body".into()).ok_or("internal error")?,
                            ns,
                        )
                        .map(|body| list!("lambda".into(); body))
                    }
                    "case-lambda" => {
                        let m = match_syntax(s, sexpr!(("case-lambda" [formals body] "...")))?;
                        Ast::map2(
                            m("formals".into()).ok_or("internal error")?,
                            m("body".into()).ok_or("internal error")?,
                            |formals, body| self.compile_lambda(formals, body, ns),
                        )
                        .map(|cases| sexpr!(("case-lambda". #(cases))))
                    }
                    "#%app" => {
                        let m = match_syntax(s, sexpr!(("#%app".rest)))?;
                        m("rest".into()).ok_or("internal error")?.map(compile)
                    }
                    "if" => {
                        let m = match_syntax(
                            s,
                            list!("if".into(), "test".into(), "then".into(), "else".into()),
                        )?;
                        Ok(list!(
                            "if".into(),
                            m("test".into())
                                .ok_or("internal error".to_string())
                                .and_then(compile)?,
                            m("then".into())
                                .ok_or("internal error".to_string())
                                .and_then(compile)?,
                            m("else".into())
                                .ok_or("internal error".to_string())
                                .and_then(compile)?,
                        ))
                    }

                    "with-continuation-mark" => {
                        let m = match_syntax(
                            s,
                            // TODO: should this match with-continuation-mark as opposed to if?
                            list!("if".into(), "key".into(), "val".into(), "body".into()),
                        )?;
                        Ok(list!(
                            "with-continuation-mark".into(),
                            m("key".into())
                                .ok_or("internal error".to_string())
                                .and_then(compile)?,
                            m("val".into())
                                .ok_or("internal error".to_string())
                                .and_then(compile)?,
                            m("body".into())
                                .ok_or("internal error".to_string())
                                .and_then(compile)?,
                        ))
                    }
                    // maybe begin0 is if its gen-symed (at a sybmol level)
                    "begin" | "begin0" => {
                        let m = match_syntax(s, list!("begin".into(), "e".into(), "...+".into()))?;
                        m("e".into())
                            .ok_or("internal error")?
                            .map(compile)
                            .map(|e| list!(Ast::Symbol(core_sym.into()); e ))
                    }
                    "set!" => {
                        let m = match_syntax(s, list!("set!".into(), "id".into(), "value".into()))?;
                        Ok(list!(
                            "set!".into(),
                            m("id".into())
                                .ok_or("internal error".to_string())
                                .and_then(compile)?,
                            m("value".into())
                                .ok_or("internal error".to_string())
                                .and_then(compile)?,
                        ))
                    }
                    "let-values" | "letrec-values" => self.compile_let(core_sym, s, ns),
                    "quote" => {
                        let m = match_syntax(s, list!("quote".into(), "datum".into()))?;
                        m("datum".into())
                            .ok_or("internal error".to_string())
                            .map(Ast::syntax_to_datum)
                            .map(|datum| list!("quote".into(), datum))
                    }
                    "quote-syntax" => {
                        let m = match_syntax(s, list!("quote-syntax".into(), "datum".into()))?;
                        m("datum".into())
                            .ok_or("internal error".to_string())
                            .map(|datum| list!("quote".into(), datum))
                    }
                    _ => Err(format!("unrecognized core form {core_sym}")),
                }
            }
            Ast::Symbol(ref s1) => {
                let with = syntax.with_ref(s1.clone());
                let b = self.resolve(&with, false).inspect_err(|e| {
                    dbg!(format!("{e}"));
                })?;
                match b {
                    Binding::Local(b) => Ok(Ast::Symbol(key_to_symbol(b))),
                    Binding::Module(s) => ns
                        .variables
                        .get(&s.clone().into())
                        .ok_or(format!("missing core bindig for primitive {s}"))
                        .cloned(),
                }
            }
            _ => Err(format!("bad syntax after expansion {s} compile")),
        }
    }
    fn loop_formals(&self, formals: Ast) -> Result<Ast, String> {
        match formals {
            Ast::Syntax(mut s) => {
                let mut a = Ast::TheEmptyList;
                mem::swap(&mut s.0, &mut a);
                match a {
                    Ast::Symbol(sym) => self.local_symbol(&s.with(sym)).map(Ast::Symbol),
                    a @ (Ast::Pair(_) | Ast::TheEmptyList) => self.loop_formals(a),
                    formals => Err(format!("bad parameter: {formals}")),
                }
            }
            Ast::Pair(p) => Ok(Ast::Pair(Box::new(Pair(
                self.loop_formals(p.0)?,
                self.loop_formals(p.1)?,
            )))),
            Ast::TheEmptyList => Ok(Ast::TheEmptyList),
            _ => Err(format!("bad parameter: {formals}")),
        }
    }
    fn compile_lambda(&self, formals: Ast, body: Ast, ns: &NameSpace) -> Result<Ast, String> {
        Ok(list!(self.loop_formals(formals)?, self.compile(body, ns)?))
    }

    fn compile_let(&self, core_sym: Rc<str>, s: Ast, ns: &NameSpace) -> Result<Ast, String> {
        let rec = &*core_sym == "letrec-values";
        let m = match_syntax(
            s,
            list!(
                "let-values".into(),
                list!(
                    list!(list!("id".into(), "...".into()), "rhs".into()),
                    "...".into()
                ),
                "body".into()
            ),
        )?;
        let idss = m("id".into()).ok_or("internal error")?;
        Ast::map2(
            idss,
            m("rhs".into()).ok_or("internal error")?,
            |ids, rhs| {
                ids.map(|id| self.local_symbol(&id.try_into()?).map(Ast::Symbol))
                    .and_then(|ids| self.compile(rhs.clone(), ns).map(|rhs| list!(ids, rhs)))
            },
        )
        .and_then(|signature| {
            m("body".into())
                .ok_or("internal error".to_string())
                .and_then(|body| self.compile(body, ns))
                .map(|body| list!(Ast::Symbol(core_sym.into()), signature, body))
        })
    }
    fn local_symbol(&self, id: &Syntax<Symbol>) -> Result<Symbol, String> {
        let b = self.resolve(id, false).inspect_err(|e| {
            dbg!(format!("{e}"));
        })?;
        let Binding::Local(s) = b else {
            return Err(format!("bad binding {b}"));
        };
        Ok(key_to_symbol(s))
    }

    pub fn expand_time_eval(&self, compiled: Ast) -> Result<Values, String> {
        Evaluator::eval(compiled, self.expand_time_env.clone())
    }
    pub fn run_time_eval(&self, compiled: Ast) -> Result<Values, String> {
        Evaluator::eval(compiled, self.run_time_env.clone())
    }
    pub fn expand_time_eval_single(&self, compiled: Ast) -> Result<Ast, String> {
        Evaluator::eval_single_value(compiled, self.expand_time_env.clone())
    }
    pub fn run_time_eval_single(&self, compiled: Ast) -> Result<Ast, String> {
        Evaluator::eval_single_value(compiled, self.run_time_env.clone())
    }
}

const fn key_to_symbol(key: Symbol) -> Symbol {
    key
}
