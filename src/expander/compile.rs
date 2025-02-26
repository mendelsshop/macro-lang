use std::{mem, rc::Rc};

use crate::{
    ast::{syntax::Syntax, Ast, Pair, Symbol},
    evaluator::{Evaluator, Values},
    list, sexpr,
};

use super::{
    binding::Binding,
    module_path::ResolvedModulePath,
    namespace::NameSpace,
    phase::{self, Phase},
    r#match::match_syntax,
    Expander,
};

impl Expander {
    pub fn compile(
        &self,
        s: Ast,
        ns: &NameSpace,
        phase: Phase,
        self_name: Option<ResolvedModulePath>,
    ) -> Result<Ast, String> {
        let compile = |s| self.compile(s, ns, phase, self_name.clone());
        let Ast::Syntax(syntax) = s.clone() else {
            panic!()
        };
        match syntax.0 {
            Ast::Pair(_) => {
                let core_sym = Expander::core_form_symbol(s.clone(), phase)
                    .map_err(|_| format!("not a core form {s}"))?;
                match core_sym.to_string().as_str() {
                    "module" | "module*" => self.compile_module(s, ns, self_name),
                    "#%require" => todo!(),
                    "lambda" => {
                        let m = match_syntax(
                            s,
                            list!("lambda".into(), "formals".into(), "body".into()),
                        )?;
                        self.compile_lambda(
                            m("formals".into()).ok_or("internal error")?,
                            m("body".into()).ok_or("internal error")?,
                            ns,
                            phase,
                            self_name,
                        )
                        .map(|body| list!("lambda".into(); body))
                    }
                    "case-lambda" => {
                        let m = match_syntax(s, sexpr!(("case-lambda" [formals body] "...")))?;
                        Ast::map2(
                            m("formals".into()).ok_or("internal error")?,
                            m("body".into()).ok_or("internal error")?,
                            |formals, body| {
                                self.compile_lambda(formals, body, ns, phase, self_name.clone())
                            },
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
                    "let-values" | "letrec-values" => {
                        self.compile_let(core_sym, s, ns, phase, self_name)
                    }
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
                            .map(|datum| sexpr!((quote #(datum)))).map(|q|
                                match self_name {
                                    Some(_) => sexpr!(("syntax-shift-phase-level" #(q) #(Ast::Symbol(self.phase_shift_id.clone())))),
                                    None => q,
                                })
                    }
                    _ => Err(format!("unrecognized core form {core_sym}")),
                }
            }
            Ast::Symbol(ref s1) => {
                let with = syntax.with_ref(s1.clone());
                let b = Expander::resolve(&with, phase, false)?;
                match b {
                    Binding::Local(b) => Ok(Ast::Symbol(key_to_symbol(b))),
                    Binding::Module(b) => {
                        let module_name = b.from_module;
                        match module_name {
                            ResolvedModulePath::Symbol(ref s) if &*s.0 == "#%core" => {
                                let module_namespace = ns
                                    .namespace_to_module_namespace(&module_name, phase, false)
                                    .map_err(|e| e.unwrap_or(format!("no module found")))?;
                                module_namespace.namespace_module_instantiate(
                                    &ResolvedModulePath::Symbol("#%core".into()),
                                    b.from_phase,
                                    Phase::Normal(0),
                                )?;
                                module_namespace
                                    .namespace_get_variable(b.from_phase, &b.from_symbol)
                                    .ok_or(format!(
                                        "internal error: bad #%core reference: {phase} {} {}",
                                        b.from_symbol, b.from_phase
                                    ))
                            }
                            _ if Some(module_name) == self_name => Ok(Ast::Symbol(b.from_symbol)),
                            _ => Ok(sexpr!(
                                ("namespace-get-variable"
                                    ("namespace->module-namespace"
                                        #(self_name.map_or(todo!("runtime namespace repr {ns:?}"),
                                            |_| Ast::Symbol(self.namespace_id.clone())))
                                        (quote #(module_name.into()))
                                        #({
                                            let phase = phase - b.from_phase;
                                            self_name.map_or(sexpr!(("+"  #(Ast::Symbol(self.phase_shift_id.clone())) #(todo!("runtime phase repr {phase}")))),
                                            |_| Ast::Symbol(self.namespace_id.clone()))
                                        }))
                                        #(todo!("runtime phase repr {}", b.from_phase))
                                        (quote #(Ast::Symbol(b.from_symbol)))
                                        #(todo!("failure handler"))))),
                        }
                        //ns.variables
                        //    .get(&b.clone().into())
                        //    .ok_or(format!("missing core bindig for primitive {b}"))
                        //    .cloned()
                    }
                }
            }
            _ => Err(format!("bad syntax after expansion {s} compile")),
        }
    }
    fn compile_module(
        &self,
        s: Ast,
        ns: &NameSpace,
        self_name: Option<ResolvedModulePath>,
    ) -> Result<Ast, String> {
        todo!()
    }
    fn loop_formals(&self, formals: Ast, phase: Phase) -> Result<Ast, String> {
        match formals {
            Ast::Syntax(mut s) => {
                let mut a = Ast::TheEmptyList;
                mem::swap(&mut s.0, &mut a);
                match a {
                    Ast::Symbol(sym) => self.local_symbol(&s.with(sym), phase).map(Ast::Symbol),
                    a @ (Ast::Pair(_) | Ast::TheEmptyList) => self.loop_formals(a, phase),
                    formals => Err(format!("bad parameter: {formals}")),
                }
            }
            Ast::Pair(p) => Ok(Ast::Pair(Box::new(Pair(
                self.loop_formals(p.0, phase)?,
                self.loop_formals(p.1, phase)?,
            )))),
            Ast::TheEmptyList => Ok(Ast::TheEmptyList),
            _ => Err(format!("bad parameter: {formals}")),
        }
    }

    fn compile_lambda(
        &self,
        formals: Ast,
        body: Ast,
        ns: &NameSpace,
        phase: Phase,
        self_name: Option<ResolvedModulePath>,
    ) -> Result<Ast, String> {
        Ok(list!(
            self.loop_formals(formals, phase)?,
            self.compile(body, ns, phase, self_name)?
        ))
    }

    fn compile_let(
        &self,
        core_sym: Symbol,
        s: Ast,
        ns: &NameSpace,
        phase: Phase,
        self_name: Option<ResolvedModulePath>,
    ) -> Result<Ast, String> {
        let rec = &*core_sym.0 == "letrec-values";
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
                ids.map(|id| self.local_symbol(&id.try_into()?, phase).map(Ast::Symbol))
                    .and_then(|ids| {
                        self.compile(rhs.clone(), ns, phase, self_name.clone())
                            .map(|rhs| list!(ids, rhs))
                    })
            },
        )
        .and_then(|signature| {
            m("body".into())
                .ok_or("internal error".to_string())
                .and_then(|body| self.compile(body, ns, phase, self_name))
                .map(|body| list!(Ast::Symbol(core_sym.into()), signature, body))
        })
    }
    fn local_symbol(&self, id: &Syntax<Symbol>, phase: Phase) -> Result<Symbol, String> {
        let b = Expander::resolve(id, phase, false).inspect_err(|e| {
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
