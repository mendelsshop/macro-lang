use crate::{
    binding::Binding, list, r#match::match_syntax, syntax::Syntax, Ast, Expander, Function, Symbol,
};

impl Expander {
    pub fn compile(&mut self, s: Ast) -> Result<Ast, String> {
        let Ast::Syntax(syntax) = s.clone() else {
            panic!()
        };
        match syntax.0 {
            Ast::Pair(_) => {
                let core_sym = self
                    .core_form_symbol(s.clone())
                    .map_err(|_| format!("not a core form {}", s))?;
                match core_sym.to_string().as_str() {
                    "lambda" => {
                        let m = match_syntax(
                            s,
                            list!(
                                "lambda".into(),
                                list!("id".into(), "...".into(),),
                                "body".into()
                            ),
                        )?;
                        let formals = m("id".into()).ok_or("internal error")?;
                        let body = m("body".into()).ok_or("internal error")?;
                        Ok(list!(
                            "lambda".into(),
                            formals.map(|id| self.local_symbol(id).map(Ast::Symbol))?,
                            self.compile(body)?
                        ))
                    }
                    "#%app" => todo!(),
                    "quote" => todo!(),
                    "quote-syntax" => todo!(),
                    _ => Err(format!("unrecognized core form {core_sym}")),
                }
            }
            Ast::Symbol(s1) => {
                let b = self.resolve(&Syntax(s1, syntax.1))?;
                match b {
                    Binding::Variable(b) => Ok(Ast::Symbol(key_to_symbol(b.clone()))),
                    Binding::CoreBinding(s) => self
                        .core_primitives
                        .get(s)
                        .ok_or(format!("missing core bindig for primitive {s}"))
                        .cloned()
                        .map(Ast::Function),
                }
            }
            _ => Err(format!("bad syntax after expansion {}", s)),
        }
    }

    fn local_symbol(&self, id: Ast) -> Result<Symbol, String> {
        let Ast::Syntax(ref s) = id else {
            return Err(format!("expected symbol found {id}"));
        };
        let Ast::Symbol(ref id) = s.0 else {
            return Err(format!("expected symbol found {id}"));
        };
        let b = self.resolve(&Syntax(id.clone(), s.1.clone()))?;
        let Binding::Variable(s) = b else {
            return Err(format!("bad binding {b}"));
        };
        Ok(key_to_symbol(s.clone()))
    }
}

fn key_to_symbol(key: Symbol) -> Symbol {
    key
}
