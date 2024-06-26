use crate::{binding::Binding, r#match::match_syntax, syntax::Syntax, Ast, Expander, Function, Symbol};

impl Expander {
    pub fn compile(&mut self, s: Ast) -> Result<Ast, String> {
        match s {
            Ast::List(_) => {
                let core_sym = self.core_form_symbol(s.clone()).map_err(|_| format!("not a core form {}", s))?;
                match core_sym.to_string().as_str() {
                    "lambda" => {
                        let m = match_syntax(s, Ast::List(vec![ Ast::List(vec!["id".into(), "...".into()], ), "body".into()]))?;
                        let id = m("id".into());
                        let id = m("body".into());

                    },
                    "#%app" => todo!(),
                    "quote" => todo!(),
                    "quote-syntax" => todo!(),
                    _ => Err(format!("unrecognized core form {core_sym}"))
                    
                }
            }
            Ast::Symbol(s1) => {
                let b = self.resolve(&Syntax(s1, s.1))?;
                match b {
                    Binding::Variable(b) => Ok(Ast::Symbol(key_to_symbol(b.clone()))),
                    Binding::CoreBinding(s) => self
                        .core_primitives
                        .get(s)
                        .ok_or(format!("missing core bindig for primitive {s}"))
                        .cloned()
                        .map( Ast::Function),
                }
            }
            _ => Err(format!("bad syntax after expansion {}", s)),
        }
    }
}
fn key_to_symbol(key: Symbol) -> Symbol {
    key
}
