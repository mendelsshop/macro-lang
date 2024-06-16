use crate::{binding::Binding, syntax::Syntax, Ast, Expander, Function, Symbol};

impl Expander {
    pub fn compile(&mut self, s: Syntax<Ast>) -> Result<Ast, String> {
        match s.0 {
            Ast::List(_) => {
                let core_sym = self.core_form_symbol(s.clone().0).map_err(|_| format!("not a core form {}", s.0))?;
                match core_sym.to_string().as_str() {
                    "lambda" => todo!(),
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
            _ => Err(format!("bad syntax after expansion {}", s.0)),
        }
    }
}

fn key_to_symbol(key: Symbol) -> Symbol {
    key
}
