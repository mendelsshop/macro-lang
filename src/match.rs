use std::collections::HashMap;

use crate::{Ast, Symbol};

// just used internally to "parse" stuff
pub fn match_syntax(original: Ast, pattern: Ast) -> Result<impl Fn(Symbol) -> Option<Ast>, String> {
    let r#match = |s, pattern| -> Result<HashMap<Symbol, Ast>, String> {
        let hash_map: HashMap<Symbol, Ast> = HashMap::new();
        // TODO: make sure pattern mathches ^id(:|$)
        if let Ast::Symbol(pattern) = pattern {
            todo!()
        } else if let Ast::Syntax(pattern) = s {
            todo!()
        } else if let Ast::List(pattern) = pattern {
            match (pattern.as_slice(), s) {
                ([fst, Ast::Symbol(Symbol(str, _))], _) if ["...", "...+"].contains(&&**str) => {
                    let flat_s = fst.clone().to_synax_list();
                    match flat_s {
                        // null s
                        Ast::List(flat_s) if flat_s.len() == 0 && **str == *"...+" => {
                            todo!()
                        }
                        // pair s
                        Ast::List(flat_s) if flat_s.len() != 0 => {
                            todo!()
                        }
                        _ => {
                            // Error
                            todo!()
                        }
                    }
                }
                // null s, p
                (_, Ast::List(s)) if s.len() == 0 && pattern.len() == 0 => {
                    todo!()
                }
                // pair s, p
                (_, Ast::List(s)) if s.len() != 0 && pattern.len() != 0 => {
                    todo!()
                }
                _ => {
                    // Error
                    todo!()
                }
            }
        } else if matches!(pattern, Ast::Boolean(_)) || pattern.is_keyword() && pattern == s {
            todo!()
        } else {
            // Error
            todo!()
        }
    };
    let symbol_map = r#match(original, pattern)?;
    Ok(move |symbol| symbol_map.get(&symbol).cloned())
}
