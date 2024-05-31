use std::collections::HashMap;

use crate::{Ast, Symbol};

// just used internally to "parse" stuff
pub fn match_syntax(original: Ast, pattern: Ast) -> Result<impl Fn(Symbol) -> Option<Ast>, String> {
    let r#match = |s, pattern| -> Result<HashMap<Symbol, Ast>, String> {
        if let Ast::Symbol(pattern) = pattern {
        } else if let Ast::Syntax(pattern) = s {
            // TODO: patternp length 2 with second being ...+, ...
        } else if let Ast::List(patternp) = s {
        } else if let (Ast::List(pattern), Ast::List(s)) = (pattern, s) {
            match (pattern.len(), s.len()) {
                (0, 0) => {}
                (0, 1) | (1, 0) => {
                    // error
                }
                _ => {}
            }
        } else {
            // Error
        }

        let hash_map: HashMap<Symbol, Ast> = HashMap::new();
        Ok(hash_map)
    };
    let symbol_map = r#match(original, pattern)?;
    Ok(move |symbol| symbol_map.get(&symbol).cloned())
}
