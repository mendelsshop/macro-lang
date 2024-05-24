use std::collections::HashMap;

use crate::{Ast, Symbol};

// just used internally to "parse" stuff
pub fn match_syntax(original: Ast, pattern: Ast) ->Result<impl Fn(Symbol) -> Option<Ast>, String> {
    let r#match = |s, pattern| -> Result<HashMap<Symbol, Ast>, String> {
        let hash_map: HashMap<Symbol, Ast> = HashMap::new();
        Ok(hash_map)
    };
    let symbol_map = r#match(original,pattern)?; 
    Ok(move |symbol| symbol_map.get(&symbol).cloned())
}
