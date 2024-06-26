use std::collections::HashMap;

use crate::{Ast, Symbol};

// sum of the folds might be/probably are supposed to be smoosh hash hash1 by putting all the
//  concantinating the values of all a in hash and hash1 into new hashmap
// just used internally to "parse" stuff
pub fn match_syntax(original: Ast, pattern: Ast) -> Result<impl Fn(Symbol) -> Option<Ast>, String> {
    fn r#match(
        s: Ast,
        pattern: Ast,
        original_pattern: &Ast,
    ) -> Result<HashMap<Symbol, Ast>, String> {
        // TODO: make sure pattern mathches ^id(:|$)
        if let Ast::Symbol(pattern) = pattern {
            if (pattern.0.starts_with("id") || pattern.0.starts_with("id:")) && !s.identifier() {
                Err(format!("not an identifier {s}"))
            } else {
                Ok(HashMap::from([(pattern, s)]))
            }
        } else if let Ast::Syntax(s) = s {
            r#match(s.0, pattern, original_pattern)
        } else if let Ast::List(pattern) = pattern {
            match (pattern.as_slice(), s) {
                ([fst, Ast::Symbol(Symbol(str, _))], s) if ["...", "...+"].contains(&&**str) => {
                    let flat_s = s.clone().to_synax_list();
                    match flat_s {
                        // null s
                        Ast::List(flat_s) if flat_s.len() == 0 && **str == *"...+" => {
                            Ok(make_empty_vars(Ast::List(pattern)))
                        }
                        // pair s
                        Ast::List(flat_s) if flat_s.len() != 0 => flat_s
                            .into_iter()
                            .map(|s| r#match(s, fst.clone(), original_pattern))
                            .try_fold(HashMap::new(), |mut hash, resulut| {
                                resulut.map(|hash1| {
                                    hash.extend(hash1);
                                    hash
                                })
                            }),
                        _ => {
                            // Error
                            Err(format!("bad syntax {original_pattern}"))
                        }
                    }
                }
                // null s, p
                (_, Ast::List(s)) if s.len() == 0 && pattern.len() == 0 => Ok(HashMap::new()),
                // pair s, p
                // i think len s = len p
                (_, Ast::List(s)) if s.len() == pattern.len() => s
                    .into_iter()
                    .zip(pattern.into_iter())
                    .map(|(s, pattern)| r#match(s, pattern, original_pattern))
                    .try_fold(HashMap::new(), |mut hash, resulut| {
                        resulut.map(|hash1| {
                            hash.extend(hash1);
                            hash
                        })
                    }),
                _ => {
                    // Error
                    Err(format!("bad syntax {original_pattern}"))
                }
            }
        } else if matches!(pattern, Ast::Boolean(_)) || pattern.is_keyword() && pattern == s {
            Ok(HashMap::new())
        } else {
            // Error
            Err(format!("bad syntax {original_pattern}"))
        }
    }
    let symbol_map = r#match(original, pattern.clone(), &pattern.clone())?;
    Ok(move |symbol| symbol_map.get(&symbol).cloned())
}

fn make_empty_vars(pattern: Ast) -> HashMap<Symbol, Ast> {
    match pattern {
        Ast::List(l) if matches!(&l[..],  [_, Ast::Symbol(Symbol(str, _))] if ["...", "...+"].contains(&&**str)) =>
        {
            let fst = l[0].clone();
            make_empty_vars(fst)
        }
        Ast::List(l) => {
            l.into_iter()
                .map(make_empty_vars)
                .fold(HashMap::new(), |mut hash, hash1| {
                    hash.extend(hash1);
                    hash
                })
        }
        // return hashmap of the symbol and null
        Ast::Symbol(s) => HashMap::from([(s, Ast::List(vec![]))]),
        _ => HashMap::new(),
    }
}

// just an alias for match syntax since we don't panic (in rust terms) immediatly, but instead we
// return result, so we don't need to do continuation stuff
pub fn try_match_syntax(
    original: Ast,
    pattern: Ast,
) -> Result<impl Fn(Symbol) -> Option<Ast>, String> {
    match_syntax(original, pattern)
}
