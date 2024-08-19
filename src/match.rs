use std::collections::HashMap;

use itertools::Itertools;

use crate::{ast::Pair, Ast, Symbol};

// sum of the folds might be/probably are supposed to be smoosh hash hash1 by putting all the
//  concantinating the values of all a in hash and hash1 into new hashmap
// just used internally to "parse" stuff
pub fn match_syntax(original: Ast, pattern: Ast) -> Result<impl Fn(Symbol) -> Option<Ast>, String> {
    fn r#match(
        s: Ast,
        pattern: Ast,
        original_s: &Ast,
        // HashMap of vec no worky b/c it only vec if matching ...+/...
        // Need better way to smush ...+/... without replacement
    ) -> Result<HashMap<Symbol, Ast>, String> {
        // TODO: make sure pattern mathches ^id
        if let Ast::Symbol(pattern) = pattern {
            if (pattern.0.starts_with("id") || pattern.0.starts_with("id:")) && !s.identifier() {
                Err(format!("not an identifier {s}"))
            } else {
                Ok(HashMap::from([(pattern, s)]))
            }
        } else if let Ast::Syntax(s) = s {
            r#match(s.0, pattern, original_s)
        } else if let Ast::Pair(pattern) = pattern {
            match (*pattern.clone(), s) {
                (Pair(fst, Ast::Pair(second)), s) if matches!(&second.0, Ast::Symbol(Symbol(str,_ )) if ["...", "...+"].contains(&&**str)) =>
                {
                    let Ast::Symbol(Symbol(str, _)) = second.0 else {
                        panic!()
                    };
                    let flat_s = s.to_synax_list();
                    match flat_s {
                        // null s
                        Ast::TheEmptyList if *str == *"..." => {
                            Ok(make_empty_vars(Ast::Pair(pattern)))
                        }
                        Ast::TheEmptyList if *str == *"...+" => Err(format!(
                            "bad syntax {original_s}, expected one or more {fst}"
                        )),
                        // pair s
                        _ if flat_s.list() => Ok((flat_s.foldl(
                            |s, vars: Result<Vec<HashMap<Symbol, Ast>>, String>| {
                                vars.and_then(|mut vars| {
                                    r#match(s, fst.clone(), original_s).map(|s| {
                                        vars.push(s);
                                        vars
                                    })
                                })
                            },
                            Ok(vec![]),
                        )?)?
                        .into_iter()
                        .flatten()
                        .chunk_by(|vars| vars.0.clone())
                        .into_iter()
                        .map(|(s, matches)| {
                            (
                                s,
                                matches.fold(Ast::TheEmptyList, |list, current| {
                                    Ast::Pair(Box::new(Pair(current.1, list)))
                                }),
                            )
                        })
                        .collect::<HashMap<_, _>>()),
                        _ => {
                            // Error
                            Err(format!("bad syntax {original_s}"))
                        }
                    }
                }
                // pair s, p
                // i think len s = len p
                (Pair(p1, p2), Ast::Pair(s)) => {
                    r#match(s.0.clone(), p1, original_s).and_then(|mut vars| {
                        r#match(s.1, p2, original_s).map(|vars_cdr| {
                            vars.extend(vars_cdr);
                            vars
                        })
                    })
                }
                _ => {
                    // Error
                    Err(format!("bad syntax {original_s}"))
                }
            }
            // null s, p
        } else if matches!(pattern, Ast::TheEmptyList) {
            Ok(HashMap::new())
        } else if matches!(pattern, Ast::Boolean(_)) || pattern.is_keyword() && pattern == s {
            Ok(HashMap::new())
        } else {
            // Error
            Err(format!("bad syntax {original_s}"))
        }
    }
    let symbol_map = r#match(original.clone(), pattern, &original)?;
    Ok(move |symbol| symbol_map.get(&symbol).cloned())
}

fn make_empty_vars(pattern: Ast) -> HashMap<Symbol, Ast> {
    match pattern {
        Ast::Pair(first) if matches!(&first.1, Ast::Pair(second) if matches!(&second.0, Ast::Symbol(Symbol(str,_ )) if ["...", "...+"].contains(&&**str))) =>
        {
            let fst = first.0;
            make_empty_vars(fst)
        }
        Ast::Pair(p) => {
            let mut vars = make_empty_vars(p.0);
            vars.extend(make_empty_vars(p.1));
            vars
        }
        // return hashmap of the symbol and null
        Ast::Symbol(s) => HashMap::from([(s, Ast::TheEmptyList)]),
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
impl Ast {
    pub fn to_synax_list(self) -> Self {
        match self {
            Self::Pair(l) => Self::Pair(Box::new(Pair(l.0, l.1.to_synax_list()))),
            Self::Syntax(s) => s.0.to_synax_list(),
            _ => self,
        }
    }
}
