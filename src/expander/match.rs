use std::collections::HashMap;

use gensym::gensym;
use itertools::Itertools;

use crate::{ast::Pair, Ast, Symbol};

// TODO: make compile time version that is garunteed that when if matches, indexing the matched
// fields will not fail, and indexing patterns that are not declared are compile time error

// sum of the folds might be/probably are supposed to be smoosh hash hash1 by putting all the
//  concantinating the values of all a in hash and hash1 into new hashmap
// just used internally to "parse" stuff
// TODO: maybe have a recursive data structure that represents a match instead of using lists
pub fn match_syntax(
    original: Ast,
    pattern: Ast,
) -> Result<impl Fn(Symbol) -> Option<Ast> + Clone, String> {
    fn r#match(s: Ast, pattern: Ast, original_s: &Ast) -> Result<HashMap<Symbol, Ast>, String> {
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
                (Pair(fst, Ast::Pair(second)), s) if matches!(&second.0, Ast::Symbol(Symbol(str )) if ["...", "...+"].contains(&&**str)) =>
                {
                    let Ast::Symbol(Symbol(str)) = second.0 else {
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
                        // TODO: maybe better way to get/garuntee matches are in correct order
                        .rev()
                        .flatten()
                        // chunk is not a true group by in that it only groups similiar things if they are next to each other so we first sort them
                        .sorted_by_key(|x| x.0.clone())
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
                            Err(format!("bad syntax1 {original_s}"))
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
                s => {
                    // Error
                    Err(format!("bad syntax, {} shoud be a pair, {original_s}", s.1))
                }
            }
            // null s, p
        } else if matches!(pattern, Ast::TheEmptyList) {
            if matches!(s, Ast::TheEmptyList) {
                Ok(HashMap::new())
            } else {
                Err(format!("bad syntax3 {original_s}"))
            }
        } else if matches!(pattern, Ast::Boolean(_)) || pattern.is_keyword() && pattern == s {
            Ok(HashMap::new())
        } else {
            // Error
            Err(format!("bad syntax4 {original_s}"))
        }
    }
    let symbol_map = r#match(original.clone(), pattern, &original)?;
    Ok(move |symbol| symbol_map.get(&symbol).cloned())
}

macro_rules! make_struct {
    ($gensym:ident, $($ids:ident)*) => {{
        #[derive(Clone)]
        struct $gensym { $($ids: Ast,)* }
    }};
    ($($ids:ident)*) => {
        gensym::gensym!(make_struct!($($ids)*));
    };
}
macro_rules! make_function {
    ($gensym:ident,($syntax:ident, $original:ident) $body:block) => {fn $gensym($syntax: Ast, $original: Ast) -> Result<Ast, String> $body
        $gensym};
    (($syntax:ident, $original:ident) $body:block) => {
        gensym::gensym!(make_function!(($syntax, $original) $body));
    };

    ($gensym:ident,($syntax:ident, _) $body:block) => {fn $gensym($syntax: Ast, _: Ast) -> Result<Ast, String> $body
        $gensym};
    (($syntax:ident, _) $body:block) => {
        gensym::gensym!(make_function!(($syntax, _) $body));
    };
}

macro_rules! match_syntax {
    (@matcher($syntax:expr)) => {
        if $syntax != Ast::TheEmptyList {
            return false;
        }
    };
    (@matcher($syntax:expr) $symbol:ident:id ...) => {
        let mut expr = $syntax;
        while let Ast::Pair(pair) = expr {
            if !pair.0.identifier() {
                return false;
            }
            expr = pair.1;
            if let Ast::Syntax(s) = expr {
                expr = s.0
            }
        }
    };
    (@matcher($syntax:expr) $symbol:ident ...) => {
        let mut expr = $syntax;
        while let Ast::Pair(pair) = expr {
            expr = pair.1;
            if let Ast::Syntax(s) = expr {
                expr = s.0
            }
        }

    };
    (@matcher($syntax:expr) ($($tt:tt)*) ...) => {
        let mut expr = $syntax;
        while let Ast::Pair(pair) = expr {
            match_syntax!(@matcher(pair.0)$($tt)*);
            expr = pair.1;
            if let Ast::Syntax(s) = expr {
                expr = s.0
            }
        }
    };
    (@matcher($syntax:expr) $symbol:ident:id ...+) => {

    };
    (@macther($syntax:expr) $symbol:ident ...+) => {

    };
    (@matcher($syntax:expr) ($($tt:tt)*) ...+) => {
    };
    (@matcher($syntax:expr) $symbol:ident:id $($tt:tt)*) => {
        let syntax = match $syntax {
            Ast::Syntax(s) => {
                if let Ast::Pair(s) = s.0 {
                    s
                } else {
                    return false
                }
            }
            Ast::Pair(p) => p,
            _ => return false
        };

        if !syntax.0.identifier() {
            return false;
        }
        match_syntax!(@matcher(syntax.1) $($tt)*);
    };
    (@matcher($syntax:expr) $symbol:ident $($tt:tt)*) => {
        let syntax = match $syntax {
            Ast::Syntax(s) => {
                if let Ast::Pair(s) = s.0 {
                    s
                } else {
                    return false
                }
            }
            Ast::Pair(p) => p,
            _ => return false
        };
        match_syntax!(@matcher(syntax.1) $($tt)*);
    };
    (@matcher($syntax:expr) ($($tt:tt)*) $($tts:tt)*) => {
        let syntax = match $syntax {
            Ast::Syntax(s) => {
                if let Ast::Pair(s) = s.0 {
                    s
                } else {
                    return false
                }
            }
            Ast::Pair(p) => p,
            _ => return false
        };
       match_syntax!(@matcher(syntax.0)  $($tt)*);
       match_syntax!(@matcher(syntax.1)  $($tts)*);
    };

    (@list($($ids:ident)*)) => { make_struct!($($ids)*);};
    (@list($($ids:ident)*) $symbol:ident:id ...  ) => {
        match_syntax!(@list($($ids)* $symbol ));
    };
    (@list($($ids:ident)*) $symbol:ident   ...   ) => {

        match_syntax!(@list($($ids)* $symbol )   );
    };
    (@list($($ids:ident)*) ($($tt:tt)*)  ...) => {
       match_syntax!(@list($($ids)*) $($tt)* );
    };
    (@list($($ids:ident)*) $symbol:ident:id $($tt:tt)*  ) => {

        make_function!((syntax, _) {
            if syntax.identifier() {
                Ok(syntax)} else {

                Err(format!("not an identifier {syntax}"))
        }
        });
        match_syntax!(@list($($ids)* $symbol ) $($tt)*);
    };
    (@list($($ids:ident)*) $symbol:ident  $($tt:tt)*   ) => {
        make_function!((syntax, _) {Ok(syntax)});
        match_syntax!(@list($($ids)* $symbol ) $($tt)*  );
    };
    (@list($($ids:ident)*) ($($tt:tt)*) $($tts:tt)*) => {
       match_syntax!(@list($($ids)*) $($tt)* $($tts)*);
    };
    (($($tt:tt)*)) => {
       //match_syntax!(@matcher $($tt)* );
       match_syntax!(@list() $($tt)* );
    };
}

fn matches_new(syntax: Ast) -> bool {
    match_syntax!(@matcher(syntax.clone()) (id:id) ...);
    match_syntax!(@matcher(syntax) (id:id) ...);
    return true;
}
fn make_empty_vars(pattern: Ast) -> HashMap<Symbol, Ast> {
    match_syntax!(((bar foo:id ) ...));
    match pattern {
        Ast::Pair(first) if matches!(&first.1, Ast::Pair(second) if matches!(&second.0, Ast::Symbol(Symbol(str)) if ["...", "...+"].contains(&&**str))) =>
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
