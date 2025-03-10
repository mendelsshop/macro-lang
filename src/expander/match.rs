use std::collections::HashMap;

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

macro_rules! match_syntax {
    (@matcher($original:expr, $syntax:expr)) => {
        if $syntax != Ast::TheEmptyList {
            return Err(format!("bad syntax {}", $original));
        }
    };
    (@matcher($original:expr,$syntax:expr) . $symbol:ident:id) => {
        if !$syntax.identifier() {
            return Err(format!("not an identifier {}", $syntax));
        }
    };
    (@matcher($original:expr,$syntax:expr) . $symbol:ident) => {
    };
    (@matcher($original:expr,$syntax:expr) . ($($tt:tt)*)) => {
        match_syntax!(@matcher($original,$syntax)$($tt)*);
    };

    (@matcher($original:expr,$syntax:expr) $symbol:ident:id ...) => {
        let mut expr = $syntax;
        while let Ast::Pair(pair) = expr {
            if !pair.0.identifier() {
                return Err(format!("not an identifier {}", pair.0));
            }
            expr = pair.1;
            if let Ast::Syntax(s) = expr {
                expr = s.0
            }
        }
    };
    (@matcher($original:expr,$syntax:expr) $symbol:ident ...) => {
        let mut expr = $syntax;
        while let Ast::Pair(pair) = expr {
            expr = pair.1;
            if let Ast::Syntax(s) = expr {
                expr = s.0
            }
        }

    };
    (@matcher($original:expr,$syntax:expr) ($($tt:tt)*) ...) => {
        let mut expr = $syntax;
        while let Ast::Pair(pair) = expr {
            match_syntax!(@matcher($original,pair.0)$($tt)*);
            expr = pair.1;
            if let Ast::Syntax(s) = expr {
                expr = s.0
            }
        }
    };
    (@matcher($original:expr,$syntax:expr) $symbol:ident:id ...+) => {
        let mut expr = $syntax;
        let mut found = false;
        while let Ast::Pair(pair) = expr {
            found = true;
            if !pair.0.identifier() {
                return Err(format!("not an identifier {}", pair.0));
            }
            expr = pair.1;
            if let Ast::Syntax(s) = expr {
                expr = s.0
            }
        }
        if !found {
            return Err(format!("bad syntax {}, expected one or more {}:id",$original, stringify!($symbol)));
        }
    };
    (@macther($original:expr,$syntax:expr) $symbol:ident ...+) => {
        let mut expr = $syntax;
        let mut found = false;
        while let Ast::Pair(pair) = expr {
            found = true;
            expr = pair.1;
            if let Ast::Syntax(s) = expr {
                expr = s.0
            }
        }
        if !found {
            return Err(format!("bad syntax {}, expected one or more {}", $original, stringify!($symbol)));
        }
    };
    (@matcher($original:expr,$syntax:expr) ($($tt:tt)*) ...+) => {
        let mut found = false;
        let mut expr = $syntax;
        while let Ast::Pair(pair) = expr {
            found = true;
            match_syntax!(@matcher($original,pair.0)$($tt)*);
            expr = pair.1;
            if let Ast::Syntax(s) = expr {
                expr = s.0
            }
        }
        if !found {
            return Err(format!("bad syntax {}, expected one or more {}", $original, stringify!(($($tt:tt)*))));
        }
    };
    (@matcher($original:expr,$syntax:expr) $symbol:ident:id $($tt:tt)*) => {
        let syntax = match $syntax {
            Ast::Syntax(s) => {
                if let Ast::Pair(s) = s.0 {
                    s
                } else {
                    return Err(format!("bad syntax, {} shoud be a pair, {}",  s.0,$original));
                }
            }
            Ast::Pair(p) => p,
            _ => return Err(format!("bad syntax, {} shoud be a pair, {}", $syntax, $original))
        };

        if !syntax.0.identifier() {
            return Err(format!("not an identifier {}", syntax.0));
        }
        match_syntax!(@matcher($original,syntax.1) $($tt)*);
    };
    (@matcher($original:expr,$syntax:expr) $symbol:ident $($tt:tt)*) => {
        let syntax = match $syntax {
            Ast::Syntax(s) => {
                if let Ast::Pair(s) = s.0 {
                    s
                } else {
                    return Err(format!("bad syntax, {} shoud be a pair, {}", s.0, $original));

                }
            }
            Ast::Pair(p) => p,
            _ => return Err(format!("bad syntax, {} shoud be a pair, {}", $syntax, $original))

        };
        match_syntax!(@matcher($original,syntax.1) $($tt)*);
    };
    (@matcher($original:expr,$syntax:expr) ($($tt:tt)*) $($tts:tt)*) => {
        let syntax = match $syntax {
            Ast::Syntax(s) => {
                if let Ast::Pair(s) = s.0 {
                    s
                } else {
                    return Err(format!("bad syntax, {} shoud be a pair, {}", s.0, $original));
                }
            }
            Ast::Pair(p) => p,
            _ => return Err(format!("bad syntax, {} shoud be a pair, {}", $syntax,$original))
        };
       match_syntax!(@matcher($original, syntax.0)  $($tt)*);
       match_syntax!(@matcher($original,syntax.1)  $($tts)*);
    };

    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*)) => {
        #[derive(Clone)]
        struct $name { $($ids: Ast,)* }
        impl $name {
            fn r#match(syntax: Ast) -> Result<Self, String> {
                match_syntax!(@matcher(syntax, syntax.clone()) $($ttl)*);
                todo!()
            }
        }
    };
    (@list($name:ident $($ids:ident)*, $($ttl:tt)*) $symbol:ident:id ...  ) => {
        match_syntax!(@list($name, $($ids)* $symbol, $($ttl)*));
    };
    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) $symbol:ident   ...   ) => {
        match_syntax!(@list($name, $($ids)* $symbol,$($ttl)*))
    };
    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) ($($tt:tt)*)  ...) => {
       match_syntax!(@list($name, $($ids)*,$($ttl)*) $($tt)* )
    };
    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) $symbol:ident:id $($tt:tt)*  ) => {
        match_syntax!(@list($name, $($ids)* $symbol,$($ttl)* ) $($tt)*)
    };
    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) $symbol:ident  $($tt:tt)*   ) => {
        match_syntax!(@list($name, $($ids)* $symbol,$($ttl)* ) $($tt)*  )
    };
    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) ($($tt:tt)*) $($tts:tt)*) => {
       match_syntax!(@list($name, $($ids)*,$(ttl)*) $($tt)* $($tts)*)
    };
    ($name:ident as ($($tt:tt)*)) => {
       match_syntax!(@list($name,,$($tt)*) $($tt)* )
    };
}

fn make_empty_vars(pattern: Ast) -> HashMap<Symbol, Ast> {
    match_syntax!(Foo as ((bar foo:id ) ...));
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
