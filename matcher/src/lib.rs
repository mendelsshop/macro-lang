use std::collections::HashSet;

use crate::custom::DotDotPlus;
use custom::id;
use proc_macro::TokenStream;
use quote::{ToTokens, TokenStreamExt, quote};
use syn::{Ident, Token, ext::IdentExt, parenthesized, parse::Parse, parse_macro_input};
// original attempt at macro using MBE just here to look at to adpat
//macro_rules! match_syntax {
//   (@matcher($this:expr, $original:expr, $syntax:expr, $type:ty) $symbol:ident:id ...+) => {
//        let result = $syntax.map_to_syntax_list(
//            |ident|{
//                if !ident.identifier() {
//                    return Err(format!("not an identifier {}", ident));
//                } else {
//                    Ok(ident)
//                }
//            }
//        )?;
//        if result == Ast::TheEmptyList  {
//            return Err(format!("bad syntax {}, expected one or more {}", $original, stringify!($symbol)));
//        }
//        if $this.found.$symbol {
//            $this.$symbol = sexpr!((#(result)));
//        } else {
//            $this.found.$symbol = true;
//            $this.$symbol = result;
//        }
//    };
//    (@matcher($this:expr, $original:expr, $syntax:expr, $type:ty) $symbol:ident ...+) => {
//        let result = $syntax.to_synax_list();
//        if result == Ast::TheEmptyList  {
//            return Err(format!("bad syntax {}, expected one or more {}", $original, stringify!($symbol)));
//        }
//        if $this.found.$symbol {
//            $this.$symbol = sexpr!((#(result)));
//        } else {
//            $this.found.$symbol = true;
//            $this.$symbol = result;
//        }
//    };
//    (@matcher($this:expr, $original:expr, $syntax:expr, $type:ty) ($($tt:tt)*) ...+) => {
//        let mut found = false;
//        let set_found =|| {
//            let mut current: $type = Default::default();
//            match_syntax!(@set_found(current) $($tt)*);
//            current
//        };
//
//        let mut expr = $syntax;
//        let mut current = set_found();
//        while let Ast::Pair(pair) = expr {
//            let mut new = set_found();
//            found = true;
//            match_syntax!(@matcher(new, $original,pair.0, $type)$($tt)*);
//            current = current.merge(new);
//            expr = pair.1;
//            if let Ast::Syntax(s) = expr {
//                expr = s.0
//            }
//        }
//        if !found {
//            return Err(format!("bad syntax {}, expected one or more {}", $original, stringify!(($($tt:tt)*))));
//        }
//        $this = current.merge_both($this);
//    };
//    (@matcher($this:expr, $original:expr, $syntax:expr, $type:ty)) => {
//        if $syntax != Ast::TheEmptyList {
//            return Err(format!("bad syntax {}, expected end of list", $original));
//        }
//    };
//    (@matcher($this:expr, $original:expr, $syntax:expr, $type:ty) . $symbol:ident:id) => {
//        if !$syntax.identifier() {
//            return Err(format!("not an identifier {}", $syntax));
//        }
//        if $this.found.$symbol {
//            $this.$symbol = sexpr!((#($syntax)));
//        } else {
//            $this.found.$symbol = true;
//            $this.$symbol = $syntax;
//        }
//    };
//    (@matcher($this:expr, $original:expr, $syntax:expr, $type:ty) . $symbol:ident) => {
//        if $this.found.$symbol {
//            $this.$symbol = sexpr!((#($syntax)));
//        } else {
//            $this.found.$symbol = true;
//            $this.$symbol = $syntax;
//        }
//    };
//    (@matcher($this:expr, $original:expr, $syntax:expr, $type:ty) . ($($tt:tt)*)) => {
//        match_syntax!(@matcher($this, $original,$syntax, $type)$($tt)*);
//    };
//
//    (@matcher($this:expr, $original:expr, $syntax:expr, $type:ty) $symbol:ident:id ...) => {
//        let result = $syntax.map_to_syntax_list(
//            |ident|{
//                if !ident.identifier() {
//                    return Err(format!("not an identifier {}", ident));
//                } else {
//                    Ok(ident)
//                }
//            }
//        )?;
//
//        if $this.found.$symbol {
//            $this.$symbol = sexpr!((#(result)));
//        } else {
//            $this.found.$symbol = true;
//            $this.$symbol = result;
//        }
//
//
//    };
//    (@matcher($this:expr, $original:expr, $syntax:expr, $type:ty) $symbol:ident ...) => {
//        let result = $syntax.to_synax_list();
//        if $this.found.$symbol {
//            $this.$symbol = sexpr!((#(result)));
//        } else {
//            $this.found.$symbol = true;
//            $this.$symbol = result;
//        }
//    };
//    (@matcher($this:expr, $original:expr, $syntax:expr, $type:ty) ($($tt:tt)*) ...) => {
//        let set_found =|| {
//            let mut current: $type = Default::default();
//            match_syntax!(@set_found(current) $($tt)*);
//            current
//        };
//
//        let mut expr = $syntax;
//        let mut current = set_found();
//        while let Ast::Pair(pair) = expr {
//            let mut new = set_found();
//            match_syntax!(@matcher(new, $original,pair.0, $type)$($tt)*);
//            current = new.merge(current);
//            expr = pair.1;
//            if let Ast::Syntax(s) = expr {
//                expr = s.0
//            }
//        }
//        $this = current.merge_both($this);
//    };
//
//    (@matcher($this:expr, $original:expr,$syntax:expr, $type:ty) $symbol:ident:id $($tt:tt)*) => {
//        let syntax = match $syntax {
//            Ast::Syntax(s) => {
//                if let Ast::Pair(s) = s.0 {
//                    s
//                } else {
//                    return Err(format!("bad syntax, {} shoud be a pair, {}",  s.0,$original));
//                }
//            }
//            Ast::Pair(p) => p,
//            _ => return Err(format!("bad syntax, {} shoud be a pair, {}", $syntax, $original))
//        };
//
//        if !syntax.0.identifier() {
//            return Err(format!("not an identifier {}", syntax.0));
//        }
//        if $this.found.$symbol {
//            $this.$symbol = sexpr!((#(syntax.0)));
//        } else {
//            $this.found.$symbol = true;
//            $this.$symbol = syntax.0;
//        }
//        match_syntax!(@matcher($this, $original,syntax.1, $type) $($tt)*);
//    };
//    (@matcher($this:expr, $original:expr,$syntax:expr, $type:ty) $symbol:ident $($tt:tt)*) => {
//        let syntax = match $syntax {
//            Ast::Syntax(s) => {
//                if let Ast::Pair(s) = s.0 {
//                    s
//                } else {
//                    return Err(format!("bad syntax, {} shoud be a pair, {}", s.0, $original));
//
//                }
//            }
//            Ast::Pair(p) => p,
//            _ => return Err(format!("bad syntax, {} shoud be a pair, {}", $syntax, $original))
//
//        };
//        if $this.found.$symbol {
//            $this.$symbol = sexpr!((#(syntax.0)));
//        } else {
//            $this.found.$symbol = true;
//            $this.$symbol = syntax.0;
//        }
//        match_syntax!(@matcher($this, $original,syntax.1, $type) $($tt)*);
//    };
//    (@matcher($this:expr, $original:expr,$syntax:expr, $type:ty) ($($tt:tt)*) $($tts:tt)*) => {
//        let syntax = match $syntax {
//            Ast::Syntax(s) => {
//                if let Ast::Pair(s) = s.0 {
//                    s
//                } else {
//                    return Err(format!("bad syntax, {} shoud be a pair, {}", s.0, $original));
//                }
//            }
//            Ast::Pair(p) => p,
//            _ => return Err(format!("bad syntax, {} shoud be a pair, {}", $syntax,$original))
//        };
//       match_syntax!(@matcher($this, $original, syntax.0, $type)  $($tt)*);
//       match_syntax!(@matcher($this, $original, syntax.1, $type)  $($tts)*);
//    };
//
//    (@set_found($type:ident)) => {
//    };
//    (@set_found($type:ident) $symbol:ident:id ...+  ) => {
//        $type.found.$symbol= true;
//    };
//    (@set_found($type:ident) $symbol:ident   ...+   ) => {
//        $type.found.$symbol= true;
//    };
//    (@set_found($type:ident) ($($tt:tt)*)  ...+) => {
//       match_syntax!(@set_found($type) $($tt)* )
//    };
//    (@set_found($type:ident) $symbol:ident:id ...  ) => {
//        $type.found.$symbol= true;
//    };
//    (@set_found($type:ident) $symbol:ident   ...   ) => {
//        $type.found.$symbol= true;
//    };
//    (@set_found($type:ident) ($($tt:tt)*)  ...) => {
//       match_syntax!(@set_found($type) $($tt)* )
//    };
//    (@set_found($type:ident) $symbol:ident:id $($tt:tt)*  ) => {
//        $type.found.$symbol= true;
//        match_syntax!(@set_found($type ) $($tt)*)
//    };
//    (@set_found($type:ident) $symbol:ident  $($tt:tt)*   ) => {
//        $type.found.$symbol= true;
//        match_syntax!(@set_found($type ) $($tt)*)
//
//    };
//    (@set_found($type:ident,$($ids:ident)*) $symbol:ident:id $($tt:tt)*  ) => {
//        $type.found.$symbol= true;
//        match_syntax!(@set_found($type) $($tt)*  )
//    };
//    (@set_found($type:ident) ($($tt:tt)*) $($tts:tt)*) => {
//       match_syntax!(@set_found($type) $($tt)* $($tts)*)
//    };
//    (@set_found($type:ident) $($tt:tt)*) => {
//       match_syntax!(@set_found($type) $($tt)*)
//    };
//    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*)) => {
//        gensym::gensym!(make_match_struct!($name, $($ids)*, $($ttl)*))
//    };
//
//    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) $symbol:ident:id ...+  ) => {
//        match_syntax!(@list($name, $($ids)* $symbol, $($ttl)*));
//    };
//    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) $symbol:ident   ...+   ) => {
//        match_syntax!(@list($name, $($ids)* $symbol,$($ttl)*))
//    };
//    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) ($($tt:tt)*)  ...+) => {
//       match_syntax!(@list($name, $($ids)*,$($ttl)*) $($tt)* )
//    };
//    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) $symbol:ident:id ...  ) => {
//        match_syntax!(@list($name, $($ids)* $symbol, $($ttl)*));
//    };
//    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) $symbol:ident   ...   ) => {
//        match_syntax!(@list($name, $($ids)* $symbol,$($ttl)*))
//    };
//    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) ($($tt:tt)*)  ...) => {
//       match_syntax!(@list($name, $($ids)*,$($ttl)*) $($tt)* )
//    };
//    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) $symbol:ident:id $($tt:tt)*  ) => {
//        match_syntax!(@list($name, $($ids)* $symbol,$($ttl)* ) $($tt)*)
//    };
//    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) $symbol:ident  $($tt:tt)*   ) => {
//        match_syntax!(@list($name, $($ids)* $symbol,$($ttl)* ) $($tt)*  )
//    };
//    (@list($name:ident, $($ids:ident)*, $($ttl:tt)*) ($($tt:tt)*) $($tts:tt)*) => {
//        // this causes problems with ((ab ...) (bc ...)) which get  transformed to -> ab ... bc ... which is invalid
//        // either allow this form or idk
//       match_syntax!(@list($name, $($ids)*,$($ttl)*) $($tt)* $($tts)*)
//    };
//    ($name:ident as ($($tt:tt)*)) => {
//       match_syntax!(@list($name,,$($tt)*) $($tt)* )
//    };
//
//}

#[derive(Clone, Debug)]
struct MatchStruct {
    binders: HashSet<Ident>,
}
mod custom {
    use syn::{custom_keyword, custom_punctuation};

    custom_punctuation!(DotDotPlus, ..+);
    custom_keyword!(id);
}
#[derive(Debug)]
enum SExpr {
    Many(Box<Self>, MatchStruct),
    ManyOne(Box<Self>, MatchStruct),
    Symbol(Ident),
    // only matches identifiers
    Identifier(Ident),
    Empty,
    Pair {
        car: Box<Self>,
        cdr: Box<Self>,
        binders: MatchStruct,
    },
}
impl SExpr {
    fn binders(&self) -> MatchStruct {
        match self {
            SExpr::Many(_, match_struct) => match_struct.clone(),
            SExpr::ManyOne(_, match_struct) => match_struct.clone(),
            SExpr::Symbol(ident) => MatchStruct {
                binders: HashSet::from([ident.clone()]),
            },
            SExpr::Identifier(ident) => MatchStruct {
                binders: HashSet::from([ident.clone()]),
            },
            SExpr::Empty => MatchStruct {
                binders: HashSet::new(),
            },
            SExpr::Pair {
                car: _,
                cdr: _,
                binders,
            } => binders.clone(),
        }
    }
}
impl Parse for SExpr {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let sexpr = if input.peek(Ident::peek_any) {
            let ident = Ident::parse_any(input)?;
            if input.peek(Token![:]) {
                input.parse::<Token![:]>()?;
                if input.peek(id) {
                    input.parse::<id>()?;
                    Self::Identifier(ident)
                } else {
                    return Err(input.error("unkown syntax expected `id` after `:`"));
                }
            } else if ident.to_string() == "id" {
                Self::Identifier(ident)
            } else {
                Self::Symbol(ident)
            }
        } else {
            let paren_input;
            parenthesized!(paren_input in input);
            parse_paren(&paren_input)?
        };
        if input.peek(Token![...]) {
            input.parse::<Token![...]>()?;

            let binders = sexpr.binders();
            Ok(SExpr::Many(Box::new(sexpr), binders))
        } else if input.peek(DotDotPlus) {
            input.parse::<DotDotPlus>()?;
            let binders = sexpr.binders();
            Ok(SExpr::ManyOne(Box::new(sexpr), binders))
        } else {
            Ok(sexpr)
        }
    }
}

fn parse_paren(input: &syn::parse::ParseBuffer<'_>) -> syn::Result<SExpr> {
    if input.is_empty() {
        Ok(SExpr::Empty)
    } else {
        let current = input
            .parse::<SExpr>()
            .map_err(|_| input.error("unterminated sexpr pair"))?;
        let mut current_binders = current.binders();
        if input.peek(Token![.]) {
            input.parse::<Token![.]>()?;
            let end = input.parse::<SExpr>().map_err(|_| {
                input.error("expected expression after improper list dots".to_string())
            })?;
            if input.is_empty() {
                check_duplicates(input, &mut current_binders, &end)?;
                Ok(SExpr::Pair {
                    car: Box::new(current),
                    cdr: Box::new(end),
                    binders: current_binders,
                })
            } else {
                Err(input.error("expected nothing after last expression in improper list"))
            }
        } else {
            let next = parse_paren(input)?;
            check_duplicates(input, &mut current_binders, &next)?;

            Ok(SExpr::Pair {
                car: Box::new(current),
                cdr: Box::new(next),
                binders: current_binders,
            })
        }
    }
}

fn check_duplicates(
    input: &syn::parse::ParseBuffer<'_>,
    current_binders: &mut MatchStruct,
    next: &SExpr,
) -> Result<(), syn::Error> {
    next.binders().binders.into_iter().try_for_each(|binder| {
        let message = format!("duplicate binder {binder}");
        if !current_binders.binders.insert(binder) {
            Err(input.error(message))
        } else {
            Ok(())
        }
    })
}

impl ToTokens for SExpr {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            SExpr::Many(sexpr, match_struct) => {
                let binders = match_struct.binders.clone().into_iter();
                let binders1 = match_struct.binders.clone().into_iter();
                let token = quote! {
                    let res = s.fold_to_syntax_list::<Self, String>(
                        &mut |s, mut current| {
                            let mut this = Self::default();
                            #sexpr;
                            #(  current.#binders = crate::ast::Ast::Pair(Box::new(Pair(this.#binders, current.#binders))); )*
                             Ok(current)
                        },
                        Self::default()
                    )?;

                    #(  this.#binders1 = res.#binders1; )*
                };
                tokens.append_all(token.into_iter());
            }
            SExpr::ManyOne(sexpr, match_struct) => {
                // TODO: make sure at least one
                let sexpr_string = format!("{sexpr:?}");
                let binders = match_struct.binders.clone().into_iter();
                let binders1 = match_struct.binders.clone().into_iter();
                let token = quote! {
                    let sexpr = #sexpr_string;
                    let error = format!("expected at least one of {sexpr:?} {s}");
                    let res = s.fold_to_syntax_list::<(usize, Self), String>(
                        &mut |s, (i, mut current)| {
                            let next_i = if s == crate::ast::Ast::TheEmptyList { 0 } else  {1  } + i;
                            let mut this = Self::default();
                            #sexpr;
                            #(  current.#binders = crate::ast::Ast::Pair(Box::new(Pair(this.#binders, current.#binders))); )*
                             Ok((next_i, current))
                        },
                        (0, Self::default())
                    )?;

                    if res.0 == 0 {
                        return Err(error)
                    }
                    #(  this.#binders1 = res.1.#binders1; )*
                };
                tokens.append_all(token.into_iter());
            }
            SExpr::Symbol(ident) => {
                let token = quote! {
                    this.#ident = s;
                };
                tokens.append_all(token.into_iter());
            }
            SExpr::Identifier(ident) => {
                let token = quote! {
                    if !s.identifier() {
                       return Err(format!("not an identifier {s}"))
                    }
                    this.#ident = s;
                };
                tokens.append_all(token.into_iter());
            }
            SExpr::Empty => {
                let token = quote! {
                    if s != crate::ast::Ast::TheEmptyList {
                       return Err(format!("bad syntax expected expected null {s}"))
                    }
                };
                tokens.append_all(token.into_iter());
            }
            SExpr::Pair {
                car,
                cdr,
                binders: _,
            } => {
                let token = quote! {
                   if let crate::ast::Ast::Pair(p) = s {
                        let crate::ast::Pair(car, cdr) = *p;
                        {
                            let s = car;
                            #car
                        }
                        {

                            let s = cdr;
                            #cdr
                        }
                    } else {
                       return Err(format!("not a pair {s}"))
                    }
                };
                tokens.append_all(token.into_iter());
            }
        }
    }
}
#[proc_macro]
pub fn match_syntax(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as SExpr);
    let binders = input.binders().binders.into_iter();
    let binders1 = input.binders().binders.into_iter();
    quote! {
        struct Matcher {
            #(  #binders: crate::ast::Ast, )*
        }
        impl Default for Matcher {
            fn default() -> Self {
                 Self {
                    #(  #binders1: crate::ast::Ast::TheEmptyList, )*
                }
            }
        }
        impl Matcher {
            fn matches(s: Ast) -> Result<Self, String> {
                let mut this = Self::default();
                #input
                Ok(this)
            }
        }
    }
    .into()
}
