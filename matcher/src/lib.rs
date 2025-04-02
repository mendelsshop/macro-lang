use crate::custom::DotDotPlus;
use proc_macro::TokenStream;
use syn::{
    Ident, Token, ext::IdentExt, parenthesized, parse::Parse, parse_macro_input, token::DotDotDot,
};
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

#[derive(Clone)]
struct MatchStruct {
    binders: Vec<Ident>,
}
mod custom {
    use syn::custom_punctuation;

    custom_punctuation!(DotDotPlus, ..+);
}
enum SExpr {
    Many(Box<Self>, MatchStruct),
    ManyOne(Box<Self>, MatchStruct),
    Symbol(Ident),
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
                binders: vec![ident.clone()],
            },
            SExpr::Empty => MatchStruct {
                binders: Vec::new(),
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
        let lookahead = input.lookahead1();
        let sexpr = if lookahead.peek(Ident::peek_any) {
            let ident = Ident::parse_any(input)?;
            Self::Symbol(ident)
        } else {
            let paren_input;
            let last = Self::Empty;
            parenthesized!(paren_input in input);
            while !paren_input.is_empty() {
                let next = input.parse::<Self>()?;
            }
            last
        };
        if lookahead.peek(Token![...]) {
            input.parse::<DotDotDot>();

            let binders = sexpr.binders();
            Ok(SExpr::Many(Box::new(sexpr), binders))
        } else if lookahead.peek(DotDotPlus) {
            input.parse::<DotDotPlus>();
            let binders = sexpr.binders();
            Ok(SExpr::ManyOne(Box::new(sexpr), binders))
        } else {
            Ok(sexpr)
        }
    }
}

#[proc_macro]
pub fn match_syntax(input: TokenStream) -> TokenStream {
    let input_ = parse_macro_input!(input as SExpr);
    return TokenStream::new();
}
