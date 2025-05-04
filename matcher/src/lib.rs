use std::collections::HashSet;

use crate::custom::DotDotPlus;
use custom::id;
use proc_macro::TokenStream;
use quote::{ToTokens, TokenStreamExt, quote};
use rand::random;
use syn::{
    Ident, Token, ext::IdentExt, parenthesized, parse::Parse, parse_macro_input, spanned::Spanned,
};

#[derive(Clone, Debug)]
struct MatchStruct {
    binders: HashSet<Ident>,
}
mod custom {
    use syn::{custom_keyword, custom_punctuation};

    custom_punctuation!(DotDotPlus, ..+);
    custom_keyword!(id);
}
struct NameAsSExpr(Ident, SExpr);
impl Parse for NameAsSExpr {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let ident = Ident::parse_any(input)?;
        input.parse::<Token![as]>()?;
        let sexpr = input.parse()?;
        Ok(NameAsSExpr(ident, sexpr))
    }
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
                    let ident = Ident::new(&(ident.to_string() + "_id"), ident.span());
                    Self::Identifier(ident)
                } else {
                    return Err(input.error("unkown syntax expected `id` after `:`"));
                }
            } else if ident == "id" {
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
        if input.peek(Token![.]) && !(input.peek(Token![...]) || input.peek(DotDotPlus)) {
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
                            #(  current.#binders = crate::ast::Ast::Pair(Box::new(crate::ast::Pair(this.#binders, current.#binders))); )*
                             Ok(current)
                        },
                        Self::default()
                    )?;

                    #(  this.#binders1 = res.#binders1; )*
                };
                tokens.append_all(token);
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
                tokens.append_all(token);
            }
            SExpr::Symbol(ident) => {
                let token = quote! {
                    this.#ident = s;
                };
                tokens.append_all(token);
            }
            SExpr::Identifier(ident) => {
                let token = quote! {
                    if !s.identifier() {
                       return Err(format!("not an identifier {s}"))
                    }
                    this.#ident = s;
                };
                tokens.append_all(token);
            }
            SExpr::Empty => {
                let token = quote! {
                    if s != crate::ast::Ast::TheEmptyList {
                       return Err(format!("bad syntax expected expected null {s}"))
                    }
                };
                tokens.append_all(token);
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
                tokens.append_all(token);
            }
        }
    }
}
#[proc_macro]
pub fn match_syntax_as(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as NameAsSExpr);
    let name = input.0;
    let input = input.1;
    let binders = input.binders().binders.into_iter();
    let binders1 = input.binders().binders.into_iter();
    quote! {

        #[derive(Clone)]
        struct #name {
            #(  #binders: crate::ast::Ast, )*
        }
        impl Default for #name {
            fn default() -> Self {
                 Self {
                    #(  #binders1: crate::ast::Ast::TheEmptyList, )*
                }
            }
        }
        impl #name {
            fn matches(s: Ast) -> Result<Self, String> {
                let mut this = Self::default();
                #input
                Ok(this)
            }
        }
        // TODO: somehow just return the type (#name), but doesn't seem to be usable in a type context

    }
    .into()
}
#[proc_macro]
pub fn match_syntax(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as SExpr);
    let binders = input.binders().binders.into_iter();
    let binders1 = input.binders().binders.into_iter();
    let name = syn::Ident::new(&format!("Matcher{}", random::<u64>()), input.span());
    quote! {
        {
        #[derive(Clone)]
        struct #name {
            #(  #binders: crate::ast::Ast, )*
        }
        impl Default for #name {
            fn default() -> Self {
                 Self {
                    #(  #binders1: crate::ast::Ast::TheEmptyList, )*
                }
            }
        }
        impl #name {
            fn matches(s: Ast) -> Result<Self, String> {
                let mut this = Self::default();
                #input
                Ok(this)
            }
        }
        // TODO: somehow just return the type (#name), but doesn't seem to be usable in a type context
        (#name::matches)
        }
    }
    .into()
}
