use std::{iter, path::Path, rc::Rc};

use itertools::Itertools;

use crate::ast::{Ast, Pair, Symbol};

#[derive(Debug)]
pub enum ModulePath {
    Root(RootModulePath),
    /// if the type is Up, then the list of submod path elements also includes the first Up
    /// (from the type) because a submod path element can also be an up
    Submodule(SubModuleType, Rc<[SubModulePathElement]>),
}

impl TryFrom<Ast> for ModulePath {
    type Error = String;

    fn try_from(value: Ast) -> Result<Self, Self::Error> {
        match value {
            Ast::Pair(pair) => match pair.0 {
                Ast::Symbol(ref s) => match s.0.to_string().as_str() {
                    "submod" => parse_submod(pair),
                    "quote" => parse_quote(pair)
                        .map(RootModulePath::Identifier)
                        .map(ModulePath::Root),
                    "lib" => parse_lib(pair).map(ModulePath::Root),
                    other => Err(format!("invalid module path head: {other}")),
                },

                other => Err(format!("invalid module path head: {other}")),
            },
            Ast::Symbol(symbol) => todo!(),
            Ast::String(symbol) => todo!(),
            other => Err(format!("invalid module path: {other}")),
        }
    }
}

fn parse_lib(pair: Box<Pair>) -> Result<RootModulePath, String> {
    todo!()
}

fn parse_submod(pair: Box<crate::ast::Pair>) -> Result<ModulePath, String> {
    if let Ast::Pair(inner_pair) = pair.1 {
        parse_submod_head(inner_pair)
    } else {
        Err(format!("invalid submodule path: {}", Ast::Pair(pair)))
    }
}

fn parse_submod_head(pair: Box<crate::ast::Pair>) -> Result<ModulePath, String> {
    let tail = pair.1;
    let head = pair.0;
    match head {
        Ast::Pair(inner_pair) => match inner_pair.0 {
            Ast::Symbol(ref s) => match s.0.to_string().as_str() {
                // TODO: maybe turn this into (submod . )
                "quote" => parse_quote(inner_pair)
                    .map(RootModulePath::Identifier)
                    .and_then(|hd| parse_submod_tail(SubModuleType::Root(hd), tail)),
                "lib" => parse_lib(inner_pair)
                    .and_then(|hd| parse_submod_tail(SubModuleType::Root(hd), tail)),

                other => Err(format!("invalid submodule path head: {other}")),
            },

            other => Err(format!("invalid submodule path head: {other}")),
        },
        ref head @ Ast::String(ref symbol) if symbol.to_string().as_str() == ".." => {
            parse_submod_tail(
                SubModuleType::Up,
                Ast::Pair(Box::new(Pair(head.clone(), tail))),
            )
        }
        Ast::String(symbol) if symbol.to_string().as_str() == "." => {
            parse_submod_tail(SubModuleType::Current, tail)
        }
        Ast::Symbol(symbol) => todo!(),
        Ast::String(symbol) => todo!(),
        other => Err(format!("invalid submodule path: {other}")),
    }
}
fn parse_submod_tail(ty: SubModuleType, tail: Ast) -> Result<ModulePath, String> {
    todo!()
}

fn parse_quote(pair: Box<crate::ast::Pair>) -> Result<Symbol, String> {
    if let Ast::Pair(ref inner_pair) = pair.0 {
        if let Ast::Symbol(ref s) = inner_pair.0 {
            if inner_pair.1 == Ast::TheEmptyList {
                Ok(s.clone())
            } else {
                Err(format!(
                    "invalid module path unterminated quote: {}",
                    Ast::Pair(pair)
                ))
            }
        } else {
            Err(format!(
                "invalid module path quote exptected symbol: {}",
                Ast::Pair(pair)
            ))
        }
    } else {
        Err(format!(
            "invalid module path unterminated quote: {}",
            Ast::Pair(pair)
        ))
    }
}

#[derive(Debug)]
pub enum ResolvedModulePath {
    Symbol(Symbol),
    List(Rc<[Symbol]>),
}
impl ModulePath {
    pub fn resolve_module_path(
        self,
        enclosing: Option<ResolvedModulePath>,
    ) -> Result<Option<ResolvedModulePath>, String> {
        let original = format!("{self:?}");
        match self {
            // TODO: what does (quote symbol) coresspond to in the typed repr
            ModulePath::Root(RootModulePath::Identifier(i)) => {
                Ok(Some(ResolvedModulePath::Symbol(i)))
            }
            ModulePath::Submodule(SubModuleType::Up, sub_module_path_elements) => {
                sub_module_path_elements
                    .into_iter()
                    .try_fold(enclosing, |enclosing, s| {
                        build_module_name(s, enclosing, &original)
                    })
            }
            ModulePath::Submodule(SubModuleType::Current, sub_module_path_elements) => {
                sub_module_path_elements
                    .into_iter()
                    .try_fold(enclosing, |enclosing, s| {
                        build_module_name(s, enclosing, &original)
                    })
            }

            ModulePath::Submodule(
                SubModuleType::Root(root_module_path),
                sub_module_path_elements,
            ) => sub_module_path_elements.into_iter().try_fold(
                ModulePath::Root(root_module_path).resolve_module_path(enclosing)?,
                |enclosing, s| build_module_name(s, enclosing, &original),
            ),
            _ => Err(format!("not a supported module path: {original}")),
        }
    }
}

fn build_module_name(
    s: &SubModulePathElement,
    enclosing: Option<ResolvedModulePath>,
    original: &str,
) -> Result<Option<ResolvedModulePath>, String> {
    match enclosing {
        None => Ok(Some(ResolvedModulePath::Symbol(s.clone().into()))),
        Some(ResolvedModulePath::Symbol(enclosing)) => {
            Ok(Some(ResolvedModulePath::List(Rc::new([
                enclosing,
                s.clone().into(),
            ]))))
        }
        Some(ResolvedModulePath::List(enclosing)) if matches!(s, SubModulePathElement::Up) => {
            let (last, enclosing) = enclosing
                .split_last()
                .ok_or(format!("too many \"..\"s: {original}"))?;
            if enclosing.is_empty() {
                Ok(Some(ResolvedModulePath::Symbol(last.clone())))
            } else {
                Ok(Some(ResolvedModulePath::List(Into::<Rc<[_]>>::into(
                    enclosing,
                ))))
            }
        }
        Some(ResolvedModulePath::List(enclosing)) => {
            Ok(Some(ResolvedModulePath::List(Into::<Rc<[_]>>::into(
                enclosing
                    .clone()
                    .into_iter()
                    .cloned()
                    .chain(iter::once(s.clone().into()))
                    .collect_vec()
                    .as_slice(),
            ))))
        }
    }
}

#[derive(Debug)]
pub enum SubModuleType {
    Root(RootModulePath),
    // unix .
    Current,
    /// unix ..
    Up,
}

#[derive(Debug)]
pub struct LibraryRelativePath(Rc<Path>);
#[derive(Debug)]
// we do not support file (platform dependent)
// we do not support planet (maybe some day)
pub enum RootModulePath {
    // id or (lib rel-string ..)
    // maybe seperate id an (lib ..)
    Lib(LibraryRelativePath, Rc<[LibraryRelativePath]>),
    // from (quote id)
    Identifier(Symbol),
}

#[derive(Debug, Clone)]
pub enum SubModulePathElement {
    Up,
    Identifier(Symbol),
}

impl From<SubModulePathElement> for Symbol {
    fn from(value: SubModulePathElement) -> Self {
        match value {
            SubModulePathElement::Up => "..".into(),
            SubModulePathElement::Identifier(symbol) => symbol,
        }
    }
}
