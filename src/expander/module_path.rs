use core::fmt;
use std::{
    iter,
    path::{Path, PathBuf},
    rc::Rc,
};

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
            Ast::Symbol(symbol) => parse_symbol_path(symbol),
            Ast::String(symbol) => parse_string_path(&symbol, true, true)
                .map(RootModulePath::File)
                .map(Self::Root),
            other => Err(format!("invalid module path: {other}")),
        }
    }
}

fn parse_lib(pair: Box<Pair>) -> Result<RootModulePath, String> {
    if let Ast::Pair(inner_pair) = pair.1 {
        let first = parse_string_path_ast(inner_pair.0, false, true)
            .map_err(|e| format!("invalid module path lib form {e}"))?;
        let pair_string = format!("{} is not a list", inner_pair.1);
        let rest = inner_pair
            .1
            .map_to_list_checked(|x| {
                parse_string_path_ast(x, false, false).map(LibraryRelativePath)
            })
            .map_err(|e| format!("invalid module path lib form: {}", e.unwrap_or(pair_string)))?;
        Ok(RootModulePath::Lib(LibraryRelativePath(first), rest.into()))
    } else {
        Err(format!(
            "invalid module path lib form must have at least one element {}",
            Ast::Pair(pair)
        ))
    }
}
fn parse_string_path_ast(
    pair: Ast,
    dot_dirs_ok: bool,
    file_end_ok: bool,
) -> Result<Rc<Path>, String> {
    if let Ast::String(s) = pair {
        parse_string_path(&s, dot_dirs_ok, file_end_ok)
    } else {
        Err(format!("path is not a string {pair}"))
    }
}
fn parse_string_path(pair: &str, dot_dirs_ok: bool, file_end_ok: bool) -> Result<Rc<Path>, String> {
    let mut path_iter = pair.chars().peekable();
    enum State {
        Start,
        DotEnd,
        PathItem(String),
        PathItemExt(String, String),
        Slashed,
        Dot,
    }

    // TODO: %
    path_iter
        .try_fold(
            (PathBuf::new(), State::Start),
            |(mut path_buf, state), c| match state {
                State::Start if c == '.' && dot_dirs_ok => Ok((path_buf, State::Dot)),
                State::Start if c == '/' => {
                    Err(format!("path string cannot start with a / {pair}"))
                }
                State::Start if is_file_character(c) => {
                    Ok((path_buf, State::PathItem(c.to_string())))
                }
                State::Start => Err(format!("bad path string character {c}")),

                State::Slashed if c == '.' && dot_dirs_ok => Ok((path_buf, State::Dot)),
                State::Slashed if c == '/' => {
                    Err(format!("path string contain multiple /s in a row {pair}"))
                }
                State::Slashed if is_file_character(c) => {
                    Ok((path_buf, State::PathItem(c.to_string())))
                }
                State::Slashed => Err(format!("bad path string character {c}")),
                State::DotEnd if c == '/' => {
                    path_buf.push("..");
                    Ok((path_buf, State::Slashed))
                }
                State::DotEnd => Err(format!(".. must be followed by /")),
                State::PathItem(str) if c == '.' && file_end_ok => {
                    Ok((path_buf, State::PathItemExt(str, "".to_string())))
                }

                State::PathItem(str) if c == '/' => {
                    path_buf.push(format!("{str}.rkt"));
                    Ok((path_buf, State::Slashed))
                }
                State::PathItem(mut str) if is_file_character(c) => {
                    str.push(c);
                    Ok((path_buf, State::PathItem(str)))
                }
                State::PathItem(_) => Err(format!("bad path string character {c}")),
                State::PathItemExt(_, _) if c == '/' => {
                    Err(format!("path string cannot end with / {pair}"))
                }

                State::PathItemExt(s, ext) if c == '.' => Ok((
                    path_buf,
                    State::PathItemExt(format!("{s}.{ext}"), "".to_string()),
                )),
                State::PathItemExt(s, mut ext) if is_file_character(c) => {
                    ext.push(c);
                    Ok((path_buf, State::PathItemExt(s, ext)))
                }
                State::PathItemExt(_, _) => Err(format!("bad path string character {c}")),

                State::Dot if c == '.' => Ok((path_buf, State::DotEnd)),
                State::Dot if c == '/' => {
                    path_buf.push(".");
                    Ok((path_buf, State::Slashed))
                }
                State::Dot => Err(format!("path string . must be followed by . or /")),
            },
        )
        .and_then(|(mut p, s)| match s {
            State::Start => Err(format!("path string is empty")),
            State::DotEnd => Ok(p.into()),
            State::PathItem(s) => {
                p.push(format!("{s}.rkt"));
                Ok(p.into())
            }
            State::PathItemExt(_, e) if e.is_empty() => {
                Err(format!("path string missing extension {pair}"))
            }
            State::PathItemExt(s, e) => {
                p.push(format!("{s}.{}", if e == "ss" { "rkt" } else { &e }));
                Ok(p.into())
            }
            State::Slashed => Err(format!("path string cannot end with / {pair}")),
            State::Dot => {
                p.push(".");
                Ok(p.into())
            }
        })
}

fn is_file_character(c: char) -> bool {
    c.is_ascii_alphanumeric() | ['+', '_', '-'].contains(&c)
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
        Ast::Symbol(symbol) => parse_symbol_path(symbol),
        Ast::String(symbol) => parse_string_path(&symbol, true, true)
            .map(RootModulePath::File)
            .map(ModulePath::Root),
        other => Err(format!("invalid submodule path: {other}")),
    }
}

fn parse_symbol_path(symbol: Symbol) -> Result<ModulePath, String> {
    parse_string_path(&symbol.to_string(), false, false)
        .map(LibraryRelativePath)
        .map(|p| RootModulePath::Lib(p, Rc::new([])))
        .map(ModulePath::Root)
}
fn parse_submod_tail(ty: SubModuleType, tail: Ast) -> Result<ModulePath, String> {
    let tail_string = tail.to_string();
    let tail = tail
        .to_list_checked()
        .map_err(|_| format!("submodule path elements are not in a list {tail_string}"))?;
    tail.into_iter()
        .map(|s| match s {
            Ast::String(s) if s.to_string().as_str() == ".." => Ok(SubModulePathElement::Up),
            Ast::Symbol(s) => Ok(SubModulePathElement::Identifier(s)),
            o => Err(format!("invalid submodule path element {o}")),
        })
        .try_collect()
        .map(|tail| ModulePath::Submodule(ty, tail))
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

#[derive(Clone, Debug, Hash, Eq, Ord, PartialEq, PartialOrd)]
pub enum ResolvedModulePath {
    Symbol(Symbol),
    List(Rc<[Symbol]>),
}
impl fmt::Display for ResolvedModulePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResolvedModulePath::Symbol(symbol) => write!(f, "{symbol}"),
            ResolvedModulePath::List(symbols) => {
                write!(f, "({})", symbols.iter().map(|s| s.to_string()).join(" "))
            }
        }
    }
}
impl From<&str> for ResolvedModulePath {
    fn from(value: &str) -> Self {
        Self::Symbol(value.into())
    }
}
impl From<ResolvedModulePath> for Ast {
    fn from(value: ResolvedModulePath) -> Self {
        match value {
            ResolvedModulePath::Symbol(symbol) => Self::Symbol(symbol),
            ResolvedModulePath::List(symbols) => {
                symbols
                    .into_iter()
                    .fold(Ast::TheEmptyList, |list: Ast, current: &Symbol| {
                        Ast::Pair(Box::new(Pair(Ast::Symbol(current.clone()), list)))
                    })
            }
        }
    }
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
                        build_module_name(s, enclosing, &original).map(Some)
                    })
            }
            ModulePath::Submodule(SubModuleType::Current, sub_module_path_elements) => {
                sub_module_path_elements
                    .into_iter()
                    .try_fold(enclosing, |enclosing, s| {
                        build_module_name(s, enclosing, &original).map(Some)
                    })
            }

            ModulePath::Submodule(
                SubModuleType::Root(root_module_path),
                sub_module_path_elements,
            ) => sub_module_path_elements.into_iter().try_fold(
                ModulePath::Root(root_module_path).resolve_module_path(enclosing)?,
                |enclosing, s| build_module_name(s, enclosing, &original).map(Some),
            ),
            _ => Err(format!("not a supported module path: {original}")),
        }
    }
}

pub fn build_module_name(
    s: &SubModulePathElement,
    enclosing: Option<ResolvedModulePath>,
    original: &str,
) -> Result<ResolvedModulePath, String> {
    match enclosing {
        None => Ok(ResolvedModulePath::Symbol(s.clone().into())),
        Some(ResolvedModulePath::Symbol(enclosing)) => Ok(ResolvedModulePath::List(Rc::new([
            enclosing,
            s.clone().into(),
        ]))),
        Some(ResolvedModulePath::List(enclosing)) if matches!(s, SubModulePathElement::Up) => {
            let (last, enclosing) = enclosing
                .split_last()
                .ok_or(format!("too many \"..\"s: {original}"))?;
            if enclosing.is_empty() {
                Ok(ResolvedModulePath::Symbol(last.clone()))
            } else {
                Ok(ResolvedModulePath::List(enclosing.into()))
            }
        }
        Some(ResolvedModulePath::List(enclosing)) => Ok(ResolvedModulePath::List(
            enclosing
                .clone()
                .into_iter()
                .cloned()
                .chain(iter::once(s.clone().into()))
                .collect(),
        )),
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
    // from rel-string
    File(Rc<Path>),
}

#[derive(Debug, Clone)]
pub enum SubModulePathElement {
    Up,
    Identifier(Symbol),
}
impl From<Symbol> for SubModulePathElement {
    fn from(value: Symbol) -> Self {
        match &*value.0 {
            ".." => SubModulePathElement::Up,
            _ => SubModulePathElement::Identifier(value),
        }
    }
}
impl From<SubModulePathElement> for Symbol {
    fn from(value: SubModulePathElement) -> Self {
        match value {
            SubModulePathElement::Up => "..".into(),
            SubModulePathElement::Identifier(symbol) => symbol,
        }
    }
}
