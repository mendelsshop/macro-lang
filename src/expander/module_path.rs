use std::{iter, path::Path, rc::Rc};

use itertools::Itertools;

use crate::ast::Symbol;

#[derive(Debug)]
pub enum ModulePath {
    Root(RootModulePath),
    /// if the type is Up, then the list of submod path elements also includes the first Up
    /// (from the type) because a submod path element can also be an up
    Submodule(SubModuleType, Rc<[SubModulePathElement]>),
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
            ModulePath::Root(root_module_path) => todo!(),
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
pub enum LibraryRelativePath {
    Slashed(Rc<str>, Rc<str>),
    Single(Rc<str>),
}
#[derive(Debug)]
pub enum RootModulePath {
    Lib(LibraryRelativePath, Rc<[LibraryRelativePath]>),
    Identifier(Symbol),
    File(Rc<Path>),
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
