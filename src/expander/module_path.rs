use std::{path::Path, rc::Rc};

use crate::ast::Symbol;

pub enum ModulePath {
    Root(RootModulePath),
    Submodule(SubModuleType, Rc<[SubModulePathElement]>),
}

pub enum SubModuleType {
    Root(RootModulePath),
    Current,
    Up,
}
pub enum LibraryRelativePath {
    Slashed(Rc<str>, Rc<str>),
    Single(Rc<str>),
}
pub enum RootModulePath {
    Lib(LibraryRelativePath, Rc<[LibraryRelativePath]>),
    Identifier(Symbol),
    File(Rc<Path>),
}

pub enum SubModulePathElement {
    Up,
    Identifier(Symbol),
}
