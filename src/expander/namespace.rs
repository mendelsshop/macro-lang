use std::collections::HashMap;

use crate::ast::{Ast, Symbol};

use super::binding::CompileTimeBinding;

pub struct NameSpace {
    pub variables: HashMap<Symbol, Ast>,
    pub transformers: HashMap<Symbol, CompileTimeBinding>,
}
