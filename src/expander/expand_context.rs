use std::{cell::RefCell, collections::BTreeSet, rc::Rc};

use crate::ast::{scope::Scope, Ast};

use super::{binding::CompileTimeEnvoirnment, namespace::NameSpace, phase::Phase, Expander};

#[derive(Clone, Copy, Debug)]
pub enum Context {
    Module,
    Expression,
    TopLevel,
}
#[derive(Clone)]
pub struct ExpandContext {
    pub(crate) scopes: BTreeSet<Scope>,
    pub(crate) use_site_scopes: Option<Rc<RefCell<BTreeSet<Scope>>>>,
    pub(crate) module_scopes: BTreeSet<Scope>,
    pub(crate) context: Context,
    pub(crate) phase: Phase,
    pub(crate) namespace: NameSpace,
    pub(crate) env: CompileTimeEnvoirnment,
    pub(crate) only_immediate: bool,
    pub(crate) post_expansion_scope: Option<Scope>,
    pub(crate) module_begin_k: Option<Rc<dyn Fn(&mut Expander, Ast, &ExpandContext)>>,
}

impl std::fmt::Debug for ExpandContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExpandContext")
            .field("scopes", &self.scopes)
            .field("use_site_scopes", &self.use_site_scopes)
            .field("module_scopes", &self.module_scopes)
            .field("context", &self.context)
            .field("phase", &self.phase)
            .field("namespace", &self.namespace)
            .field("env", &self.env)
            .field("only_immediate", &self.only_immediate)
            .field("post_expansion_scope", &self.post_expansion_scope)
            .finish()
    }
}

impl ExpandContext {
    pub fn new(namespace: NameSpace) -> Self {
        Self {
            use_site_scopes: None,
            module_scopes: BTreeSet::from([namespace.scope.clone()]),
            namespace,
            env: CompileTimeEnvoirnment::new(),
            only_immediate: false,
            post_expansion_scope: None,
            scopes: BTreeSet::new(),
            context: Context::TopLevel,
            phase: Phase::Normal(0),
            module_begin_k: None,
        }
    }
}
