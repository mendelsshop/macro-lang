use crate::ast::scope::Scope;

use super::{binding::CompileTimeEnvoirnment, namespace::NameSpace};

pub struct ExpandContext {
    // TODO: maybe use set/btreeset
    use_site_scopes: Option<Vec<Scope>>,
    namespace: NameSpace,
    env: CompileTimeEnvoirnment,
    only_immediate: bool,
    post_expansion_scope: Option<Scope>,
}

impl ExpandContext {
    pub fn new(namespace: NameSpace) -> Self {
        Self {
            use_site_scopes: None,
            namespace,
            env: CompileTimeEnvoirnment::new(),
            only_immediate: false,
            post_expansion_scope: None,
        }
    }
}
