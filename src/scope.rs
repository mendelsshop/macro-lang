use std::collections::BTreeSet;

use crate::{syntax::Syntax, Ast, Binding, Expander, Symbol};

pub type ScopeSet = BTreeSet<Scope>;
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Scope(pub usize);
pub trait AdjustScope: Sized {
    fn adjust_scope(self, other_scope: Scope, operation: fn(ScopeSet, Scope) -> ScopeSet) -> Self;

    fn add_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(other_scope, |mut scopes, other_scope| {
            scopes.insert(other_scope);
            scopes
        })
    }

    fn flip_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(other_scope, |mut scopes, other_scope| {
            if !scopes.remove(&other_scope) {
                scopes.insert(other_scope);
            }
            scopes
        })
    }
}
impl AdjustScope for Syntax<Ast> {
    fn adjust_scope(
        self,
        other_scope_set: Scope,
        operation: fn(ScopeSet, Scope) -> ScopeSet,
    ) -> Self {
        Self(
            self.0.adjust_scope(other_scope_set, operation),
            operation(self.1, other_scope_set),
        )
    }
}
impl AdjustScope for Syntax<Symbol> {
    fn adjust_scope(
        self,
        other_scope_set: Scope,
        operation: fn(ScopeSet, Scope) -> ScopeSet,
    ) -> Self {
        Self(self.0, operation(self.1, other_scope_set))
    }
}
impl AdjustScope for Ast {
    fn adjust_scope(
        self,
        other_scope: Scope,
        operation: fn(ScopeSet, Scope) -> BTreeSet<Scope>,
    ) -> Self {
        match self {
            list if list.list() => list
                .map(|x| Ok(x.adjust_scope(other_scope, operation)))
                .unwrap_or(list),
            Self::Syntax(s) => Self::Syntax(Box::new(s.adjust_scope(other_scope, operation))),
            _ => self,
        }
    }
}

impl Expander {
    // we could take a plain syntax<symbol> here to
    pub fn add_binding(&mut self, id: Syntax<Symbol>, binding: Binding) {
        self.all_bindings.insert(id, binding);
    }
    pub fn resolve(&self, id: &Syntax<Symbol>) -> Result<&Binding, String> {
        let candidate_ids = self.find_all_matching_bindings(id);
        let id = candidate_ids
            .clone()
            .max_by_key(|id| id.1.len())
            .ok_or(format!("free variable {id:?}"))?;
        if check_unambiguous(id, candidate_ids) {
            self.all_bindings
                .get(id)
                .ok_or(format!("free variable {}", id.0 .0))
        } else {
            Err(format!("ambiguous binding {}", id.0 .0))
        }
    }
    fn find_all_matching_bindings<'a>(
        &'a self,
        id: &'a Syntax<Symbol>,
    ) -> impl Iterator<Item = &Syntax<Symbol>> + Clone + 'a {
        self.all_bindings
            .keys()
            .filter(move |c_id| c_id.0 == id.0 && c_id.1.is_subset(&id.1))
    }
}
// TODO: return error if ambiguous
// or maybe return error in resolve, instead of option
fn check_unambiguous<'a>(
    id: &Syntax<Symbol>,
    mut candidate_ids: impl Iterator<Item = &'a Syntax<Symbol>>,
) -> bool {
    candidate_ids.all(|c_id| c_id.1.is_subset(&id.1))
}
