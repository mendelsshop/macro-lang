use std::collections::HashMap;

use crate::{syntax::Syntax, Ast, Binding, ScopeSet, Symbol};

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
    fn adjust_scope(self, other_scope: Scope, operation: fn(ScopeSet, Scope) -> ScopeSet) -> Self {
        match self {
            Self::List(l) => Self::List(
                l.into_iter()
                    .map(|e| e.adjust_scope(other_scope, operation))
                    .collect(),
            ),
            Self::Syntax(s) => Self::Syntax(Box::new(s.adjust_scope(other_scope, operation))),
            _ => self,
        }
    }
}
#[derive(Debug)]
pub struct AllBindings(pub HashMap<Syntax<Symbol>, Binding>);

impl AllBindings {
    // we could take a plain syntax<symbol> here to
    pub fn add_binding(
        &mut self,
        id: Syntax<Symbol>,
        binding: Binding,
    )  {
       self.0.insert(id, binding);
    }
    pub fn resolve(&self, id: &Syntax<Symbol>) -> Result<&Binding, String> {
        let candidate_ids = self.find_all_matching_bindings(id);
        let id = candidate_ids
            .clone()
            .max_by_key(|id| id.1.len())
            .ok_or(format!("free variable {:?}", id))?;
        if check_unambiguous(id, candidate_ids) {
            self.0.get(id).ok_or(format!("free variable {}", id.0 .0))
        } else {
            Err(format!("ambiguous binding {}", id.0 .0))
        }
    }
    fn find_all_matching_bindings<'a>(
        &'a self,
        id: &'a Syntax<Symbol>,
    ) -> impl Iterator<Item = &Syntax<Symbol>> + Clone + 'a {
        self.0
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
