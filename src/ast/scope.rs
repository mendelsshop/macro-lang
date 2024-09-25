use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap},
    rc::Rc,
};

use itertools::Itertools;

use crate::expander::{binding::Binding, Expander};

use super::{syntax::Syntax, Ast, Pair, Symbol};

pub type ScopeSet = BTreeSet<Scope>;
#[derive(Clone, PartialEq)]
pub struct Scope(
    pub usize,
    pub Rc<RefCell<HashMap<Symbol, BTreeMap<ScopeSet, Binding>>>>,
);

impl Scope {
    pub fn scope_greater_than(&self, other: &Self) -> bool {
        self > other
    }
}

impl std::fmt::Debug for Scope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Scope").field(&self.0).finish()
    }
}

impl Ord for Scope {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl Eq for Scope {}

impl PartialOrd for Scope {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl std::hash::Hash for Scope {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
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

    fn remove_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(other_scope, |mut scopes, other_scope| {
            scopes.remove(&other_scope);
            scopes
        })
    }
    fn remove_scopes(self, other_scopes: BTreeSet<Scope>) -> Self {
        other_scopes
            .into_iter()
            .fold(self, AdjustScope::remove_scope)
    }
}
impl AdjustScope for Syntax<Ast> {
    fn adjust_scope(
        self,
        other_scope_set: Scope,
        operation: fn(ScopeSet, Scope) -> ScopeSet,
    ) -> Self {
        Self(
            self.0.adjust_scope(other_scope_set.clone(), operation),
            operation(self.1, other_scope_set),
            self.2,
            self.3,
        )
    }
}
impl AdjustScope for Syntax<Symbol> {
    fn adjust_scope(
        self,
        other_scope_set: Scope,
        operation: fn(ScopeSet, Scope) -> ScopeSet,
    ) -> Self {
        Self(self.0, operation(self.1, other_scope_set), self.2, self.3)
    }
}
impl AdjustScope for Ast {
    fn adjust_scope(
        self,
        other_scope: Scope,
        operation: fn(ScopeSet, Scope) -> BTreeSet<Scope>,
    ) -> Self {
        match self {
            Self::Pair(p) => Self::Pair(Box::new(Pair(
                p.0.adjust_scope(other_scope.clone(), operation),
                p.1.adjust_scope(other_scope, operation),
            ))),
            Self::Syntax(s) => Self::Syntax(Box::new(s.adjust_scope(other_scope, operation))),
            _ => self,
        }
    }
}

impl Expander {
    pub fn add_binding_in_scope(
        scopes: BTreeSet<Scope>,
        sym: Symbol,
        binding: Binding,
    ) -> Result<(), String> {
        scopes
            .clone()
            .into_iter()
            .max()
            .ok_or("cannot bind in empty scope set".to_string())
            .map(|max_scope| {
                let bindings = max_scope.1;
                bindings
                    .borrow_mut()
                    .entry(sym)
                    .or_insert(BTreeMap::new())
                    .insert(scopes, binding);
            })
    }
    pub fn add_binding(id: Syntax<Symbol>, binding: Binding) {
        Self::add_binding_in_scope(id.1, id.0, binding);
    }
    pub fn resolve(&self, id: &Syntax<Symbol>, exactly: bool) -> Result<Binding, String> {
        let candidate_ids = self.find_all_matching_bindings(id, &id.1);
        let max_candidate = candidate_ids
            .clone()
            .max_by_key(|id| id.0.len())
            .filter(|max_candidate: &(BTreeSet<Scope>, Binding)| {
                exactly || max_candidate.0.len() == id.1.len()
            })
            .ok_or(format!("free variable {id:?}"))?;
        if check_unambiguous(&max_candidate, candidate_ids) {
            Ok(max_candidate.1)
        } else {
            Err(format!("ambiguous binding {:?}", id))
        }
    }

    fn find_all_matching_bindings<'a>(
        &'a self,
        id: &'a Syntax<Symbol>,
        scopes: &'a BTreeSet<Scope>,
    ) -> impl Iterator<Item = (BTreeSet<Scope>, Binding)> + Clone + 'a {
        all_bindings(scopes, id)
            // hacky way to get it to be clonable
            .map(|x| x.into_iter().collect_vec().into_iter())
            .flatten()
            .filter(move |c_id| scopes.is_subset(&c_id.0))
            .map(|x| x.clone())
    }
}

fn all_bindings<'a>(
    scopes: &'a BTreeSet<Scope>,
    id: &'a Syntax<Symbol>,
) -> impl Iterator<Item = BTreeMap<BTreeSet<Scope>, Binding>> + Clone + 'a {
    scopes
        .into_iter()
        .filter_map(move |sc| sc.1.borrow().get(&id.0).cloned())
}
// TODO: return error if ambiguous
// or maybe return error in resolve, instead of option
fn check_unambiguous<'a>(
    max_candidate: &(BTreeSet<Scope>, Binding),
    mut candidate_ids: impl Iterator<Item = (BTreeSet<Scope>, Binding)>,
) -> bool {
    candidate_ids.all(|c_id| c_id.0.is_subset(&max_candidate.0))
}
