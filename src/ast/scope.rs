use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    hash::Hash,
    rc::Rc,
};

use itertools::Itertools;

use crate::expander::{binding::Binding, phase::Phase, Expander};

use super::{syntax::Syntax, Ast, Pair, Symbol};

pub type MutableMap<K, V> = Rc<RefCell<BTreeMap<K, V>>>;
pub type ScopeSet = BTreeSet<Scope>;
#[derive(Clone, PartialEq)]
pub struct ScopeData(
    pub usize,
    pub MutableMap<Symbol, BTreeMap<ScopeSet, Binding>>,
);
#[derive(Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Representative(pub ScopeData, pub MultiScope, pub Phase);

pub enum ScopeNoMultiScope {
    Simple(ScopeData),
    Representative(Representative),
}
#[derive(Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Scope {
    Simple(ScopeData),
    Representative(Representative),
    ShiftedMultiScope(Phase, MultiScope),
}
impl Scope {
    pub fn generalize_scope(self) -> Self {
        match self {
            Scope::Representative(Representative(_, scope, phase)) => {
                Scope::ShiftedMultiScope(phase, scope)
            }
            _ => self,
        }
    }
}
impl Expander {
    pub fn multi_scope_to_scope_at_phase(
        &mut self,
        multi_scope: MultiScope,
        phase: Phase,
    ) -> ScopeNoMultiScope {
        ScopeNoMultiScope::Representative({
            let this = multi_scope.0.borrow().get(&phase).cloned();
            match this {
                Some(x) => x,
                None => {
                    let s = Representative(
                        ScopeData(self.scope_creator.next(), MutableMap::default()),
                        multi_scope.clone(),
                        phase.clone(),
                    )
                    .clone();
                    multi_scope.0.borrow_mut().insert(phase, s.clone());
                    s
                }
            }
        })
    }
}
#[derive(Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct MultiScope(pub(crate) MutableMap<Phase, Representative>);

// refcell cannot be hashed correctly https://users.rust-lang.org/t/hashmap-keyed-by-rc-refcell/33210/14
// anywhere where hashing matters the hashing will be done by other fields
impl Hash for MultiScope {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl std::fmt::Debug for ScopeData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Scope")
            .field(&self.0)
            .field(&self.1.borrow().keys().collect::<BTreeSet<_>>())
            .finish()
    }
}

impl Scope {
    pub fn scope_greater_than(&self, other: &Self) -> bool {
        self > other
    }
}

impl Ord for ScopeData {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl Eq for ScopeData {}

impl PartialOrd for ScopeData {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl std::hash::Hash for ScopeData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
pub trait AdjustScope: Sized {
    fn adjust_scope(self, other_scope: Scope, operation: fn(ScopeSet, Scope) -> ScopeSet) -> Self;

    fn add_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(other_scope.generalize_scope(), |mut scopes, other_scope| {
            scopes.insert(other_scope);
            scopes
        })
    }

    fn flip_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(other_scope.generalize_scope(), |mut scopes, other_scope| {
            if !scopes.remove(&other_scope) {
                scopes.insert(other_scope);
            }
            scopes
        })
    }

    fn remove_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(other_scope.generalize_scope(), |mut scopes, other_scope| {
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
            if let Scope::ShiftedMultiScope(_, _) = other_scope_set {
                self.1
            } else {
                operation(self.1, other_scope_set.clone())
            },
            if let Scope::ShiftedMultiScope(_, _) = other_scope_set {
                operation(self.2, other_scope_set.clone())
            } else {
                self.2
            },
            self.3,
            self.4,
        )
    }
}
impl AdjustScope for Syntax<Symbol> {
    fn adjust_scope(
        self,
        other_scope_set: Scope,
        operation: fn(ScopeSet, Scope) -> ScopeSet,
    ) -> Self {
        Self(
            self.0,
            if let Scope::ShiftedMultiScope(_, _) = other_scope_set {
                self.1
            } else {
                operation(self.1, other_scope_set.clone())
            },
            if let Scope::ShiftedMultiScope(_, _) = other_scope_set {
                operation(self.2, other_scope_set.clone())
            } else {
                self.2
            },
            self.3,
            self.4,
        )
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
                    .or_default()
                    .insert(scopes, binding);
            })
    }
    pub fn add_binding(id: Syntax<Symbol>, phase: Phase, binding: Binding) -> Result<(), String> {
        Self::add_binding_in_scope(id.1, id.0, binding)
    }
    /// exactly by default should be false
    pub fn resolve(
        &self,
        id: &Syntax<Symbol>,
        phase: Phase,
        exactly: bool,
    ) -> Result<Binding, String> {
        let candidate_ids = self.find_all_matching_bindings(id, &id.1);
        let max_candidate = candidate_ids
            .clone()
            .max_by_key(|id| id.0.len())
            .filter(|max_candidate: &(BTreeSet<Scope>, Binding)| {
                !exactly || max_candidate.0.len() == id.1.len()
            })
            .ok_or(format!("free variable {id:?}"))?;
        if check_unambiguous(&max_candidate, candidate_ids) {
            Ok(max_candidate.1)
        } else {
            Err(format!("ambiguous binding {id:?}"))
        }
    }

    fn find_all_matching_bindings<'a>(
        &'a self,
        id: &'a Syntax<Symbol>,
        scopes: &'a BTreeSet<Scope>,
    ) -> impl Iterator<Item = (BTreeSet<Scope>, Binding)> + Clone + 'a {
        all_bindings(scopes, id)
            // hacky way to get it to be clonable
            .flat_map(|x| x.into_iter().collect_vec())
            .filter(move |c_id| c_id.0.is_subset(scopes))
    }
}

fn all_bindings<'a>(
    scopes: &'a BTreeSet<Scope>,
    id: &'a Syntax<Symbol>,
) -> impl Iterator<Item = BTreeMap<BTreeSet<Scope>, Binding>> + Clone + 'a {
    scopes
        .iter()
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
