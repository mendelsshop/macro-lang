use std::{
    cell::{Ref, RefCell},
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
    pub MutableMap<Symbol, BTreeMap<BTreeSet<ScopeNoMultiScope>, Binding>>,
);
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Representative(pub ScopeData, pub MultiScope, pub Phase);

#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ScopeNoMultiScope {
    Simple(ScopeData),
    Representative(Representative),
}
impl ScopeNoMultiScope {
    fn scope_bindings(&self) -> MutableMap<Symbol, BTreeMap<BTreeSet<ScopeNoMultiScope>, Binding>> {
        match self {
            Self::Simple(scope_data) => Rc::clone(&scope_data.1),
            Self::Representative(representative) => Rc::clone(&representative.0 .1),
        }
    }

    pub fn get<'a>(
        &'a self,
        key: &'a Symbol,
    ) -> Option<Ref<'a, BTreeMap<BTreeSet<ScopeNoMultiScope>, Binding>>> {
        match self {
            Self::Simple(scope_data) => {
                Ref::filter_map(scope_data.1.borrow(), |map| map.get(key)).ok()
            }
            Self::Representative(representative) => {
                Ref::filter_map(representative.0 .1.borrow(), |map| map.get(key)).ok()
            }
        }
    }
}
#[derive(Clone, PartialEq, Eq, Ord, PartialOrd, Hash, Debug)]
pub struct ShiftedMultiScope(pub Phase, pub MultiScope);

#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Scope {
    Simple(ScopeNoMultiScope),
    ShiftedMultiScope(ShiftedMultiScope),
}
impl Scope {
    pub fn generalize_scope(self) -> Self {
        match self {
            Self::Simple(ScopeNoMultiScope::Representative(Representative(_, scope, phase))) => {
                Scope::ShiftedMultiScope(ShiftedMultiScope(phase, scope))
            }
            _ => self,
        }
    }
    pub fn scope_greater_than(&self, other: &Self) -> bool {
        self > other
    }
}
#[derive(Clone, PartialEq, Eq, Ord, PartialOrd, Debug)]
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
macro_rules! operation {
    ($gensym:ident,|mut $set:ident, $scope:ident| $e:expr) => {{
        #[derive(Clone, Copy)]
        struct $gensym;
        impl Operation for $gensym {
            fn operation<T: Ord>(mut $set: BTreeSet<T>, $scope: T) -> BTreeSet<T> {
                $e
            }
        }
        $gensym
    }};
    (|mut $set:ident, $scope:ident|$e:expr) => {
        gensym::gensym!(operation!(|mut $set, $scope| $e))
    };
}
// to get around rust type system limits on being rank1 polymorphic
pub trait Operation {
    fn operation<T: Ord>(_: BTreeSet<T>, e: T) -> BTreeSet<T>;
}
pub trait AdjustScope: Sized {
    fn adjust_scope<O: Operation + Copy>(self, other_scope: Scope, operation: O) -> Self;

    fn add_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(
            other_scope.generalize_scope(),
            operation!(|mut scopes, other_scope| {
                scopes.insert(other_scope);
                scopes
            }),
        )
    }

    fn flip_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(
            other_scope.generalize_scope(),
            operation!(|mut scopes, other_scope| {
                if !scopes.remove(&other_scope) {
                    scopes.insert(other_scope);
                }
                scopes
            }),
        )
    }

    fn remove_scope(self, other_scope: Scope) -> Self {
        self.adjust_scope(
            other_scope.generalize_scope(),
            operation!(|mut scopes, other_scope| {
                scopes.remove(&other_scope);
                scopes
            }),
        )
    }
    fn remove_scopes(self, other_scopes: BTreeSet<Scope>) -> Self {
        other_scopes
            .into_iter()
            .fold(self, AdjustScope::remove_scope)
    }
}
impl AdjustScope for Syntax<Ast> {
    fn adjust_scope<O: Operation + Copy>(self, other_scope_set: Scope, operation: O) -> Self {
        Self(
            self.0.adjust_scope(other_scope_set.clone(), operation),
            match other_scope_set {
                Scope::ShiftedMultiScope(ShiftedMultiScope(_, _)) => self.1,
                Scope::Simple(ref s) => O::operation(self.1, s.clone()),
            },
            if let Scope::ShiftedMultiScope(other_scope_set) = other_scope_set {
                O::operation(self.2, other_scope_set)
            } else {
                self.2
            },
            self.3,
            self.4,
        )
    }
}
impl AdjustScope for Syntax<Symbol> {
    fn adjust_scope<O: Operation + Copy>(self, other_scope_set: Scope, _: O) -> Self {
        Self(
            self.0,
            match other_scope_set {
                Scope::ShiftedMultiScope(ShiftedMultiScope(_, _)) => self.1,
                Scope::Simple(ref s) => O::operation(self.1, s.clone()),
            },
            if let Scope::ShiftedMultiScope(other_scope_set) = other_scope_set {
                O::operation(self.2, other_scope_set)
            } else {
                self.2
            },
            self.3,
            self.4,
        )
    }
}
impl AdjustScope for Ast {
    fn adjust_scope<O: Operation + Copy>(self, other_scope: Scope, operation: O) -> Self {
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
    fn multi_scope_to_scope_at_phase(
        &mut self,
        multi_scope: &MultiScope,
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
    fn syntax_scope_set<T>(&mut self, s: Syntax<T>, phase: Phase) -> BTreeSet<ScopeNoMultiScope> {
        let scopes = s.1;
        let multi_scope = s.2;
        multi_scope.into_iter().fold(scopes, |mut scopes, sms| {
            scopes.insert(self.multi_scope_to_scope_at_phase(&sms.1, sms.0 - phase));
            scopes
        })
    }
    // doesn't take an owned value but has to do a lot of copying is this better than just straight
    // up cloning
    // also cannot nest one in another k
    fn syntax_scope_set_ref<T, U>(
        &mut self,
        s: &Syntax<T>,
        phase: Phase,
        k: impl FnOnce(&mut Self, BTreeSet<&ScopeNoMultiScope>) -> U,
    ) -> U {
        let multi_scopes: Vec<_> =
            s.2.iter()
                .map(|sms| (self.multi_scope_to_scope_at_phase(&sms.1, sms.0 - phase)))
                .collect();
        let scopes: BTreeSet<&ScopeNoMultiScope> =
            BTreeSet::from_iter(s.1.iter().chain(multi_scopes.iter()));
        k(self, scopes)
    }
    pub fn add_binding_in_scope(
        scopes: BTreeSet<ScopeNoMultiScope>,
        sym: Symbol,
        binding: Binding,
    ) -> Result<(), String> {
        scopes
            .clone()
            .into_iter()
            .max()
            .ok_or("cannot bind in empty scope set".to_string())
            .map(|max_scope| {
                let bindings = max_scope.scope_bindings();
                bindings
                    .borrow_mut()
                    .entry(sym)
                    .or_default()
                    .insert(scopes, binding);
            })
    }
    pub fn add_binding(
        &mut self,
        id: Syntax<Symbol>,
        phase: Phase,
        binding: Binding,
    ) -> Result<(), String> {
        let ident = id.0.clone();
        Self::add_binding_in_scope(self.syntax_scope_set(id, phase), ident, binding)
    }
    /// exactly by default should be false
    pub fn resolve(
        &mut self,
        id: Syntax<Symbol>,
        phase: Phase,
        exactly: bool,
    ) -> Result<Binding, String> {
        let sym = id.0.clone();
        let scopes = self.syntax_scope_set(id, phase);
        let candidate_ids = self.find_all_matching_bindings(&sym, &scopes);
        let max_candidate = candidate_ids
            .clone()
            .max_by_key(|id| id.0.len())
            .filter(|max_candidate: &(BTreeSet<ScopeNoMultiScope>, Binding)| {
                !exactly || max_candidate.0.len() == scopes.len()
            })
            .ok_or(format!("free variable {sym:?}"))?;
        if check_unambiguous(&max_candidate, candidate_ids) {
            Ok(max_candidate.1)
        } else {
            Err(format!("ambiguous binding {sym:?}"))
        }
    }

    fn find_all_matching_bindings<'a>(
        &'a self,
        id: &'a Symbol,
        scopes: &'a BTreeSet<ScopeNoMultiScope>,
    ) -> impl DoubleEndedIterator<Item = (BTreeSet<ScopeNoMultiScope>, Binding)> + use<'a> + Clone
    {
        scopes
            .into_iter()
            .filter_map(move |sc| sc.get(id))
            // hacky way to get it to be clonable
            .flat_map(|x| x.clone().into_iter().collect_vec())
            .filter(move |c_id| c_id.0.is_subset(scopes))
    }
}

// TODO: return error if ambiguous
// or maybe return error in resolve, instead of option
fn check_unambiguous<'a>(
    max_candidate: &(BTreeSet<ScopeNoMultiScope>, Binding),
    mut candidate_ids: impl Iterator<Item = (BTreeSet<ScopeNoMultiScope>, Binding)>,
) -> bool {
    candidate_ids.all(|c_id| c_id.0.is_subset(&max_candidate.0))
}
impl Expander {
    pub fn bound_identifier<T>(
        &mut self,
        syntax: &Syntax<T>,
        other: &Syntax<T>,
        phase: Phase,
    ) -> bool
    where
        T: PartialEq,
    {
        syntax.0 == other.0
            && self.syntax_scope_set_ref(syntax, phase, |this, scopes| {
                this.syntax_scope_set_ref(other, phase, |_, other_scopes| scopes == other_scopes)
            })
    }
}
