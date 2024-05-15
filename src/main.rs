#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![deny(clippy::use_self, rust_2018_idioms, clippy::missing_panics_doc)]
use core::panic;
use std::collections::HashMap;
use std::fmt;
use std::{collections::BTreeSet, rc::Rc};

type Ident = Rc<str>;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Scope(usize);
#[derive(Debug)]
struct ScopeCreator(usize);

impl ScopeCreator {
    fn new() -> Self {
        Self(0)
    }

    fn new_scope(&mut self) -> Scope {
        let scope = Scope(self.0);
        self.0 += 1;
        scope
    }
}

type ScopeSet = BTreeSet<Scope>;
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
struct Syntax(Ident, ScopeSet);

trait AdjustScope: Sized {
    fn adjust_scope(
        self,
        other_scope: Scope,
        operation: fn(ScopeSet, Scope) -> BTreeSet<Scope>,
    ) -> Self;

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

impl Syntax {
    fn new(symbol: Rc<str>) -> Self {
        Self(symbol, BTreeSet::new())
    }
}

impl AdjustScope for Syntax {
    fn adjust_scope(
        self,
        other_scope_set: Scope,
        operation: fn(ScopeSet, Scope) -> BTreeSet<Scope>,
    ) -> Self {
        Self(self.0, operation(self.1, other_scope_set))
    }
}

#[derive(Clone, PartialEq, Debug)]
enum Ast {
    List(Vec<Ast>),
    Syntax(Syntax),
    Number(f64),
    Symbol(Symbol),
}

impl Ast {
    fn datum_to_syntax(self) -> Self {
        match self {
            Self::List(l) => Self::List(l.into_iter().map(Self::datum_to_syntax).collect()),
            Self::Syntax(_) => self,
            Self::Symbol(Symbol(s, _)) => Self::Syntax(Syntax::new(s)),
            _ => self,
        }
    }
    fn syntax_to_datum(self) -> Self {
        match self {
            Self::List(l) => Self::List(l.into_iter().map(Self::syntax_to_datum).collect()),
            Self::Syntax(Syntax(s, _)) => Self::Symbol(Symbol(s, 0)),
            _ => self,
        }
    }
    fn identifier(&self) -> bool {
        matches!(self, Self::Syntax(_))
    }
}

impl AdjustScope for Ast {
    fn adjust_scope(
        self,
        other_scope: Scope,
        operation: fn(ScopeSet, Scope) -> BTreeSet<Scope>,
    ) -> Self {
        match self {
            Self::List(l) => Self::List(
                l.into_iter()
                    .map(|e| e.adjust_scope(other_scope, operation))
                    .collect(),
            ),
            Self::Syntax(s) => Self::Syntax(s.adjust_scope(other_scope, operation)),
            _ => self,
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum Binding {
    Lambda,
    LetSyntax,
    Quote,
    QuoteSyntax,
    // DatumToSyntax,
    // SyntaxToDatum,
    // SyntaxE,
    // List,
    // Cons,
    // Car,
    // Cdr,
    // Map,
    Variable(Symbol),
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Variable(Symbol(s, i)) => format!("{s}{i}"),
                Self::Lambda => "lambda".to_string(),
                Self::LetSyntax => "let-syntax".to_string(),
                Self::Quote => "quote".to_string(),
                Self::QuoteSyntax => "quote-syntax".to_string(),
                // Self::DatumToSyntax => "datum->syntax".to_owned(),
                // Self::SyntaxToDatum => "syntax->datum".to_owned(),
                // Self::SyntaxE => "syntax-e".to_string(),
                // Self::List => "list".to_string(),
                // Self::Cons => "cons".to_string(),
                // Self::Car => "car".to_string(),
                // Self::Cdr => "cdr".to_string(),
                // Self::Map => "map".to_string(),
            }
        )
    }
}

#[derive(Debug)]
pub struct Expander<T> {
    all_bindings: HashMap<Syntax, T>,
    core_forms: BTreeSet<Binding>,
    core_primitives: BTreeSet<Binding>,
    core_scope: Scope,
    scope_creator: ScopeCreator,
    symbol_count: usize,
}

impl Default for Expander<Binding> {
    fn default() -> Self {
        Self::new()
    }
}

impl Expander<Binding> {
    #[must_use]
    pub fn new() -> Self {
        let mut scope_creator = ScopeCreator::new();
        let core_scope = scope_creator.new_scope();
        let core_forms = BTreeSet::from([
            Binding::Lambda,
            Binding::LetSyntax,
            Binding::Quote,
            Binding::QuoteSyntax,
        ]);
        let core_primitives = BTreeSet::from([]);
        let mut this = Self {
            scope_creator,
            core_scope,
            core_primitives,
            core_forms,
            all_bindings: HashMap::new(),
            symbol_count: 0,
        };
        this.core_forms
            .clone()
            .union(&this.core_primitives.clone())
            .for_each(|core| {
                this.add_binding(
                    Syntax(core.to_string().into(), BTreeSet::from([this.core_scope])),
                    core.clone(),
                );
            });
        this
    }
    fn add_binding(&mut self, id: Syntax, binding: Binding) {
        self.all_bindings.insert(id, binding);
    }

    fn add_local_binding(&mut self, id: Syntax) -> Symbol {
        let symbol = Symbol(id.0.clone(), self.symbol_count);
        self.add_binding(id, Binding::Variable(symbol.clone()));
        symbol
    }

    fn resolve(&self, id: &Syntax) -> Option<&Binding> {
        let candidate_ids = self.find_all_matching_bindings(id);
        candidate_ids
            .clone()
            .max_by_key(|id| id.1.len())
            .filter(|id| check_unambiguous(id, candidate_ids))
            .and_then(|id| self.all_bindings.get(id))
    }

    fn find_all_matching_bindings<'a>(
        &'a self,
        id: &'a Syntax,
    ) -> impl Iterator<Item = &Syntax> + Clone + 'a {
        self.all_bindings
            .keys()
            .filter(move |c_id| c_id.0 == id.0 && c_id.1.is_subset(&id.1))
    }

    fn introduce<T: AdjustScope>(&self, s: T) -> T {
        s.add_scope(self.core_scope)
    }

    pub fn expand(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        match s {
            Ast::List(l) if matches!(&l[..], [Ast::Syntax(_), ..]) => {
                self.expand_id_application_form(l, env)
            }
            Ast::Syntax(s) => self.expand_identifier(s, env),
            Ast::Number(_) => todo!(),
            Ast::Symbol(_) => todo!(),
            Ast::List(_) => todo!(),
        }
    }

    fn expand_identifier(&self, s: Syntax, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        let binding = self.resolve(&s).ok_or(format!("free variable {}", s.0))?;
        if self.core_forms.contains(binding) {
            Err(format!("bad syntax {}", s.0))
        } else if self.core_primitives.contains(binding) {
            Ok(Ast::Syntax(s))
        } else {
            let Binding::Variable(binding) = binding else {
                panic!()
            };
            let v = env
                .lookup(binding)
                .ok_or(format!("out of context {}", s.0))?;
            if let CompileTimeBinding::Symbol(_) = v {
                Ok(Ast::Syntax(s))
            } else {
                Err(format!("bad syntax {}", s.0))
            }
        }
    }

    // constraints = s.len() > 0
    // constraints = s[0] == Ast::Syntax(_)
    fn expand_id_application_form(
        &mut self,
        s: Vec<Ast>,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let Some(Ast::Syntax(id)) = s.first() else {
            unreachable!()
        };
        let binding = self.resolve(id).ok_or(format!("free variable {}", id.0))?;
        match binding {
            Binding::Lambda => self.expand_lambda(s, env),
            Binding::LetSyntax => self.expand_let_syntax(s, env),
            Binding::Quote | Binding::QuoteSyntax => match &s[..] {
                [_, _] => Ok(Ast::List(s)),
                _ => Err(format!("bad syntax {s:?}")),
            },
            Binding::Variable(binding) => {
                let v = env
                    .lookup(binding)
                    .ok_or(format!("out of context {}", binding.0))?;
                match v {
                    CompileTimeBinding::Symbol(_) => self.expand_app(s, env),
                    CompileTimeBinding::Macro => todo!(),
                }
            }
        }
    }

    fn expand_app(&mut self, s: Vec<Ast>, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        s.into_iter()
            .map(|sub_s| self.expand(sub_s, env.clone()))
            .collect::<Result<Vec<_>, _>>()
            .map(Ast::List)
    }

    fn expand_lambda(&mut self, s: Vec<Ast>, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        let [lambda_id, Ast::List(arg), body] = &s[..] else {
            Err(format!("invalid syntax {s:?}"))?
        };
        let [Ast::Syntax(arg_id)] = &arg[..] else {
            Err(format!("invalid syntax {s:?}"))?
        };
        let sc = self.scope_creator.new_scope();
        let id = arg_id.clone().add_scope(sc);
        let binding = self.add_local_binding(id.clone());
        let body_env = env.extend(binding.clone(), CompileTimeBinding::Symbol(binding));
        let exp_body = self.expand(body.clone().add_scope(sc), body_env)?;
        Ok(Ast::List(vec![
            lambda_id.clone(),
            Ast::List(vec![Ast::Syntax(id)]),
            exp_body,
        ]))
    }

    fn expand_let_syntax(
        &mut self,
        s: Vec<Ast>,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let [_let_syntax_id, Ast::List(arg), body] = &s[..] else {
            Err(format!("invalid syntax {s:?}"))?
        };
        let [Ast::Syntax(lhs_id), rhs] = &arg[..] else {
            Err(format!("invalid syntax {s:?}"))?
        };
        let sc = self.scope_creator.new_scope();
        let id = lhs_id.clone().add_scope(sc);
        let binding = self.add_local_binding(id);
        let rhs_val = self.eval_for_syntax_binding(rhs.clone())?;
        let body_env = env.extend(binding, rhs_val);
        self.expand(body.clone().add_scope(sc), body_env)
    }

    fn eval_for_syntax_binding(&mut self, rhs: Ast) -> Result<CompileTimeBinding, String> {
        let var_name = format!("problem `evaluating` macro {rhs:?}");
        let expand = self.expand(rhs, CompileTimeEnvoirnment::new());
        Ok(self.eval_compiled(self.compile(expand?).ok_or(var_name)?))
    }

    fn compile(&self, rhs: Ast) -> Option<Ast> {
        match rhs {
            Ast::List(l) => {
                let s = l.first()?;
                let core_sym = if let Ast::Syntax(s) = s {
                    self.resolve(s)
                } else {
                    None
                };
                match core_sym {
                    Some(Binding::Lambda) => {
                        let [_, Ast::List(arg), body] = &l[..] else {
                            None?
                        };
                        let [Ast::Syntax(id)] = &arg[..] else { None? };
                        let Binding::Variable(id) = self.resolve(id)? else {
                            None?
                        };
                        Some(Ast::List(vec![
                            Ast::Symbol(Symbol("lambda".into(), 0)),
                            Ast::List(vec![Ast::Symbol(id.clone())]),
                            self.compile(body.clone())?,
                        ]))
                    }
                    Some(Binding::Quote) => {
                        if let [_, datum] = &l[..] {
                            Some(Ast::List(vec![
                                Ast::Symbol(Symbol("quote".into(), 0)),
                                datum.clone().syntax_to_datum(),
                            ]))
                        } else {
                            None
                        }
                    }
                    Some(Binding::QuoteSyntax) => {
                        if let [_, datum] = &l[..] {
                            Some(Ast::List(vec![
                                Ast::Symbol(Symbol("quote".into(), 0)),
                                datum.clone(),
                            ]))
                        } else {
                            None
                        }
                    }
                    _ => Some(Ast::List(
                        l.into_iter()
                            .map(|e| self.compile(e))
                            .collect::<Option<Vec<_>>>()?,
                    )),
                }
            }
            Ast::Syntax(s) => {
                if let Binding::Variable(s) = self.resolve(&s)? {
                    Some(Ast::Symbol(s.clone()))
                } else {
                    None
                }
            }
            Ast::Number(_) => Some(rhs),
            Ast::Symbol(_) => todo!(),
        }
    }

    fn eval_compiled(&self, new: Ast) -> CompileTimeBinding {
        todo!()
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Symbol(pub Rc<str>, pub usize);

#[derive(Clone)]
pub enum CompileTimeBinding {
    Symbol(Symbol),
    Macro,
}

#[derive(Clone)]
struct CompileTimeEnvoirnment(HashMap<Symbol, CompileTimeBinding>);

impl CompileTimeEnvoirnment {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn extend(&self, key: Symbol, value: CompileTimeBinding) -> Self {
        let mut map = self.0.clone();
        map.insert(key, value);
        Self(map)
    }

    fn lookup(&self, key: &Symbol) -> Option<CompileTimeBinding> {
        self.0.get(key).cloned()
    }
}

// TODO: return error if ambiguous
// or maybe return error in resolve, instead of option
fn check_unambiguous<'a>(id: &Syntax, mut candidate_ids: impl Iterator<Item = &'a Syntax>) -> bool {
    candidate_ids.all(|c_id| c_id.1.is_subset(&id.1))
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::{AdjustScope, Ast, Binding, Expander, Scope, ScopeCreator, Symbol, Syntax};

    #[test]
    fn identifier_test_with_empty_syntax() {
        assert!(Ast::Syntax(Syntax::new("a".into())).identifier());
    }

    #[test]
    fn datum_to_syntax_with_identifier() {
        assert_eq!(
            Ast::Symbol(Symbol("a".into(), 0)).datum_to_syntax(),
            Ast::Syntax(Syntax("a".into(), BTreeSet::new()))
        );
    }

    #[test]
    fn datum_to_syntax_with_number() {
        assert_eq!(Ast::Number(1.0).datum_to_syntax(), Ast::Number(1.0));
    }

    #[test]
    fn datum_to_syntax_with_list() {
        assert_eq!(
            Ast::List(vec![
                Ast::Symbol(Symbol("a".into(), 0)),
                Ast::Symbol(Symbol("b".into(), 0)),
                Ast::Symbol(Symbol("c".into(), 0)),
            ])
            .datum_to_syntax(),
            Ast::List(vec![
                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("b".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
            ])
        );
    }

    #[test]
    fn datum_to_syntax_with_list_and_syntax() {
        assert_eq!(
            Ast::List(vec![
                Ast::Symbol(Symbol("a".into(), 0)),
                Ast::Syntax(Syntax("b".into(), BTreeSet::from([Scope(0), Scope(1)]))),
                Ast::Symbol(Symbol("c".into(), 0)),
            ])
            .datum_to_syntax(),
            Ast::List(vec![
                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("b".into(), BTreeSet::from([Scope(0), Scope(1)]))),
                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
            ])
        );
    }
    #[test]
    fn syntax_to_datum_with_identifier() {
        assert_eq!(
            Ast::Syntax(Syntax("a".into(), BTreeSet::new())).syntax_to_datum(),
            Ast::Symbol(Symbol("a".into(), 0)),
        );
    }

    #[test]
    fn syntax_to_datum_with_number() {
        assert_eq!(Ast::Number(1.0).syntax_to_datum(), Ast::Number(1.0));
    }

    #[test]
    fn syntax_to_datum_with_list() {
        assert_eq!(
            Ast::List(vec![
                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("b".into(), BTreeSet::new())),
                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
            ])
            .syntax_to_datum(),
            Ast::List(vec![
                Ast::Symbol(Symbol("a".into(), 0)),
                Ast::Symbol(Symbol("b".into(), 0)),
                Ast::Symbol(Symbol("c".into(), 0)),
            ])
        );
    }

    #[test]
    fn scope_equality_test() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_ne!(sc1, sc2);
        assert_eq!(sc2, sc2);
    }

    #[test]
    fn add_scope_test_empty_scope() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), BTreeSet::new())).add_scope(sc1),
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1])))
        );
    }

    #[test]
    fn add_scope_test_empty_scope_list() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        assert_eq!(
            Ast::List(vec![
                Ast::Symbol(Symbol("x".into(), 0)),
                Ast::Symbol(Symbol("y".into(), 0)),
            ])
            .datum_to_syntax()
            .add_scope(sc1),
            Ast::List(vec![
                Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))),
                Ast::Syntax(Syntax("y".into(), BTreeSet::from([sc1]))),
            ])
        );
    }

    #[test]
    fn add_scope_test_non_empty_scope() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).add_scope(sc2),
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2])))
        );
    }

    #[test]
    fn add_scope_test_add_duplicate() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).add_scope(sc1),
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1,])))
        );
    }

    #[test]
    fn flip_scope_test_different() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).flip_scope(sc2),
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2])))
        );
    }

    #[test]
    fn flip_scope_test_same() {
        let mut scope_creator = ScopeCreator::new();
        let sc1 = scope_creator.new_scope();
        let sc2 = scope_creator.new_scope();
        assert_eq!(
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2]))).flip_scope(sc2),
            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1,])))
        );
    }

    #[test]
    fn resolve_test_lambda_empty() {
        let expander = Expander::new();

        assert_eq!(
            expander.resolve(&Syntax("lambda".into(), BTreeSet::new())),
            None
        );
    }

    #[test]
    fn resolve_test_lambda_core() {
        let expander = Expander::new();

        println!("{expander:?}");
        assert_eq!(
            expander.resolve(&expander.introduce(Syntax("lambda".into(), BTreeSet::new()))),
            Some(Binding::Lambda).as_ref()
        );
    }
}
