#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![deny(static_mut_refs)]
#![deny(clippy::use_self, rust_2018_idioms, clippy::missing_panics_doc)]
use std::collections::HashMap;
use std::fmt::{self, Debug};
use std::io::{BufRead, BufReader, Write};
use std::iter::Peekable;
use std::{cell::RefCell, cmp::Ordering};
use std::{collections::BTreeSet, rc::Rc};

use trace::trace;

// use trace::trace;
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Scope(usize);
#[derive(Debug)]
struct UniqueNumberManager(usize);

// static mut UNIQUE_NUMBER_GENERATOR: usize = 1;
// fn unique_number_generator() -> usize {
//     unsafe {
//         let current = UNIQUE_NUMBER_GENERATOR;
//         UNIQUE_NUMBER_GENERATOR += 1;
//         current
//     }
// }
impl UniqueNumberManager {
    fn new() -> Self {
        Self(1)
    }

    fn next(&mut self) -> usize {
        let current = self.0;
        self.0 += 1;
        current
    }

    fn new_scope(&mut self) -> Scope {
        Scope(self.next())
    }

    fn gen_sym(&mut self, name: impl ToString) -> Symbol {
        Symbol(name.to_string().into(), self.next())
    }
}

type ScopeSet = BTreeSet<Scope>;
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Syntax(Symbol, ScopeSet);

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
    #[must_use]
    pub fn new(symbol: Symbol) -> Self {
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

pub type AnalyzedResult = Result<Box<dyn AnalyzeFn>, String>;
pub trait AnalyzeFn: Fn(EnvRef) -> Result<Ast, String> {
    fn clone_box<'a>(&self) -> Box<dyn 'a + AnalyzeFn>
    where
        Self: 'a;
}

impl<F> AnalyzeFn for F
where
    F: Fn(EnvRef) -> Result<Ast, String> + Clone,
{
    fn clone_box<'a>(&self) -> Box<dyn 'a + AnalyzeFn>
    where
        Self: 'a,
    {
        Box::new(self.clone())
    }
}
impl<'a> Clone for Box<dyn 'a + AnalyzeFn> {
    fn clone(&self) -> Self {
        (**self).clone_box()
    }
}

pub trait AnalyzeStateFn: Fn(EnvRef, State) -> Result<Ast, String> {
    fn clone_box<'a>(&self) -> Box<dyn 'a + AnalyzeStateFn>
    where
        Self: 'a;
}

impl<F> AnalyzeStateFn for F
where
    F: Fn(EnvRef, State) -> Result<Ast, String> + Clone,
{
    fn clone_box<'a>(&self) -> Box<dyn 'a + AnalyzeStateFn>
    where
        Self: 'a,
    {
        Box::new(self.clone())
    }
}
impl<'a> Clone for Box<dyn 'a + AnalyzeStateFn> {
    fn clone(&self) -> Self {
        (**self).clone_box()
    }
}
#[derive(Clone, PartialEq, Debug)]
pub enum Function {
    Lambda(Lambda),
    Primitive(Primitive),
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lambda(l) => write!(f, "(lambda {} <body>)", l.2),
            Self::Primitive(_) => write!(f, "(primitive-procedure)"),
        }
    }
}

impl Function {
    fn apply(&self, args: Ast) -> Result<Ast, String> {
        match self {
            Self::Lambda(Lambda(body, env, params)) => {
                let env = Env::extend_envoirnment(env.clone(), params.clone(), args)?;
                body(env)
                //Evaluator::eval_sequence(*body.clone(), env)
            }
            Self::Primitive(p) => p(args),
        }
    }
}

#[derive(Clone)]
pub struct Lambda(Box<dyn AnalyzeFn>, EnvRef, Ast);

impl PartialEq for Lambda {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}
impl fmt::Debug for Lambda {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(lambda {} <body>)", self.2)
    }
}
type Primitive = fn(Ast) -> Result<Ast, String>;
//#[derive(Clone, PartialEq, Debug)]
//pub struct Pair(pub Ast, pub Ast);
//
//impl Pair {
//    pub fn map(&self, mut f: impl FnMut(Ast) -> Result<Ast, String>) -> Result<Ast, String> {
//        let car = f(self.0.clone())?;
//        let cdr = self.1.map(f)?;
//        Ok(AstF::Pair(Box::new(Self(car, cdr))))
//    }
//    #[must_use]
//    pub fn list(&self) -> bool {
//        self.1.list()
//    }
//    #[must_use]
//    pub fn size(&self) -> usize {
//        1 + self.1.size()
//    }
//}

//#[derive(Clone, PartialEq, Debug)]
//pub enum Ast {
//    Pair(Box<Pair>),
//    TheEmptyList,
//    Syntax(Syntax),
//    Number(f64),
//    Symbol(Symbol),
//    Function(Function),
//}

fn bound_identifier(a: Ast, b: Ast) -> bool {
    matches!((*a.out, *b.out), (AstF::Syntax(a), AstF::Syntax(b)) if a == b)
}
//trait Borrowed: Sized {
//    fn catamorphism<A>(self, algebra: &mut impl FnMut(AstF<A>) -> A) -> A {
//        let mapped = self.out.map(|subterm| subterm.catamorphism(algebra));
//        algebra(mapped)
//    }
//    fn hylo<A, B>(
//        term: A,
//        algebra: &mut impl FnMut(AstF<B>) -> B,
//        coalgebra: &mut impl FnMut(A) -> AstF<A>,
//    ) -> B {
//        let unfolded = coalgebra(term);
//        let mapped = unfolded.map(|subterm| Self::hylo(subterm, algebra, coalgebra));
//        algebra(mapped)
//    }
//}
#[derive(Clone, PartialEq, Debug)]
pub struct Ast {
    pub out: Box<AstF<Ast>>,
}
impl Ast {
    #[must_use]
    pub fn new(out: AstF<Self>) -> Self {
        Self { out: Box::new(out) }
    }
    fn zygomorphism<A, B: Clone>(
        self,
        f: &mut impl FnMut(AstF<B>) -> B,
        g: &mut impl FnMut(AstF<(B, A)>) -> A,
    ) -> A {
        self.catamorphism(&mut |term: AstF<(B, A)>| {
            let ast_f = term.map_borrow(|(fst, _)| fst.clone());
            (f(ast_f), g(term))
        })
        .1
    }

    fn catamorphism_borrow<A>(&self, algebra: &mut impl FnMut(&AstF<A>) -> A) -> A {
        let mapped = self
            .out
            .map_borrow(|subterm: &Ast| subterm.catamorphism_borrow(algebra));
        algebra(&mapped)
    }
    pub fn bottom_up(self, f: &mut impl FnMut(Self) -> Self) -> Self {
        // TODO: report bug where inling x results in immutable borrow error
        //let x = self.out.map(|x| Self::bottom_up(x, f));
        //f(Fix::new(Box::new(x)))
        self.catamorphism(&mut |x| f(Self::new(x)))
    }
    pub fn top_down(self, f: &mut impl FnMut(Self) -> Self) -> Self {
        //Fix::new(Box::new(f(self).out.map(|x| x.top_down(f))))
        Self::anamorphism(self, &mut |x| *f(x).out)
    }

    pub fn catamorphism<A>(self, algebra: &mut impl FnMut(AstF<A>) -> A) -> A {
        let mapped = self.out.map(|subterm| subterm.catamorphism(algebra));
        algebra(mapped)
    }
    pub fn paramorphism<A>(self, algebra: &mut impl FnMut(Ast, AstF<A>) -> A) -> A {
        let mapped = self
            .out
            .clone()
            .map(|subterm| subterm.paramorphism(algebra));
        algebra(self, mapped)
    }
    pub fn anamorphism<A>(term: A, coalgebra: &mut impl FnMut(A) -> AstF<A>) -> Self {
        Self::new(coalgebra(term).map(|subterm| Self::anamorphism(subterm, coalgebra)))
    }
    pub fn hylo<A, B>(
        term: A,
        algebra: &mut impl FnMut(AstF<B>) -> B,
        coalgebra: &mut impl FnMut(A) -> AstF<A>,
    ) -> B {
        let unfolded = coalgebra(term);
        let mapped = unfolded.map(|subterm| Self::hylo(subterm, algebra, coalgebra));
        algebra(mapped)
    }
    pub fn metamorphism<A>(
        self,
        algebra: &mut impl FnMut(AstF<A>) -> A,
        coalgebra: &mut impl FnMut(A) -> AstF<A>,
    ) -> Self {
        let folded = self.catamorphism(algebra);
        Self::anamorphism(folded, coalgebra)
    }
}
#[derive(Clone, PartialEq, Debug)]
pub struct Pair<A>(pub A, pub A);

#[derive(Clone, PartialEq, Debug)]
pub enum AstF<A> {
    Pair(Pair<A>),
    TheEmptyList,
    Syntax(Syntax),
    Number(f64),
    Symbol(Symbol),
    Function(Function),
}
impl<A> AstF<A> {
    fn map<B, F>(self, mut f: F) -> AstF<B>
    where
        F: FnMut(A) -> B,
    {
        match self {
            AstF::Pair(Pair(car, cdr)) => AstF::Pair(Pair(f(car), f(cdr))),
            AstF::TheEmptyList => AstF::TheEmptyList,
            AstF::Syntax(syntax) => AstF::Syntax(syntax),
            AstF::Number(number) => AstF::Number(number),
            AstF::Symbol(symbol) => AstF::Symbol(symbol),
            AstF::Function(function) => AstF::Function(function),
        }
    }
    fn map_borrow<B, F>(&self, mut f: F) -> AstF<B>
    where
        F: FnMut(&A) -> B,
    {
        match self {
            AstF::Pair(Pair(car, cdr)) => AstF::Pair(Pair(f(car), f(cdr))),
            AstF::TheEmptyList => AstF::TheEmptyList,
            AstF::Syntax(syntax) => AstF::Syntax(syntax.clone()),
            AstF::Number(number) => AstF::Number(*number),
            AstF::Symbol(symbol) => AstF::Symbol(symbol.clone()),
            AstF::Function(function) => AstF::Function(function.clone()),
        }
    }
}
impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &*self.out {
            AstF::Pair(pair) => {
                let mut string = pair.0.to_string();
                let mut second = pair.1.clone();
                while let AstF::Pair(pair) = *second.out {
                    string = format!("{string} {}", pair.0);
                    second = pair.1;
                }
                if *second.out != AstF::TheEmptyList {
                    string = format!("{string} . {second}");
                }
                write!(f, "({string})")
            }
            AstF::Syntax(s) => write!(f, "#'{}", s.0),
            AstF::Number(n) => write!(f, "{n}"),
            AstF::Symbol(s) => write!(f, "'{s}"),
            AstF::Function(function) => write!(f, "{function}"),
            AstF::TheEmptyList => write!(f, "()"),
        }
    }
}
#[derive(Debug)]
enum MapError<E> {
    NoEmptyList,
    BadListForm,
    Other(E),
}
impl Ast {
    #[must_use]
    pub fn size(&self) -> usize {
        self.catamorphism_borrow(&mut |x: &AstF<usize>| match x {
            AstF::Pair(Pair(x, y)) => x.max(y) + 1,
            _ => 0,
        })
    }
    // TODO: maybe map should not be in terms of catamorphism
    pub fn map(&self, f: &impl Fn(Self) -> Result<Self, String>) -> Result<Self, String> {
        macro_rules! base {
            ($other:expr) => {
                Box::new(move |pair| {
                    if pair {
                        f(Ast::new($other))
                    } else {
                        Err("not a list".to_string())
                    }
                })
            };
        }
        self.clone().catamorphism(
            &mut |term: AstF<Box<dyn Fn(bool) -> Result<Ast, String>>>| match term {
                AstF::Pair(Pair(car, cdr)) => Box::new(move |_| {
                    let car = car(true)?;
                    let cdr = cdr(false)?;
                    Ok(Ast::new(AstF::Pair(Pair(car, cdr))))
                }),
                AstF::TheEmptyList => Box::new(|_| Ok(Ast::new(AstF::TheEmptyList))),
                AstF::Syntax(syntax) => base!(AstF::Syntax(syntax.clone())),
                AstF::Number(number) => base!(AstF::Number(number)),
                AstF::Symbol(symbol) => base!(AstF::Symbol(symbol.clone())),
                AstF::Function(function) => base!(AstF::Function(function.clone())),
            },
        )(false)
    }
    #[must_use]
    pub fn list(&self) -> bool {
        self.catamorphism_borrow(&mut |ast| match ast {
            AstF::Pair(Pair(_, x)) => *x,
            AstF::TheEmptyList => true,
            _ => false,
        })
    }

    #[must_use]
    pub fn datum_to_syntax(self) -> Self {
        self.catamorphism(&mut |term| match term {
            AstF::Symbol(s) => Ast::new(AstF::Syntax(Syntax::new(s))),
            _ => Ast::new(term),
        })
    }
    fn syntax_to_datum(self) -> Self {
        self.catamorphism(&mut |term| match term {
            AstF::Syntax(Syntax(s, _)) => Ast::new(AstF::Symbol(s)),
            _ => Ast::new(term),
        })
    }
    fn identifier(&self) -> bool {
        matches!(*self.out, AstF::Syntax(..))
    }
}

impl AdjustScope for Ast {
    fn adjust_scope(
        self,
        other_scope: Scope,
        operation: fn(ScopeSet, Scope) -> BTreeSet<Scope>,
    ) -> Self {
        self.catamorphism(&mut |term| match term {
            AstF::Syntax(x) => Ast::new(AstF::Syntax(x.adjust_scope(other_scope, operation))),
            _ => Ast::new(term),
        })
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum Binding {
    Lambda,
    LetSyntax,
    Quote,
    QuoteSyntax,
    App,
    Variable(Symbol),
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Variable(s) => format!("{s}"),
                Self::Lambda => "lambda".to_string(),
                Self::LetSyntax => "let-syntax".to_string(),
                Self::Quote => "quote".to_string(),
                Self::QuoteSyntax => "quote-syntax".to_string(),
                Self::App => "%app".to_string(),
            }
        )
    }
}
impl From<Binding> for Symbol {
    fn from(value: Binding) -> Self {
        match value {
            Binding::Variable(s) => s,
            Binding::Lambda => "lambda".into(),
            Binding::LetSyntax => "let-syntax".into(),
            Binding::Quote => "quote".into(),
            Binding::QuoteSyntax => "quote-syntax".into(),
            Binding::App => "%app".into(),
        }
    }
}

#[derive(Debug)]
pub struct Expander<T> {
    all_bindings: HashMap<Syntax, T>,
    core_forms: BTreeSet<Binding>,
    core_primitives: BTreeSet<Binding>,
    core_scope: Scope,
    scope_creator: UniqueNumberManager,
    env: EnvRef,
}

//impl Default for Expander<Binding> {
//    fn default() -> Self {
//        Self::new()
//    }
//}

//impl Expander<Binding> {
//    #[must_use]
//    pub fn new() -> Self {
//        let mut scope_creator = UniqueNumberManager::new();
//        let core_scope = scope_creator.new_scope();
//        let core_forms = BTreeSet::from([
//            Binding::Lambda,
//            Binding::LetSyntax,
//            Binding::Quote,
//            Binding::QuoteSyntax,
//            Binding::App,
//        ]);
//        let core_primitives = BTreeSet::from([
//            Binding::Variable("datum->syntax".into()),
//            Binding::Variable("syntax->datum".into()),
//            Binding::Variable("list".into()),
//            Binding::Variable("cons".into()),
//            Binding::Variable("car".into()),
//            Binding::Variable("cdr".into()),
//            Binding::Variable("map".into()),
//        ]);
//        let mut this = Self {
//            scope_creator,
//            core_scope,
//            core_primitives,
//            core_forms,
//            all_bindings: HashMap::new(),
//            env: new_env(),
//        };
//        this.core_forms
//            .clone()
//            .union(&this.core_primitives.clone())
//            .for_each(|core| {
//                this.add_binding(
//                    Syntax(core.clone().into(), BTreeSet::from([this.core_scope])),
//                    core.clone(),
//                );
//            });
//        this
//    }
//    fn add_binding(&mut self, id: Syntax, binding: Binding) {
//        self.all_bindings.insert(id, binding);
//    }
//
//    fn add_local_binding(&mut self, id: Syntax) -> Symbol {
//        let symbol = self.scope_creator.gen_sym(&id.0 .0);
//        self.add_binding(id, Binding::Variable(symbol.clone()));
//        symbol
//    }
//
//    fn resolve(&self, id: &Syntax) -> Result<&Binding, String> {
//        let candidate_ids = self.find_all_matching_bindings(id);
//        let id = candidate_ids
//            .clone()
//            .max_by_key(|id| id.1.len())
//            .ok_or(format!("free variable {id:?}"))?;
//        if check_unambiguous(id, candidate_ids) {
//            self.all_bindings
//                .get(id)
//                .ok_or(format!("free variable {}", id.0 .0))
//        } else {
//            Err(format!("ambiguous binding {}", id.0 .0))
//        }
//    }
//
//    fn free_identifier(&self, a: Ast, b: Ast) -> bool {
//        matches!((*a.out, *b.out), (AstF::Syntax(a), AstF::Syntax(b)) if self.resolve( &a).is_ok_and(|a| self.resolve(&b).is_ok_and(|b| a == b )))
//    }
//
//    fn find_all_matching_bindings<'a>(
//        &'a self,
//        id: &'a Syntax,
//    ) -> impl Iterator<Item = &Syntax> + Clone + 'a {
//        self.all_bindings
//            .keys()
//            .filter(move |c_id| c_id.0 == id.0 && c_id.1.is_subset(&id.1))
//    }
//
//    pub fn namespace_syntax_introduce<T: AdjustScope>(&self, s: T) -> T {
//        s.add_scope(self.core_scope)
//    }
//
//    #[trace::trace()]
//    pub fn expand(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
//        match *s.out {
//            AstF::Syntax(s) => self.expand_identifier(s, env),
//            AstF::Pair(l) if matches!(&*l.0.out, AstF::Syntax(_)) => {
//                self.expand_id_application_form(l, env)
//            }
//            AstF::Pair(l) => self.expand_app(l, env),
//            _ => Ok(Ast::new(AstF::Pair(Pair(
//                Ast::new(AstF::Syntax(Syntax(
//                    "quote".into(),
//                    BTreeSet::from([self.core_scope]),
//                ))),
//                Ast::new(AstF::Pair((Pair(s, Ast::new(AstF::TheEmptyList))))),
//            )))),
//        }
//    }
//
//    fn expand_identifier(&mut self, s: Syntax, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
//        let binding = self.resolve(&s)?;
//        if self.core_forms.contains(binding) {
//            Err(format!("bad syntax dangling core form {}", s.0))
//        } else if self.core_primitives.contains(binding) {
//            Ok(AstF::Syntax(s))
//        } else {
//            //println!("{:?}", env);
//            let Binding::Variable(binding) = binding else {
//                panic!()
//            };
//            let v = env.lookup(binding).ok_or(format!("out of context {s:?}"))?;
//            match v {
//                CompileTimeBinding::Symbol(_) => Ok(AstF::Syntax(s)),
//                CompileTimeBinding::Macro(m) => self.apply_transformer(m, AstF::Syntax(s)), //_ => Err(format!("bad syntax non function call macro {}", s.0)),
//            }
//        }
//    }
//
//    // constraints = s.len() > 0
//    // constraints = s[0] == AstF::Syntax(_)
//    fn expand_id_application_form(
//        &mut self,
//        s: Pair,
//        env: CompileTimeEnvoirnment,
//    ) -> Result<Ast, String> {
//        let AstF::Syntax(ref id) = s.0 else {
//            unreachable!()
//        };
//        let binding = self.resolve(id)?;
//        match binding {
//            Binding::Lambda => self.expand_lambda(s, env),
//            Binding::LetSyntax => self.expand_let_syntax(s, env),
//            Binding::Quote | Binding::QuoteSyntax => Ok(AstF::Pair(Pair(Box::new(s)))),
//            Binding::App => {
//                if !s.list() {
//                    Err(format!("%app form's arguements must be a list"))?
//                }
//                // TODO: empty list
//                let AstF::Pair(Pair(p)) = s.1 else {
//                    unreachable!()
//                };
//                self.expand_app(*p, env)
//            }
//            Binding::Variable(binding) => match env.lookup(binding) {
//                Some(CompileTimeBinding::Macro(m)) => {
//                    //println!("{binding} in {env:?}");
//                    let apply_transformer =
//                        self.apply_transformer(m, AstF::Pair(Pair(Box::new(s))))?;
//                    //println!("app {apply_transformer}");
//                    self.expand(apply_transformer, env)
//                }
//                _ => self.expand_app(s, env),
//            },
//        }
//    }
//    fn apply_transformer(&mut self, m: Function, s: Ast) -> Result<Ast, String> {
//        let intro_scope = self.scope_creator.new_scope();
//        //println!("apply_transformer {s:?}");
//        let intro_s = s.add_scope(intro_scope);
//        let transformed_s = m.apply(AstF::Pair(Pair(Box::new(Pair(
//            intro_s,
//            AstF::TheEmptyList,
//        )))))?;
//
//        Ok(transformed_s.flip_scope(intro_scope))
//    }
//    fn expand_app(&mut self, s: Pair, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
//        let Pair(rator, rands) = s;
//
//        Ok(AstF::Pair(Pair(Box::new(Pair(
//            AstF::Syntax(Syntax("%app".into(), BTreeSet::from([self.core_scope]))),
//            AstF::Pair(Pair(Box::new(Pair(
//                self.expand(rator, env.clone())?,
//                rands.map(|rand| self.expand(rand, env.clone()))?,
//            )))),
//        )))))
//    }
//
//    fn expand_lambda(&mut self, s: Pair, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
//        //println!("lambda body {s:?}");
//        let Pair(ref lambda_id, AstF::Pair(Pair(ref inner))) = s else {
//            Err(format!("invalid syntax {s:?} bad lambda"))?
//        };
//        let Pair(AstF::Pair(Pair(ref arg)), AstF::Pair(Pair(ref body))) = **inner else {
//            Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
//        };
//        let Pair(AstF::Syntax(ref arg_id), AstF::TheEmptyList) = **arg else {
//            Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
//        };
//        let Pair(ref body, AstF::TheEmptyList) = **body else {
//            Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
//        };
//        let sc = self.scope_creator.new_scope();
//        let id = arg_id.clone().add_scope(sc);
//        let binding = self.add_local_binding(id.clone());
//        let body_env = env.extend(binding.clone(), CompileTimeBinding::Symbol(binding));
//        let exp_body = self.expand(body.clone().add_scope(sc), body_env)?;
//        Ok(AstF::Pair(Pair(Box::new(Pair(
//            lambda_id.clone(),
//            AstF::Pair(Pair(Box::new(Pair(
//                AstF::Pair(Pair(Box::new(Pair(AstF::Syntax(id), AstF::TheEmptyList)))),
//                AstF::Pair(Pair(Box::new(Pair(exp_body, AstF::TheEmptyList)))),
//            )))),
//        )))))
//    }
//
//    fn expand_let_syntax(&mut self, s: Pair, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
//        // `(,let-syntax-id ([,lhs-id ,rhs])
//        //            ,body)
//        // (cons 'let-syntax (cons (cons (cons 'lhs (cons 'rhs '())) '()) (cons 'body '())))
//        let Pair(ref _let_syntax_id, AstF::Pair(Pair(ref inner))) = s else {
//            Err(format!("invalid syntax {s:?} bad let-syntax"))?
//        };
//        let Pair(AstF::Pair(Pair(ref binder_list)), AstF::Pair(Pair(ref body))) = **inner else {
//            Err(format!("invalid syntax {s:?} bad let-syntax {:?}", inner.0))?
//        };
//        let Pair(AstF::Pair(Pair(ref binder_list)), AstF::TheEmptyList) = **binder_list else {
//            Err(format!(
//                "invalid syntax {s:?}, bad binder list for let-syntax {binder_list:?}"
//            ))?
//        };
//        let Pair(AstF::Syntax(ref lhs_id), AstF::Pair(Pair(ref rhs_list))) = **binder_list else {
//            Err(format!(
//                "invalid syntax {s:?}, bad binder for let-syntax {binder_list:?}"
//            ))?
//        };
//        let Pair(ref rhs, AstF::TheEmptyList) = **rhs_list else {
//            Err(format!(
//                "invalid syntax {s:?}, bad binder list for let-syntax {rhs_list:?}"
//            ))?
//        };
//        let Pair(ref body, AstF::TheEmptyList) = **body else {
//            Err(format!(
//                "invalid syntax {s:?}, bad binder list for let-syntax {body:?}"
//            ))?
//        };
//        let sc = self.scope_creator.new_scope();
//        let id = lhs_id.clone().add_scope(sc);
//        let binding = self.add_local_binding(id);
//        let rhs_val = self.eval_for_syntax_binding(rhs.clone())?;
//        let body_env = env.extend(binding, rhs_val);
//        //println!("found macro {binding}");
//        //println!("expand {body} in {body_env:?}");
//        self.expand(body.clone().add_scope(sc), body_env)
//    }
//
//    fn eval_for_syntax_binding(&mut self, rhs: Ast) -> Result<CompileTimeBinding, String> {
//        // let var_name = format!("problem `evaluating` macro {rhs}");
//        //println!("macro body {rhs}");
//        let expand = self.expand(rhs, CompileTimeEnvoirnment::new())?;
//        //println!("macro body {expand}");
//        self.eval_compiled(self.compile(expand)?).and_then(|e| {
//            if let AstF::Function(f) = e {
//                Ok(CompileTimeBinding::Macro(f))
//            } else {
//                Err(format!("{e} is not a macro"))
//            }
//        })
//    }
//
//    #[trace::trace()]
//    fn compile(&self, rhs: Ast) -> Result<Ast, String> {
//        println!("compile {rhs}");
//        match rhs {
//            AstF::Pair(l) => {
//                let core_sym = if let AstF::Syntax(ref s) = l.0 {
//                    self.resolve(s)
//                } else {
//                    Err("just for _ case in next match does not actually error".to_string())
//                };
//                match core_sym {
//                    Ok(Binding::Lambda) => {
//                        let Pair(ref _lambda_id, AstF::Pair(ref inner)) = *l else {
//                            Err(format!("invalid syntax {l:?} bad lambda"))?
//                        };
//                        let Pair(AstF::Pair(ref arg), AstF::Pair(ref body)) = **inner else {
//                            Err(format!("invalid syntax {inner:?}, bad form for lambda"))?
//                        };
//                        let Pair(AstF::Syntax(ref id), AstF::TheEmptyList) = **arg else {
//                            Err(format!("invalid syntax {arg:?}, bad argument for lambda"))?
//                        };
//                        let Pair(ref body, AstF::TheEmptyList) = **body else {
//                            Err(format!("invalid syntax {body:?}, bad body for lambda"))?
//                        };
//                        let Binding::Variable(id) = self.resolve(id)? else {
//                            Err("bad syntax cannot play with core form")?
//                        };
//
//                        // (list 'lambda (list 'x) 'body)
//                        Ok(AstF::Pair(Box::new(Pair(
//                            AstF::Symbol(Symbol("lambda".into(), 0)),
//                            AstF::Pair(Box::new(Pair(
//                                AstF::Pair(Box::new(Pair(
//                                    AstF::Symbol(id.clone()),
//                                    AstF::TheEmptyList,
//                                ))),
//                                AstF::Pair(Box::new(Pair(
//                                    self.compile(body.clone())?,
//                                    AstF::TheEmptyList,
//                                ))),
//                            ))),
//                        ))))
//                    }
//                    Ok(Binding::Quote) => {
//                        let Pair(_, AstF::Pair(datum)) = *l else {
//                            Err("bad syntax, quote requires one expression")?
//                        };
//                        let Pair(datum, AstF::TheEmptyList) = *datum else {
//                            Err("bad syntax, quote requires one expression")?
//                        };
//                        Ok(AstF::Pair(Box::new(Pair(
//                            AstF::Symbol(Symbol("quote".into(), 0)),
//                            AstF::Pair(Box::new(Pair(datum.syntax_to_datum(), AstF::TheEmptyList))),
//                        ))))
//                    }
//                    Ok(Binding::QuoteSyntax) => {
//                        let Pair(_, AstF::Pair(datum)) = *l else {
//                            Err("bad syntax, quote-syntax requires one expression")?
//                        };
//                        let Pair(datum, AstF::TheEmptyList) = *datum else {
//                            Err("bad syntax, quote-syntax requires one expression")?
//                        };
//                        Ok(AstF::Pair(Box::new(Pair(
//                            AstF::Symbol(Symbol("quote".into(), 0)),
//                            AstF::Pair(Box::new(Pair(datum, AstF::TheEmptyList))),
//                        ))))
//                    }
//                    Ok(Binding::App) => {
//                        let Pair(_, AstF::Pair(app)) = *l else {
//                            Err("bad syntax, %app requires at least a function")?
//                        };
//                        if app.1.list() {
//                            Err("bad syntax, %app arguments must be a list")?
//                        }
//                        Ok(AstF::Pair(Box::new(Pair(
//                            self.compile(app.0)?,
//                            app.1.map(|e| self.compile(e))?,
//                        ))))
//                    }
//                    _ => Err(format!("unrecognized core form {}", l.0)),
//                }
//            }
//            AstF::Syntax(s) => {
//                if let Binding::Variable(s) = self.resolve(&s)? {
//                    Ok(AstF::Symbol(s.clone()))
//                } else {
//                    Err("bad syntax cannot play with core form")?
//                }
//            }
//            AstF::Number(_) | AstF::Function(_) => Ok(rhs),
//            AstF::Symbol(_) | AstF::TheEmptyList => unreachable!(),
//        }
//    }
//
//    fn eval_compiled(&self, new: Ast) -> Result<Ast, String> {
//        //println!("body {new}");
//        Evaluator::eval(new, self.env.clone())
//    }
//}

fn new_env() -> Rc<RefCell<Env>> {
    let env = Env::new();
    //env.borrow_mut().define(
    //    Symbol("datum->syntax".into(), 0),
    //    AstF::Function(Function::Primitive(move |e| {
    //        let AstF::Pair(Pair(e)) = e else {
    //            Err(format!(
    //                "arity error: expected 1 argument, got {}",
    //                e.size()
    //            ))?
    //        };
    //        let Pair(e, AstF::TheEmptyList) = *e else {
    //            Err(format!(
    //                "arity error: expected 1 argument, got {}",
    //                e.size()
    //            ))?
    //        };
    //        Ok(e.datum_to_syntax())
    //    })),
    //);
    //env.borrow_mut().define(
    //    Symbol("syntax->datum".into(), 0),
    //    AstF::Function(Function::Primitive(move |e| {
    //        let AstF::Pair(Pair(e)) = e else {
    //            Err(format!(
    //                "arity error: expected 1 argument, got {}",
    //                e.size()
    //            ))?
    //        };
    //        let Pair(e, AstF::TheEmptyList) = *e else {
    //            Err(format!(
    //                "arity error: expected 1 argument, got {}", e.size()
    //            ))?
    //        };
    //        Ok(e.syntax_to_datum())
    //    })),
    //);
    //env.borrow_mut().define(
    //    Symbol("syntax-e".into(), 0),
    //    AstF::Function(Function::Primitive(move |e| {
    //        let AstF::Pair(Pair(e)) = e else {
    //            Err(format!(
    //                "arity error: expected 1 argument, got {}",
    //                e.size()
    //            ))?
    //        };
    //        let Pair(AstF::Syntax(Syntax(e, _)), AstF::TheEmptyList) = *e else {
    //            Err(format!(
    //                "arity error: expected 1 argument, got {}",
    //                e.size()
    //            ))?
    //        };
    //        Ok(AstF::Symbol(e))
    //    })),
    //);
    env.borrow_mut().define(
        Symbol("cons".into(), 0),
        Ast::new(AstF::Function(Function::Primitive(move |e| {
            let AstF::Pair(Pair(ref car, ref rest)) = *e.out else {
                Err(format!(
                    "arity error: expected 2 argument, missing first argument",
                ))?
            };
            let AstF::Pair(Pair(ref cdr, ref rest)) = *rest.out else {
                Err(format!(
                    "arity error: expected 2 argument, missing second argument",
                ))?
            };
            if *rest.out != AstF::TheEmptyList {
                Err(format!(
                    "arity error: expected 2 argument, found more than 2, {}",
                    e.size()
                ))?
            }
            Ok(Ast::new(AstF::Pair(Pair(car.clone(), cdr.clone()))))
        }))),
    );
    //env.borrow_mut().define(
    //    Symbol("car".into(), 0),
    //    AstF::Function(Function::Primitive(move |e| {
    //        let AstF::Pair(Pair(e)) = e else {
    //            Err(format!(
    //                "arity error: expected 1 argument, got {}",
    //                e.size()
    //            ))?
    //        };
    //
    //        let Pair(AstF::Pair(Pair(e)), AstF::TheEmptyList) = *e else {
    //            Err(format!(
    //                "arity error: expected 1 argument, got {}",
    //                e.size()
    //            ))?
    //        };
    //        let Pair(fst, _) = *e;
    //        Ok(fst)
    //    })),
    //);
    //env.borrow_mut().define(
    //    Symbol("cdr".into(), 0),
    //    AstF::Function(Function::Primitive(move |e| {
    //            println!("cdr {e}");
    //            let AstF::Pair(Pair(e)) = e else {
    //                Err(format!(
    //                    "arity error: expected 1 argument, got {}",
    //                    e.size()
    //                ))?
    //            };
    //            let Pair(AstF::Pair(Pair(e)), AstF::TheEmptyList) = *e else {
    //                Err(format!(
    //                    "arity error: expected 1 argument, got {}",
    //                    e.size()
    //                ))?
    //            };
    //            let Pair(_, snd) = *e;
    //            Ok(snd)
    //        })),
    //    );
    //    env.borrow_mut().define(
    //        Symbol("list".into(), 0),
    //        AstF::Function(Function::Primitive(Ok)),
    //    );
    //    env.borrow_mut().define(
    //        Symbol("map".into(), 0),
    //        AstF::Function(Function::Primitive(move |e| {
    //            let AstF::Pair(Pair(e)) = e else {
    //                Err(format!(
    //                    "arity error: expected 1 argument, got {}",
    //                    e.size()
    //                ))?
    //            };
    //
    //            let Pair(AstF::Function(ref f), AstF::Pair(Pair(ref last))) = *e else {
    //                Err(format!(
    //                    "arity error: expected 2 argument, got {}",
    //                    e.size()
    //                ))?
    //            };
    //            let Pair(ref l, AstF::TheEmptyList) = **last else {
    //                Err(format!(
    //                    "arity error: expected 2 argument, got {}",
    //                    e.size()
    //                ))?
    //            };
    //            l.map(|a| f.apply(AstF::Pair(Pair(Box::new(Pair(a, AstF::TheEmptyList))))))
    //        })),
    //    );
    env
}

#[derive(Clone, PartialEq, Debug)]
pub struct Env {
    scope: HashMap<Symbol, Ast>,
    parent: Option<EnvRef>,
}

impl Env {
    fn lookup(&self, symbol: &Symbol) -> Option<Ast> {
        self.scope.get(symbol).cloned().or_else(|| {
            self.parent
                .as_ref()
                .and_then(|parent| parent.borrow().lookup(symbol))
        })
    }
    fn set(&mut self, symbol: Symbol, mut expr: Ast) -> Option<Ast> {
        {
            match self.scope.get_mut(&symbol) {
                Some(s) => {
                    std::mem::swap(s, &mut expr);
                    Some(expr)
                }
                None => self
                    .parent
                    .as_ref()
                    .and_then(|parent| parent.borrow_mut().set(symbol, expr)),
            }
        }
    }
    fn define(&mut self, symbol: Symbol, expr: Ast) -> bool {
        self.scope.insert(symbol, expr).is_some()
    }
    fn new_scope(env: EnvRef) -> EnvRef {
        let parent = Some(env);
        let scope = HashMap::new();
        Rc::new(RefCell::new(Self { scope, parent }))
    }

    fn extend_envoirnment(env: EnvRef, params: Ast, args: Ast) -> Result<EnvRef, String> {
        let new_envoirnment = Self::new_scope(env);
        match params.size().cmp(&args.size()) {
            Ordering::Less => Err("arity error to many arguments passed in".to_string()),
            Ordering::Greater => Err("arity error to little arguments passed in".to_string()),
            Ordering::Equal => {
                fn extend_envoirnment(
                    env: Rc<RefCell<Env>>,
                    params: Ast,
                    args: Ast,
                ) -> Option<String> {
                    match (*params.out, *args.out) {
                        (
                            AstF::Pair(Pair(param, rest_params)),
                            AstF::Pair(Pair(arg, rest_args)),
                        ) => {
                            let AstF::Symbol(p) = *param.out else {
                                return Some(String::new());
                            };
                            env.borrow_mut().define(p, arg);
                            extend_envoirnment(env, rest_params, rest_args)
                        }
                        _ => None,
                    }
                }
                extend_envoirnment(new_envoirnment.clone(), params, args);
                Ok(new_envoirnment)
            }
        }
    }

    fn new() -> EnvRef {
        let scope = HashMap::new();
        // TODO: primitive environment
        let parent = None;
        Rc::new(RefCell::new(Self { scope, parent }))
    }
}

type EnvRef = Rc<RefCell<Env>>;

pub struct Evaluator {}

#[derive(Clone, Copy)]
pub enum State {
    Normal,
    Application,
    AplicationArgs,
    Lambda,
    LambdaParams,
    Quote,
    QuoteBody,
    Define,
    LambdaBody,
    LambdaParam,
}
impl Evaluator {
    #[trace]
    fn eval(expr: Ast, env: EnvRef) -> Result<Ast, String> {
        println!("eval {expr}");
        (expr.zygomorphism(
            &mut |expr| match expr {
                AstF::Pair(pair) => pair.0,
                AstF::Symbol(s) => match &*s.0 {
                    "lambda" if s.1 == 0 => State::Lambda,
                    "quote" if s.1 == 0 => State::Quote,
                    "define" if s.1 == 0 => State::Define,
                    "%app" if s.1 == 0 => State::Application,
                    _ => State::Normal,
                },
                _ => State::Normal,
            },
            &mut |expr: AstF<(State, Box<dyn AnalyzeStateFn>)>| {
                match expr {
                    AstF::Pair(Pair(car, cdr)) => Box::new(move |env, state| {
                        let car = car.clone();
                        let cdr = cdr.clone();
                        match state {
                            State::Normal => cdr.1(env, car.0),
                            State::Application => {
                                let function = car.1(env.clone(), State::Normal)?;
                                let args = cdr.1(env, State::AplicationArgs)?;
                                Self::execute_application(function, args)
                            }
                            State::AplicationArgs => Ok(Ast::new(AstF::Pair(Pair(
                                car.1(env.clone(), State::Normal)?,
                                cdr.1(env, State::AplicationArgs)?,
                            )))),
                            State::Lambda => {
                                let args = car.1(env.clone(), State::LambdaParams)?;
                                let body = Box::new(move |env| cdr.1(env, State::LambdaBody));
                                Ok(Ast::new(AstF::Function(Function::Lambda(Lambda(
                                    body, env, args,
                                )))))
                            }
                            State::LambdaParams => Ok(Ast::new(AstF::Pair(Pair(
                                car.1(env.clone(), State::LambdaParam)?,
                                cdr.1(env, State::LambdaParams)?,
                            )))),
                            State::QuoteBody => Ok(Ast::new(AstF::Pair(Pair(
                                car.1(env.clone(), State::QuoteBody)?,
                                cdr.1(env, State::QuoteBody)?,
                            )))),
                            State::Define => todo!(),
                            State::Quote => {
                                if *cdr.1(env.clone(), State::QuoteBody)?.out != AstF::TheEmptyList
                                {
                                    Err("bad syntax, quote requires one expression")?
                                }
                                car.1(env.clone(), State::QuoteBody)
                            }
                            State::LambdaParam => panic!(),
                            State::LambdaBody => {
                                if *cdr.1(env.clone(), State::QuoteBody)?.out != AstF::TheEmptyList
                                {
                                    Err("bad syntax, quote requires one expression")?
                                }
                                car.1(env.clone(), State::Normal)
                            }
                        }
                    }),

                    // TODO: fail for lambda params unless the empty list
                    AstF::Symbol(s) => Box::new(move |env: EnvRef, state: State| match state {
                        State::Normal => env
                            .borrow()
                            .lookup(&s)
                            .ok_or(format!("free variable {}", &s)),
                        _ => Ok(Ast::new(AstF::Symbol(s.clone()))),
                    }),
                    AstF::TheEmptyList => Box::new(move |_, _| Ok(Ast::new(AstF::TheEmptyList))),
                    AstF::Syntax(s) => Box::new(move |_, _| Ok(Ast::new(AstF::Syntax(s.clone())))),
                    AstF::Function(f) => {
                        Box::new(move |_, _| Ok(Ast::new(AstF::Function(f.clone()))))
                    }
                    AstF::Number(n) => Box::new(move |_, _| Ok(Ast::new(AstF::Number(n.clone())))),
                }
            },
        ))(env, State::Normal)
        //match expr {
        //    AstF::Pair(list) => match list.0 {
        //        AstF::Symbol(Symbol(ref lambda, 0)) if **lambda == *"lambda" => {
        //            let Pair(ref lambda_id, AstF::Pair(ref inner)) = *list else {
        //                Err(format!("invalid syntax {list:?} bad lambda"))?
        //            };
        //            let Pair(AstF::Pair(ref arg), AstF::Pair(ref body)) = **inner else {
        //                Err(format!("invalid syntax {list:?}, bad argument for lambda"))?
        //            };
        //
        //            // TODO: variadic function with dot notation
        //            let args = arg.map(|arg| {
        //                if let AstF::Symbol(s) = arg {
        //                    Ok(AstF::Symbol(s))
        //                } else {
        //                    Err(format!("bad syntax {arg} is not a valid paramter"))
        //                }
        //            })?;
        //            Ok(AstF::Function(Function::Lambda(Lambda(
        //                Box::new(AstF::Pair(body.clone())),
        //                env,
        //                Box::new(args),
        //            ))))
        //        }
        //        AstF::Symbol(Symbol(quote, 0)) if *quote == *"quote" => {
        //            let Pair(_, AstF::Pair(datum)) = *list else {
        //                Err("bad syntax, quote requires one expression")?
        //            };
        //            let Pair(datum, AstF::TheEmptyList) = *datum else {
        //                Err("bad syntax, quote requires one expression")?
        //            };
        //            Ok(datum)
        //        }
        //        f => {
        //            let f = Self::eval(f, env.clone())?;
        //            let rest = list.1.map(|arg| Self::eval(arg, env.clone()))?;
        //            Self::execute_application(f, rest)
        //        } //AstF::TheEmptyList => Err(format!("bad syntax {list:?}, empty application")),
        //    },
        //    AstF::Symbol(s) =>
        //    //println!("variable {s})");
        //    {
        //        env.borrow().lookup(&s).ok_or(format!("free variable {s}"))
        //    }
        //    //.inspect(|x|println!("variable {x}"))
        //    ,
        //    _ => Ok(expr.clone()),
        //}
    }

    fn execute_application(f: Ast, args: Ast) -> Result<Ast, String> {
        if let AstF::Function(f) = *f.out {
            f.apply(args)
            //.inspect(|x|println!("application {x}"))
        } else {
            Err(format!(
                "cannot not apply {f} to {args:?}, because {f} is not a function"
            ))
        }
    }

    fn eval_sequence(body: Ast, env: Rc<RefCell<Env>>) -> Result<Ast, String> {
        let AstF::Pair(Pair(car, cdr)) = *body.out else {
            return Err(format!("not a sequence {body}"));
        };
        if *cdr.out == AstF::TheEmptyList {
            Self::eval(car, env)
        } else {
            Self::eval(car, env.clone())?;
            Self::eval_sequence(cdr, env)
        }
    }
}

pub struct Reader(String);
#[derive(Debug)]
struct OwnedChars {
    string: String,
    position: usize,
}

impl Iterator for OwnedChars {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        let c = self.string[self.position..].chars().next()?;
        self.position += c.len_utf8();
        Some(c)
    }
}

trait OwnedCharsExt {
    fn chars(self) -> OwnedChars;
}
impl OwnedCharsExt for String {
    fn chars(self) -> OwnedChars {
        OwnedChars {
            string: self,
            position: 0,
        }
    }
}
trace::init_depth_var!();
type Input = Peekable<OwnedChars>;
type ReaderInnerResult = Result<(Ast, Input), (String, Input)>;
impl Reader {
    // we have empty continuations for if we run out of input, but we can recover if we get more
    // input
    pub fn read(&mut self) -> Result<Ast, String> {
        let input = <String as Clone>::clone(&self.0).chars().peekable();
        match Self::read_inner(input, &mut || None) {
            Ok((ast, rest)) => {
                self.0 = rest.collect();
                Ok(ast)
            }
            Err((reason, rest)) => {
                self.0 = rest.collect();
                Err(reason)
            }
        }
    }
    pub fn read_with_continue(
        &mut self,
        mut empty_continuation: impl FnMut() -> String,
    ) -> Result<Ast, String> {
        let input = <String as Clone>::clone(&self.0).chars().peekable();
        match Self::read_inner(input, &mut || Some(empty_continuation())) {
            Ok((ast, rest)) => {
                self.0 = rest.collect();
                Ok(ast)
            }
            Err((reason, rest)) => {
                self.0 = rest.collect();
                Err(reason)
            }
        }
    }
    // #[trace(format_enter = "", format_exit = "")]
    fn read_inner(
        input: Input,
        empty_continuation: &mut impl FnMut() -> Option<String>,
    ) -> ReaderInnerResult {
        let mut input = Self::read_whitespace_and_comments(input).1;
        match input.peek() {
            // TODO: quote
            Some('(') => {
                input.next();
                Self::read_list(input, empty_continuation)
            }
            Some(')') => {
                input.next();
                Err(("unfinished pair".to_string(), input))
            }

            Some(n) if n.is_ascii_digit() => Self::read_number(input),
            Some(_) => Self::read_symbol(input),
            None => empty_continuation()
                .ok_or((String::from("empty input"), input))
                .and_then(|input| {
                    let input = input.chars().peekable();
                    Self::read_inner(input, empty_continuation)
                }),
        }
    }

    // #[trace(format_enter = "", format_exit = "")]
    fn read_whitespace_and_comments(mut input: Input) -> (bool, Input) {
        let mut found = false;
        while let Some(c) = input.peek() {
            match c {
                ';' => {
                    found = true;
                    // we do find to skip untill we find newline, this is essentially
                    // what skip while does, but skip while returns a new type and we
                    // cannot do impl trait in type alias so this does not work for with
                    // my input type
                    input.find(|c| *c != '\n');
                }
                c if c.is_whitespace() => {
                    found = true;
                    input.next();
                }
                _ => break,
            }
        }
        (found, input)
    }

    // #[trace(format_enter = "", format_exit = "")]
    // parse symbol if not followed by space paren or comment
    // invariant Some('.') | Some(c) if c.is_ascci_digit() = input.peek()
    fn read_number(input: Input) -> ReaderInnerResult {
        let (first, mut input) = Self::read_digit(input);
        let (second, input) = {
            if input.peek().copied().filter(|c| *c == '.').is_some() {
                input.next();
                let (digits, input) = Self::read_digit(input);
                (format!(".{digits}"), input)
            } else {
                (String::new(), input)
            }
        };
        let (last, input) = Self::read_symbol_inner(input);
        match (first.as_str(), second.as_str(), last.as_str()) {
            ("", "." | "", "") => Err(("invalid syntax dangling dot".to_owned(), input)),
            (_, _, "") => match format!("{first}{second}").parse::<f64>() {
                Ok(n) => Ok((Ast::new(AstF::Number(n)), input)),
                Err(e) => Err((e.to_string(), input)),
            },

            (first, second, _) => {
                let (last, input) = Self::read_symbol_inner(input);
                Ok((
                    Ast::new(AstF::Symbol(Symbol(
                        format!("{first}{second}{last}").into(),
                        0,
                    ))),
                    input,
                ))
            }
        }
    }
    fn read_digit(mut input: Input) -> (String, Input) {
        let mut number = String::new();
        while let Some(n) = input.peek().copied().filter(char::is_ascii_digit) {
            input.next();
            number.push(n);
        }
        (number, input)
    }
    // constraints input.next() == Some(c) if c != whitespace or comment or paren
    // #[trace(format_enter = "", format_exit = "")]
    fn read_symbol(input: Input) -> ReaderInnerResult {
        let (symbol, input) = Self::read_symbol_inner(input);
        Ok((Ast::new(AstF::Symbol(Symbol(symbol.into(), 0))), input))
    }

    // #[trace(format_enter = "", format_exit = "")]
    fn read_list(
        mut input: Input,
        empty_continuation: &mut impl FnMut() -> Option<String>,
    ) -> ReaderInnerResult {
        input = Self::read_whitespace_and_comments(input).1;
        match input.peek() {
            // TODO: dot tailed list and pair instead of list
            Some(')') => {
                input.next();
                Ok((Ast::new(AstF::TheEmptyList), input))
            }
            Some('.') => {
                let item: Ast;
                (item, input) = Self::read_inner(input, empty_continuation)?;
                input = Self::read_end_parenthesis(input, empty_continuation)?;
                Ok((item, input))
            }
            Some(_) => {
                let item: Ast;
                (item, input) = Self::read_inner(input, empty_continuation)?;
                let item2: Ast;
                (item2, input) = Self::read_list(input, empty_continuation)?;
                Ok((Ast::new(AstF::Pair(Pair(item, item2))), input))
            }
            None => {
                input = empty_continuation()
                    .ok_or(("unfinished list".to_string(), input))
                    .map(|input| input.chars().peekable())?;

                Self::read_list(input, empty_continuation)
            }
        }
    }

    fn read_end_parenthesis(
        mut input: Input,
        empty_continuation: &mut impl FnMut() -> Option<String>,
    ) -> Result<Input, (String, Input)> {
        input = Self::read_whitespace_and_comments(input).1;
        match input.next() {
            Some(')') => Ok(input),
            Some(char) => Err((
                format!("invalid termination character of dotted list {char}"),
                input,
            )),
            None => {
                input = empty_continuation()
                    .ok_or(("unfinished list".to_string(), input))
                    .map(|input| input.chars().peekable())?;
                Self::read_end_parenthesis(input, empty_continuation)
            }
        }
    }

    fn read_symbol_inner(mut input: Input) -> (String, Input) {
        let mut str = String::new();
        while let Some(char) = input.peek().copied() {
            if char.is_whitespace() || ['(', ')', ';', '"', '\''].contains(&char) {
                break;
            }
            input.next();
            str.push(char);
        }
        (str, input)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Symbol(pub Rc<str>, pub usize);

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.0, self.1)
    }
}

impl From<Rc<str>> for Symbol {
    fn from(value: Rc<str>) -> Self {
        Self(value, 0)
    }
}
impl From<&str> for Symbol {
    fn from(value: &str) -> Self {
        Self(value.into(), 0)
    }
}

#[derive(Clone, Debug)]
pub enum CompileTimeBinding {
    Symbol(Symbol),
    Macro(Function),
}

#[derive(Clone, Debug)]
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
    let mut reader = Reader(String::new());
    let newline = || {
        let mut stdin = BufReader::new(std::io::stdin());
        let mut input = String::new();
        // flush the screen
        std::io::stdout().flush().unwrap();
        stdin.read_line(&mut input).unwrap();
        input
    };
    //let mut expander = Expander::new();
    loop {
        print!("\n>> ",);

        let ast = reader
            .read_with_continue(newline)
            .inspect(|e| println!("after reader: {e}"))
            //.and_then(|ast| {
            //    expander.expand(
            //        expander.namespace_syntax_introduce(ast.datum_to_syntax()),
            //        CompileTimeEnvoirnment::new(),
            //    )
            //})
            //.inspect(|e| println!("after expansion: {e}"))
            //.and_then(|ast| expander.compile(ast))
            //.inspect(|e| println!("after expansion part 2: {e}"))
            //.and_then(|ast| expander.eval_compiled(ast));
            .and_then(|e| Evaluator::eval(e, new_env()));
        match ast {
            Ok(expr) => println!("{expr}"),
            Err(e) => println!("{e}"),
        }
    }
}

//#[cfg(test)]
//mod tests {
//    use std::collections::BTreeSet;
//
//    use crate::{AdjustScope, Ast, Binding, Expander, Scope, Symbol, Syntax, UniqueNumberManager};
//
//    #[test]
//    fn identifier_test_with_empty_syntax() {
//        assert!(AstF::Syntax(Syntax::new("a".into())).identifier());
//    }
//
//    #[test]
//    fn datum_to_syntax_with_identifier() {
//        assert_eq!(
//            AstF::Symbol(Symbol("a".into(), 0)).datum_to_syntax(),
//            AstF::Syntax(Syntax("a".into(), BTreeSet::new()))
//        );
//    }
//
//    #[test]
//    fn datum_to_syntax_with_number() {
//        assert_eq!(AstF::Number(1.0).datum_to_syntax(), AstF::Number(1.0));
//    }
//
//    #[test]
//    fn datum_to_syntax_with_list() {
//        assert_eq!(
//            Ast::List(vec![
//                AstF::Symbol(Symbol("a".into(), 0)),
//                AstF::Symbol(Symbol("b".into(), 0)),
//                AstF::Symbol(Symbol("c".into(), 0)),
//            ])
//            .datum_to_syntax(),
//            Ast::List(vec![
//                AstF::Syntax(Syntax("a".into(), BTreeSet::new())),
//                AstF::Syntax(Syntax("b".into(), BTreeSet::new())),
//                AstF::Syntax(Syntax("c".into(), BTreeSet::new())),
//            ])
//        );
//    }
//
//    #[test]
//    fn datum_to_syntax_with_list_and_syntax() {
//        assert_eq!(
//            Ast::List(vec![
//                AstF::Symbol(Symbol("a".into(), 0)),
//                AstF::Syntax(Syntax("b".into(), BTreeSet::from([Scope(0), Scope(1)]))),
//                AstF::Symbol(Symbol("c".into(), 0)),
//            ])
//            .datum_to_syntax(),
//            Ast::List(vec![
//                AstF::Syntax(Syntax("a".into(), BTreeSet::new())),
//                AstF::Syntax(Syntax("b".into(), BTreeSet::from([Scope(0), Scope(1)]))),
//                AstF::Syntax(Syntax("c".into(), BTreeSet::new())),
//            ])
//        );
//    }
//    #[test]
//    fn syntax_to_datum_with_identifier() {
//        assert_eq!(
//            AstF::Syntax(Syntax("a".into(), BTreeSet::new())).syntax_to_datum(),
//            AstF::Symbol(Symbol("a".into(), 0)),
//        );
//    }
//
//    #[test]
//    fn syntax_to_datum_with_number() {
//        assert_eq!(AstF::Number(1.0).syntax_to_datum(), AstF::Number(1.0));
//    }
//
//    #[test]
//    fn syntax_to_datum_with_list() {
//        assert_eq!(
//            Ast::List(vec![
//                AstF::Syntax(Syntax("a".into(), BTreeSet::new())),
//                AstF::Syntax(Syntax("b".into(), BTreeSet::new())),
//                AstF::Syntax(Syntax("c".into(), BTreeSet::new())),
//            ])
//            .syntax_to_datum(),
//            Ast::List(vec![
//                AstF::Symbol(Symbol("a".into(), 0)),
//                AstF::Symbol(Symbol("b".into(), 0)),
//                AstF::Symbol(Symbol("c".into(), 0)),
//            ])
//        );
//    }
//
//    #[test]
//    fn scope_equality_test() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//        assert_ne!(sc1, sc2);
//        assert_eq!(sc2, sc2);
//    }
//
//    #[test]
//    fn add_scope_test_empty_scope() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        assert_eq!(
//            AstF::Syntax(Syntax("x".into(), BTreeSet::new())).add_scope(sc1),
//            AstF::Syntax(Syntax("x".into(), BTreeSet::from([sc1])))
//        );
//    }
//
//    #[test]
//    fn add_scope_test_empty_scope_list() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        assert_eq!(
//            Ast::List(vec![
//                AstF::Symbol(Symbol("x".into(), 0)),
//                AstF::Symbol(Symbol("y".into(), 0)),
//            ])
//            .datum_to_syntax()
//            .add_scope(sc1),
//            Ast::List(vec![
//                AstF::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))),
//                AstF::Syntax(Syntax("y".into(), BTreeSet::from([sc1]))),
//            ])
//        );
//    }
//
//    #[test]
//    fn add_scope_test_non_empty_scope() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//        assert_eq!(
//            AstF::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).add_scope(sc2),
//            AstF::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2])))
//        );
//    }
//
//    #[test]
//    fn add_scope_test_add_duplicate() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        assert_eq!(
//            AstF::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).add_scope(sc1),
//            AstF::Syntax(Syntax("x".into(), BTreeSet::from([sc1,])))
//        );
//    }
//
//    #[test]
//    fn flip_scope_test_different() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//        assert_eq!(
//            AstF::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).flip_scope(sc2),
//            AstF::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2])))
//        );
//    }
//
//    #[test]
//    fn flip_scope_test_same() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//        assert_eq!(
//            AstF::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2]))).flip_scope(sc2),
//            AstF::Syntax(Syntax("x".into(), BTreeSet::from([sc1,])))
//        );
//    }
//
//    #[test]
//    fn resolve_test_lambda_empty() {
//        let expander = Expander::new();
//
//        assert_eq!(
//            expander.resolve(&Syntax("lambda".into(), BTreeSet::new())),
//            Err("free variable lambda".to_string())
//        );
//    }
//
//    #[test]
//    fn resolve_test_lambda_core() {
//        let expander = Expander::new();
//
//        println!("{expander:?}");
//        assert_eq!(
//            expander.resolve(&expander.introduce(Syntax("lambda".into(), BTreeSet::new()))),
//            Ok(&Binding::Lambda)
//        );
//    }
//}
