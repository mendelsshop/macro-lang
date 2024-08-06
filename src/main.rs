#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![deny(static_mut_refs)]
#![deny(clippy::use_self, rust_2018_idioms, clippy::missing_panics_doc)]
use core::panic;
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

#[derive(Clone, PartialEq, Debug)]
pub enum Function {
    Lambda(Lambda),
    Primitive(Primitive),
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lambda(l) => write!(f, "(lambda {} {}", l.2, l.0),
            Self::Primitive(_) => write!(f, "(primitive-procedure)"),
        }
    }
}

impl Function {
    fn apply(&self, args: Ast) -> Result<Ast, String> {
        match self {
            Self::Lambda(Lambda(body, env, params)) => {
                let env = Env::extend_envoirnment(env.clone(), *params.clone(), args)?;
                Evaluator::eval_sequence(*body.clone(), env)
            }
            Self::Primitive(p) => p(args),
        }
    }
}

#[derive(Clone)]
pub struct Lambda(Box<Ast>, EnvRef, Box<Ast>);

impl PartialEq for Lambda {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}
impl fmt::Debug for Lambda {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(lambda {} {}", self.2, self.0)
    }
}
type Primitive = fn(Ast) -> Result<Ast, String>;
#[derive(Clone, PartialEq, Debug)]
pub struct Pair(pub Ast, pub Ast);

impl Pair {
    pub fn map(&self, mut f: impl FnMut(Ast) -> Result<Ast, String>) -> Result<Ast, String> {
        let car = f(self.0.clone())?;
        let cdr = self.1.map(f)?;
        Ok(Ast::Pair(Box::new(Self(car, cdr))))
    }
    #[must_use]
    pub fn list(&self) -> bool {
        self.1.list()
    }
    #[must_use]
    pub fn size(&self) -> usize {
        1 + self.1.size()
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Ast {
    Pair(Box<Pair>),
    TheEmptyList,
    Syntax(Syntax),
    Number(f64),
    Symbol(Symbol),
    Function(Function),
}

fn bound_identifier(a: Ast, b: Ast) -> bool {
    matches!((a, b), (Ast::Syntax(a), Ast::Syntax(b)) if a == b)
}

#[derive(Clone)]
pub struct Fix {
    pub out: Box<AstF<Fix>>,
}
impl Fix {
    #[must_use]
    pub fn new(out: Box<AstF<Self>>) -> Self {
        Self { out }
    }

    pub fn bottom_up(self, f: &mut impl FnMut(Self) -> Self) -> Self {
        // TODO: report bug where inling x results in immutable borrow error
        //let x = self.out.map(|x| Self::bottom_up(x, f));
        //f(Fix::new(Box::new(x)))
        self.catamorphism(&mut |x| f(Self::new(Box::new(x))))
    }
    pub fn top_down(self, f: &mut impl FnMut(Self) -> Self) -> Self {
        //Fix::new(Box::new(f(self).out.map(|x| x.top_down(f))))
        Self::anamorphism(self, &mut |x| *f(x).out)
    }

    pub fn catamorphism<A>(self, algebra: &mut impl FnMut(AstF<A>) -> A) -> A {
        let mapped = self.out.map(|subterm| subterm.catamorphism(algebra));
        algebra(mapped)
    }
    pub fn anamorphism<A>(term: A, coalgebra: &mut impl FnMut(A) -> AstF<A>) -> Self {
        Self::new(Box::new(
            coalgebra(term).map(|subterm| Self::anamorphism(subterm, coalgebra)),
        ))
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
pub enum AstF<A> {
    Pair(A, A),
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
            Self::Pair(car, cdr) => AstF::Pair(f(car), f(cdr)),
            Self::TheEmptyList => AstF::TheEmptyList,
            Self::Syntax(syntax) => AstF::Syntax(syntax),
            Self::Number(number) => AstF::Number(number),
            Self::Symbol(symbol) => AstF::Symbol(symbol),
            Self::Function(function) => AstF::Function(function),
        }
    }
}
impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Pair(pair) => {
                let mut string = pair.0.to_string();
                let mut second = pair.1.clone();
                while let Self::Pair(pair) = second {
                    string = format!("{string} {}", pair.0);
                    second = pair.1;
                }
                if second != Self::TheEmptyList {
                    string = format!("{string} . {second}");
                }
                write!(f, "({string})")
            }
            Self::Syntax(s) => write!(f, "#'{}", s.0),
            Self::Number(n) => write!(f, "{n}"),
            Self::Symbol(s) => write!(f, "'{s}"),
            Self::Function(function) => write!(f, "{function}"),
            Self::TheEmptyList => write!(f, "()"),
        }
    }
}
impl Ast {
    #[must_use]
    pub fn size(&self) -> usize {
        match self {
            Self::Pair(p) => p.size(),
            _ => 0,
        }
    }
    pub fn map(&self, f: impl FnMut(Self) -> Result<Self, String>) -> Result<Self, String> {
        match self {
            Self::Pair(p) => {
                let this = &p;
                let mut f = f;
                let car = f(this.0.clone())?;
                let cdr = this.1.map(f)?;
                Ok(Ast::Pair(Box::new(Pair(car, cdr))))
            }
            Self::TheEmptyList => Ok(Self::TheEmptyList),
            bad => Err(format!("cannot map {bad}")),
        }
    }
    pub fn map_pair<E>(self, mut f: impl FnMut(Self, bool) -> Result<Self, E>) -> Result<Self, E> {
        {
            match self {
                Ast::Pair(p) => {
                    let Pair(car, cdr) = *p;
                    let car = f(car, false)?;
                    let cdr = cdr.map_pair(f)?;
                    Ok(Ast::Pair(Box::new(Pair(car, cdr))))
                }
                other_term => f(other_term, true),
            }
        }
    }

    pub fn foldl_pair<A>(self, mut f: impl FnMut(Self, bool, A) -> A, init: A) -> A {
        match self {
            Ast::Pair(p) => {
                let Pair(car, cdr) = *p;
                let car = f(car, false, init);
                let cdr = cdr.foldl_pair(f, car);
                cdr
            }
            other_term => f(other_term, true, init),
        }
    }

    pub fn foldl<A>(self, mut f: impl FnMut(Self, A) -> A, init: A) -> Result<A, String> {
        self.foldl_pair(
            |term, base, init: Result<A, String>| {
                if !base {
                    init.map(|init| f(term, init))
                } else {
                    match term {
                        Ast::TheEmptyList => init,
                        _other => Err("".to_string()),
                    }
                }
            },
            Ok(init),
        )
    }
    #[must_use]
    pub fn list(&self) -> bool {
        matches!(self,  Self::Pair(p) if p.list() ) || *self == Self::TheEmptyList
    }

    #[must_use]
    pub fn datum_to_syntax(self) -> Self {
        match self {
            list if list.list() => list.map(|x| Ok(x.datum_to_syntax())).unwrap_or(list),
            Self::Syntax(_) => self,
            Self::Symbol(s) => Self::Syntax(Syntax::new(s)),
            _ => self,
        }
    }
    fn syntax_to_datum(self) -> Self {
        match self {
            list if list.list() => list.map(|x| Ok(x.syntax_to_datum())).unwrap_or(list),
            Self::Syntax(Syntax(s, _)) => Self::Symbol(s),
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
            list if list.list() => list
                .map(|x| Ok(x.adjust_scope(other_scope, operation)))
                .unwrap_or(list),
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

impl Default for Expander<Binding> {
    fn default() -> Self {
        Self::new()
    }
}

impl Expander<Binding> {
    #[must_use]
    pub fn new() -> Self {
        let mut scope_creator = UniqueNumberManager::new();
        let core_scope = scope_creator.new_scope();
        let core_forms = BTreeSet::from([
            Binding::Lambda,
            Binding::LetSyntax,
            Binding::Quote,
            Binding::QuoteSyntax,
            Binding::App,
        ]);
        let core_primitives = BTreeSet::from([
            Binding::Variable("datum->syntax".into()),
            Binding::Variable("syntax->datum".into()),
            Binding::Variable("syntax-e".into()),
            Binding::Variable("list".into()),
            Binding::Variable("cons".into()),
            Binding::Variable("car".into()),
            Binding::Variable("cdr".into()),
            Binding::Variable("map".into()),
        ]);
        let mut this = Self {
            scope_creator,
            core_scope,
            core_primitives,
            core_forms,
            all_bindings: HashMap::new(),
            env: new_env(),
        };
        this.core_forms
            .clone()
            .union(&this.core_primitives.clone())
            .for_each(|core| {
                this.add_binding(
                    Syntax(core.clone().into(), BTreeSet::from([this.core_scope])),
                    core.clone(),
                );
            });
        this
    }
    fn add_binding(&mut self, id: Syntax, binding: Binding) {
        self.all_bindings.insert(id, binding);
    }

    fn add_local_binding(&mut self, id: Syntax) -> Symbol {
        let symbol = self.scope_creator.gen_sym(&id.0 .0);
        self.add_binding(id, Binding::Variable(symbol.clone()));
        symbol
    }

    fn resolve(&self, id: &Syntax) -> Result<&Binding, String> {
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

    fn free_identifier(&self, a: Ast, b: Ast) -> bool {
        matches!((a, b), (Ast::Syntax(a), Ast::Syntax(b)) if self.resolve( &a).is_ok_and(|a| self.resolve(&b).is_ok_and(|b| a == b )))
    }

    fn find_all_matching_bindings<'a>(
        &'a self,
        id: &'a Syntax,
    ) -> impl Iterator<Item = &Syntax> + Clone + 'a {
        self.all_bindings
            .keys()
            .filter(move |c_id| c_id.0 == id.0 && c_id.1.is_subset(&id.1))
    }

    pub fn namespace_syntax_introduce<T: AdjustScope>(&self, s: T) -> T {
        s.add_scope(self.core_scope)
    }

    #[trace::trace()]
    pub fn expand(&mut self, s: Ast, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        match s {
            Ast::Syntax(s) => self.expand_identifier(s, env),
            Ast::Pair(l) if matches!(&l.0, Ast::Syntax(_)) => {
                self.expand_id_application_form(*l, env)
            }
            Ast::Pair(l) => self.expand_app(*l, env),
            _ => Ok(Ast::Pair(Box::new(Pair(
                Ast::Syntax(Syntax("quote".into(), BTreeSet::from([self.core_scope]))),
                Ast::Pair(Box::new(Pair(s, Ast::TheEmptyList))),
            )))),
        }
    }

    fn expand_identifier(&mut self, s: Syntax, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        let binding = self.resolve(&s)?;
        if self.core_forms.contains(binding) {
            Err(format!("bad syntax dangling core form {}", s.0))
        } else if self.core_primitives.contains(binding) {
            Ok(Ast::Syntax(s))
        } else {
            //println!("{:?}", env);
            let Binding::Variable(binding) = binding else {
                panic!()
            };
            let v = env.lookup(binding).ok_or(format!("out of context {s:?}"))?;
            match v {
                CompileTimeBinding::Symbol(_) => Ok(Ast::Syntax(s)),
                CompileTimeBinding::Macro(m) => self.apply_transformer(m, Ast::Syntax(s)), //_ => Err(format!("bad syntax non function call macro {}", s.0)),
            }
        }
    }

    // constraints = s.len() > 0
    // constraints = s[0] == Ast::Syntax(_)
    fn expand_id_application_form(
        &mut self,
        s: Pair,
        env: CompileTimeEnvoirnment,
    ) -> Result<Ast, String> {
        let Ast::Syntax(ref id) = s.0 else {
            unreachable!()
        };
        let binding = self.resolve(id)?;
        match binding {
            Binding::Lambda => self.expand_lambda(s, env),
            Binding::LetSyntax => self.expand_let_syntax(s, env),
            Binding::Quote | Binding::QuoteSyntax => Ok(Ast::Pair(Box::new(s))),
            Binding::App => {
                if !s.list() {
                    Err(format!("%app form's arguements must be a list"))?
                }
                // TODO: empty list
                let Ast::Pair(p) = s.1 else { unreachable!() };
                self.expand_app(*p, env)
            }
            Binding::Variable(binding) => match env.lookup(binding) {
                Some(CompileTimeBinding::Macro(m)) => {
                    //println!("{binding} in {env:?}");
                    let apply_transformer = self.apply_transformer(m, Ast::Pair(Box::new(s)))?;
                    //println!("app {apply_transformer}");
                    self.expand(apply_transformer, env)
                }
                _ => self.expand_app(s, env),
            },
        }
    }
    fn apply_transformer(&mut self, m: Function, s: Ast) -> Result<Ast, String> {
        let intro_scope = self.scope_creator.new_scope();
        //println!("apply_transformer {s:?}");
        let intro_s = s.add_scope(intro_scope);
        let transformed_s = m.apply(Ast::Pair(Box::new(Pair(intro_s, Ast::TheEmptyList))))?;

        Ok(transformed_s.flip_scope(intro_scope))
    }
    fn expand_app(&mut self, s: Pair, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        let Pair(rator, rands) = s;

        Ok(Ast::Pair(Box::new(Pair(
            Ast::Syntax(Syntax("%app".into(), BTreeSet::from([self.core_scope]))),
            Ast::Pair(Box::new(Pair(
                self.expand(rator, env.clone())?,
                rands.map(|rand| self.expand(rand, env.clone()))?,
            ))),
        ))))
    }

    fn expand_lambda(&mut self, s: Pair, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        //println!("lambda body {s:?}");
        let Pair(ref lambda_id, Ast::Pair(ref inner)) = s else {
            Err(format!("invalid syntax {s:?} bad lambda"))?
        };
        let Pair(ref args, Ast::Pair(ref body)) = **inner else {
            Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
        };
        let sc = self.scope_creator.new_scope();
        let args = args.clone().map_pair(|term, base| match term {
            Ast::Syntax(id) => {
                let id = id.add_scope(sc);
                Ok(Ast::Syntax(id))
            }
            Ast::TheEmptyList if base => Ok(Ast::TheEmptyList),
            _ => Err(format!(
                "{term} is not a symbol so it cannot be a parameter"
            )),
        })?;
        let body_env = args.clone().foldl_pair(
            |term, base, env: Result<CompileTimeEnvoirnment, String>| match term {
                Ast::Syntax(id) => {
                    let binding = self.add_local_binding(id);
                    env.map(|env| env.extend(binding.clone(), CompileTimeBinding::Symbol(binding)))
                }
                Ast::TheEmptyList if base => env,
                _ => Err(format!(
                    "{term} is not a symbol so it cannot be a parameter"
                )),
            },
            Ok(env),
        )?;
        let Pair(ref body, Ast::TheEmptyList) = **body else {
            Err(format!("invalid syntax {s:?}, bad argument for lambda"))?
        };
        let exp_body = self.expand(body.clone().add_scope(sc), body_env)?;
        Ok(Ast::Pair(Box::new(Pair(
            lambda_id.clone(),
            Ast::Pair(Box::new(Pair(
                args,
                Ast::Pair(Box::new(Pair(exp_body, Ast::TheEmptyList))),
            ))),
        ))))
    }

    fn expand_let_syntax(&mut self, s: Pair, env: CompileTimeEnvoirnment) -> Result<Ast, String> {
        // `(,let-syntax-id ([,lhs-id ,rhs])
        //            ,body)
        // (cons 'let-syntax (cons (cons (cons 'lhs (cons 'rhs '())) '()) (cons 'body '())))
        let Pair(ref _let_syntax_id, Ast::Pair(ref inner)) = s else {
            Err(format!("invalid syntax {s:?} bad let-syntax"))?
        };
        let Pair(Ast::Pair(ref binder_list), Ast::Pair(ref body)) = **inner else {
            Err(format!("invalid syntax {s:?} bad let-syntax {:?}", inner.0))?
        };
        let Pair(Ast::Pair(ref binder_list), Ast::TheEmptyList) = **binder_list else {
            Err(format!(
                "invalid syntax {s:?}, bad binder list for let-syntax {binder_list:?}"
            ))?
        };
        let Pair(Ast::Syntax(ref lhs_id), Ast::Pair(ref rhs_list)) = **binder_list else {
            Err(format!(
                "invalid syntax {s:?}, bad binder for let-syntax {binder_list:?}"
            ))?
        };
        let Pair(ref rhs, Ast::TheEmptyList) = **rhs_list else {
            Err(format!(
                "invalid syntax {s:?}, bad binder list for let-syntax {rhs_list:?}"
            ))?
        };
        let Pair(ref body, Ast::TheEmptyList) = **body else {
            Err(format!(
                "invalid syntax {s:?}, bad binder list for let-syntax {body:?}"
            ))?
        };
        let sc = self.scope_creator.new_scope();
        let id = lhs_id.clone().add_scope(sc);
        let binding = self.add_local_binding(id);
        let rhs_val = self.eval_for_syntax_binding(rhs.clone())?;
        let body_env = env.extend(binding, rhs_val);
        //println!("found macro {binding}");
        //println!("expand {body} in {body_env:?}");
        self.expand(body.clone().add_scope(sc), body_env)
    }

    fn eval_for_syntax_binding(&mut self, rhs: Ast) -> Result<CompileTimeBinding, String> {
        // let var_name = format!("problem `evaluating` macro {rhs}");
        //println!("macro body {rhs}");
        let expand = self.expand(rhs, CompileTimeEnvoirnment::new())?;
        //println!("macro body {expand}");
        self.eval_compiled(self.compile(expand)?).and_then(|e| {
            if let Ast::Function(f) = e {
                Ok(CompileTimeBinding::Macro(f))
            } else {
                Err(format!("{e} is not a macro"))
            }
        })
    }

    #[trace::trace()]
    fn compile(&self, rhs: Ast) -> Result<Ast, String> {
        println!("compile {rhs}");
        match rhs {
            Ast::Pair(l) => {
                let core_sym = if let Ast::Syntax(ref s) = l.0 {
                    self.resolve(s)
                } else {
                    Err("just for _ case in next match does not actually error".to_string())
                };
                match core_sym {
                    Ok(Binding::Lambda) => {
                        let Pair(ref _lambda_id, Ast::Pair(ref inner)) = *l else {
                            Err(format!("invalid syntax {l:?} bad lambda"))?
                        };
                        let Pair(ref args, Ast::Pair(ref body)) = **inner else {
                            Err(format!("invalid syntax {inner:?}, bad form for lambda"))?
                        };

                        let args = args.clone().map_pair(|term, base| match term {
                            Ast::Syntax(id) => {
                                let Binding::Variable(id) = self.resolve(&id)? else {
                                    Err("bad syntax cannot play with core form")?
                                };
                                Ok(Ast::Symbol(id.clone()))
                            }
                            Ast::TheEmptyList if base => Ok(Ast::TheEmptyList),
                            _ => Err(format!(
                                "{term} is not a symbol so it cannot be a parameter"
                            )),
                        })?;
                        let Pair(ref body, Ast::TheEmptyList) = **body else {
                            Err(format!("invalid syntax {body:?}, bad body for lambda"))?
                        };

                        // (list 'lambda (list 'x) 'body)
                        Ok(Ast::Pair(Box::new(Pair(
                            Ast::Symbol(Symbol("lambda".into(), 0)),
                            Ast::Pair(Box::new(Pair(
                                args,
                                Ast::Pair(Box::new(Pair(
                                    self.compile(body.clone())?,
                                    Ast::TheEmptyList,
                                ))),
                            ))),
                        ))))
                    }
                    Ok(Binding::Quote) => {
                        let Pair(_, Ast::Pair(datum)) = *l else {
                            Err("bad syntax, quote requires one expression")?
                        };
                        let Pair(datum, Ast::TheEmptyList) = *datum else {
                            Err("bad syntax, quote requires one expression")?
                        };
                        Ok(Ast::Pair(Box::new(Pair(
                            Ast::Symbol(Symbol("quote".into(), 0)),
                            Ast::Pair(Box::new(Pair(datum.syntax_to_datum(), Ast::TheEmptyList))),
                        ))))
                    }
                    Ok(Binding::QuoteSyntax) => {
                        let Pair(_, Ast::Pair(datum)) = *l else {
                            Err("bad syntax, quote-syntax requires one expression")?
                        };
                        let Pair(datum, Ast::TheEmptyList) = *datum else {
                            Err("bad syntax, quote-syntax requires one expression")?
                        };
                        Ok(Ast::Pair(Box::new(Pair(
                            Ast::Symbol(Symbol("quote".into(), 0)),
                            Ast::Pair(Box::new(Pair(datum, Ast::TheEmptyList))),
                        ))))
                    }
                    Ok(Binding::App) => {
                        let Pair(_, Ast::Pair(app)) = *l else {
                            Err("bad syntax, %app requires at least a function")?
                        };
                        if !app.1.list() {
                            Err("bad syntax, %app arguments must be a list")?
                        }
                        Ok(Ast::Pair(Box::new(Pair(
                            self.compile(app.0)?,
                            app.1.map(|e| self.compile(e))?,
                        ))))
                    }
                    _ => Err(format!("unrecognized core form {}", l.0)),
                }
            }
            Ast::Syntax(s) => {
                if let Binding::Variable(s) = self.resolve(&s)? {
                    Ok(Ast::Symbol(s.clone()))
                } else {
                    Err("bad syntax cannot play with core form")?
                }
            }
            Ast::Number(_) | Ast::Function(_) => Ok(rhs),
            Ast::Symbol(_) | Ast::TheEmptyList => unreachable!(),
        }
    }

    fn eval_compiled(&self, new: Ast) -> Result<Ast, String> {
        //println!("body {new}");
        Evaluator::eval(new, self.env.clone())
    }
}

fn new_env() -> Rc<RefCell<Env>> {
    let env = Env::new();
    env.borrow_mut().define(
        Symbol("datum->syntax".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let Ast::Pair(e) = e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };
            let Pair(e, Ast::TheEmptyList) = *e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };
            Ok(e.datum_to_syntax())
        })),
    );
    env.borrow_mut().define(
        Symbol("syntax->datum".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let Ast::Pair(e) = e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };
            let Pair(e, Ast::TheEmptyList) = *e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };
            Ok(e.syntax_to_datum())
        })),
    );
    env.borrow_mut().define(
        Symbol("syntax-e".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let Ast::Pair(e) = e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };
            let Pair(Ast::Syntax(Syntax(e, _)), Ast::TheEmptyList) = *e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };
            Ok(Ast::Symbol(e))
        })),
    );
    env.borrow_mut().define(
        Symbol("cons".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let Ast::Pair(e) = e else {
                Err(format!(
                    "arity error: expected 2 argument, got {}",
                    e.size()
                ))?
            };
            let Pair(ref fst, Ast::Pair(ref last)) = *e else {
                Err(format!(
                    "arity error: expected 2 argument, got {}",
                    e.size()
                ))?
            };
            let Pair(ref snd, Ast::TheEmptyList) = **last else {
                Err(format!(
                    "arity error: expected 2 argument, got {}",
                    e.size()
                ))?
            };
            Ok(Ast::Pair(Box::new(Pair(fst.clone(), snd.clone()))))
        })),
    );
    env.borrow_mut().define(
        Symbol("car".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let Ast::Pair(e) = e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };

            let Pair(Ast::Pair(e), Ast::TheEmptyList) = *e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };
            let Pair(fst, _) = *e;
            Ok(fst)
        })),
    );
    env.borrow_mut().define(
        Symbol("cdr".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            println!("cdr {e}");
            let Ast::Pair(e) = e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };
            let Pair(Ast::Pair(e), Ast::TheEmptyList) = *e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };
            let Pair(_, snd) = *e;
            Ok(snd)
        })),
    );
    env.borrow_mut().define(
        Symbol("list".into(), 0),
        Ast::Function(Function::Primitive(Ok)),
    );
    env.borrow_mut().define(
        Symbol("map".into(), 0),
        Ast::Function(Function::Primitive(move |e| {
            let Ast::Pair(e) = e else {
                Err(format!(
                    "arity error: expected 1 argument, got {}",
                    e.size()
                ))?
            };

            let Pair(Ast::Function(ref f), Ast::Pair(ref last)) = *e else {
                Err(format!(
                    "arity error: expected 2 argument, got {}",
                    e.size()
                ))?
            };
            let Pair(ref l, Ast::TheEmptyList) = **last else {
                Err(format!(
                    "arity error: expected 2 argument, got {}",
                    e.size()
                ))?
            };
            l.map(|a| f.apply(Ast::Pair(Box::new(Pair(a, Ast::TheEmptyList)))))
        })),
    );
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
                    match (params, args) {
                        (Ast::Pair(param), Ast::Pair(arg)) => {
                            let Ast::Symbol(p) = param.0 else {
                                return Some(String::new());
                            };
                            env.borrow_mut().define(p, arg.0);
                            extend_envoirnment(env, param.1, arg.1)
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

impl Evaluator {
    #[trace]
    fn eval(expr: Ast, env: EnvRef) -> Result<Ast, String> {
        println!("eval {expr}");
        match expr {
            Ast::Pair(list) => match list.0 {
                Ast::Symbol(Symbol(ref lambda, 0)) if **lambda == *"lambda" => {
                    let Pair(ref lambda_id, Ast::Pair(ref inner)) = *list else {
                        Err(format!("invalid syntax {list:?} bad lambda"))?
                    };
                    let Pair(ref arg, Ast::Pair(ref body)) = **inner else {
                        Err(format!("invalid syntax {list:?}, bad argument for lambda"))?
                    };

                    // TODO: variadic function with dot notation
                    let args = arg.clone().map_pair(|arg, base| match arg {
                        Ast::Symbol(s) => Ok(Ast::Symbol(s)),
                        Ast::TheEmptyList if base => Ok(Ast::TheEmptyList),
                        _ => Err(format!("bad syntax {arg} is not a valid paramter")),
                    })?;
                    Ok(Ast::Function(Function::Lambda(Lambda(
                        Box::new(Ast::Pair(body.clone())),
                        env,
                        Box::new(args),
                    ))))
                }
                Ast::Symbol(Symbol(quote, 0)) if *quote == *"quote" => {
                    let Pair(_, Ast::Pair(datum)) = *list else {
                        Err("bad syntax, quote requires one expression")?
                    };
                    let Pair(datum, Ast::TheEmptyList) = *datum else {
                        Err("bad syntax, quote requires one expression")?
                    };
                    Ok(datum)
                }
                f => {
                    let f = Self::eval(f, env.clone())?;
                    let rest = list.1.map(|arg| Self::eval(arg, env.clone()))?;
                    Self::execute_application(f, rest)
                } //Ast::TheEmptyList => Err(format!("bad syntax {list:?}, empty application")),
            },
            Ast::Symbol(s) =>
            //println!("variable {s})");
            {
                env.borrow().lookup(&s).ok_or(format!("free variable {s}"))
            }
            //.inspect(|x|println!("variable {x}"))
            ,
            _ => Ok(expr.clone()),
        }
    }

    fn execute_application(f: Ast, args: Ast) -> Result<Ast, String> {
        if let Ast::Function(f) = f {
            f.apply(args)
            //.inspect(|x|println!("application {x}"))
        } else {
            Err(format!(
                "cannot not apply {f} to {args:?}, because {f} is not a function"
            ))
        }
    }

    fn eval_sequence(body: Ast, env: Rc<RefCell<Env>>) -> Result<Ast, String> {
        let Ast::Pair(pair) = body else {
            return Err(format!("not a sequence {body}"));
        };
        if pair.1 == Ast::TheEmptyList {
            Self::eval(pair.0, env)
        } else {
            Self::eval(pair.0, env.clone())?;
            Self::eval_sequence(pair.1, env)
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
                Ok(n) => Ok((Ast::Number(n), input)),
                Err(e) => Err((e.to_string(), input)),
            },

            (first, second, _) => {
                let (last, input) = Self::read_symbol_inner(input);
                Ok((
                    Ast::Symbol(Symbol(format!("{first}{second}{last}").into(), 0)),
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
        Ok((Ast::Symbol(Symbol(symbol.into(), 0)), input))
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
                Ok((Ast::TheEmptyList, input))
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
                Ok((Ast::Pair(Box::new(Pair(item, item2))), input))
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
    let mut expander = Expander::new();
    loop {
        print!("\n>> ",);

        let ast = reader
            .read_with_continue(newline)
            .inspect(|e| println!("after reader: {e}"))
            .and_then(|ast| {
                expander.expand(
                    expander.namespace_syntax_introduce(ast.datum_to_syntax()),
                    CompileTimeEnvoirnment::new(),
                )
            })
            .inspect(|e| println!("after expansion: {e}"))
            .and_then(|ast| expander.compile(ast))
            .inspect(|e| println!("after expansion part 2: {e}"))
            .and_then(|ast| expander.eval_compiled(ast));
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
//        assert!(Ast::Syntax(Syntax::new("a".into())).identifier());
//    }
//
//    #[test]
//    fn datum_to_syntax_with_identifier() {
//        assert_eq!(
//            Ast::Symbol(Symbol("a".into(), 0)).datum_to_syntax(),
//            Ast::Syntax(Syntax("a".into(), BTreeSet::new()))
//        );
//    }
//
//    #[test]
//    fn datum_to_syntax_with_number() {
//        assert_eq!(Ast::Number(1.0).datum_to_syntax(), Ast::Number(1.0));
//    }
//
//    #[test]
//    fn datum_to_syntax_with_list() {
//        assert_eq!(
//            Ast::List(vec![
//                Ast::Symbol(Symbol("a".into(), 0)),
//                Ast::Symbol(Symbol("b".into(), 0)),
//                Ast::Symbol(Symbol("c".into(), 0)),
//            ])
//            .datum_to_syntax(),
//            Ast::List(vec![
//                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
//                Ast::Syntax(Syntax("b".into(), BTreeSet::new())),
//                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
//            ])
//        );
//    }
//
//    #[test]
//    fn datum_to_syntax_with_list_and_syntax() {
//        assert_eq!(
//            Ast::List(vec![
//                Ast::Symbol(Symbol("a".into(), 0)),
//                Ast::Syntax(Syntax("b".into(), BTreeSet::from([Scope(0), Scope(1)]))),
//                Ast::Symbol(Symbol("c".into(), 0)),
//            ])
//            .datum_to_syntax(),
//            Ast::List(vec![
//                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
//                Ast::Syntax(Syntax("b".into(), BTreeSet::from([Scope(0), Scope(1)]))),
//                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
//            ])
//        );
//    }
//    #[test]
//    fn syntax_to_datum_with_identifier() {
//        assert_eq!(
//            Ast::Syntax(Syntax("a".into(), BTreeSet::new())).syntax_to_datum(),
//            Ast::Symbol(Symbol("a".into(), 0)),
//        );
//    }
//
//    #[test]
//    fn syntax_to_datum_with_number() {
//        assert_eq!(Ast::Number(1.0).syntax_to_datum(), Ast::Number(1.0));
//    }
//
//    #[test]
//    fn syntax_to_datum_with_list() {
//        assert_eq!(
//            Ast::List(vec![
//                Ast::Syntax(Syntax("a".into(), BTreeSet::new())),
//                Ast::Syntax(Syntax("b".into(), BTreeSet::new())),
//                Ast::Syntax(Syntax("c".into(), BTreeSet::new())),
//            ])
//            .syntax_to_datum(),
//            Ast::List(vec![
//                Ast::Symbol(Symbol("a".into(), 0)),
//                Ast::Symbol(Symbol("b".into(), 0)),
//                Ast::Symbol(Symbol("c".into(), 0)),
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
//            Ast::Syntax(Syntax("x".into(), BTreeSet::new())).add_scope(sc1),
//            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1])))
//        );
//    }
//
//    #[test]
//    fn add_scope_test_empty_scope_list() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        assert_eq!(
//            Ast::List(vec![
//                Ast::Symbol(Symbol("x".into(), 0)),
//                Ast::Symbol(Symbol("y".into(), 0)),
//            ])
//            .datum_to_syntax()
//            .add_scope(sc1),
//            Ast::List(vec![
//                Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))),
//                Ast::Syntax(Syntax("y".into(), BTreeSet::from([sc1]))),
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
//            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).add_scope(sc2),
//            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2])))
//        );
//    }
//
//    #[test]
//    fn add_scope_test_add_duplicate() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        assert_eq!(
//            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).add_scope(sc1),
//            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1,])))
//        );
//    }
//
//    #[test]
//    fn flip_scope_test_different() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//        assert_eq!(
//            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1]))).flip_scope(sc2),
//            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2])))
//        );
//    }
//
//    #[test]
//    fn flip_scope_test_same() {
//        let mut scope_creator = UniqueNumberManager::new();
//        let sc1 = scope_creator.new_scope();
//        let sc2 = scope_creator.new_scope();
//        assert_eq!(
//            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1, sc2]))).flip_scope(sc2),
//            Ast::Syntax(Syntax("x".into(), BTreeSet::from([sc1,])))
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
