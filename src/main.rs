#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![deny(static_mut_refs)]
#![deny(clippy::use_self, rust_2018_idioms, clippy::missing_panics_doc)]
use std::io::{BufRead, BufReader, Write};

use ast::{Scope, Symbol};
use expander::{CompileTimeEnvoirnment, Expander};

trace::init_depth_var!();

mod ast;
mod evaluator;
mod expander;
mod reader;
#[derive(Debug)]
struct UniqueNumberManager(usize);

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

fn main() {
    let mut reader = reader::Reader::new();
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
//
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
