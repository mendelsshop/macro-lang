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
