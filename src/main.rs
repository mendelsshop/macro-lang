#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![deny(static_mut_refs)]
#![deny(clippy::use_self, rust_2018_idioms, clippy::missing_panics_doc)]
use std::{
    cell::RefCell,
    collections::HashMap,
    io::{BufRead, BufReader, Write},
    rc::Rc,
};

use ast::{
    scope::{MultiScope, Scope},
    Ast, Symbol,
};
use expander::Expander;

trace::init_depth_var!();

mod ast;
mod evaluator;
mod expander;
mod primitives;
mod reader;

#[derive(Debug)]
struct UniqueNumberManager(usize);

impl UniqueNumberManager {
    const fn new() -> Self {
        Self(1)
    }

    fn next(&mut self) -> usize {
        let current = self.0;
        self.0 += 1;
        current
    }

    fn new_scope(&mut self) -> Scope {
        Scope(
            self.next(),
            Rc::new(RefCell::new(HashMap::new())),
            ast::scope::ScopeData::Simple,
        )
    }
    // fn new_multi_scope(&self) -> Scope {
    //     Scope(
    //         self.next(),
    //         Rc::new(RefCell::new(HashMap::new())),
    //         ast::scope::ScopeData::Simple,
    //     )
    // }
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
                let ns = expander.namespace();
                expander.eval(ast, ns)
            });
        match ast {
            Ok(expr) => println!("{expr}"),
            Err(e) => println!("{e}"),
        }
    }
}
