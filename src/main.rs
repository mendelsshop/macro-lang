#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![deny(static_mut_refs)]
#![deny(clippy::use_self, rust_2018_idioms, clippy::missing_panics_doc)]
use std::io::{BufRead, BufReader, Write};

use ast::{scope::Scope, Ast, Symbol};
use expander::{binding::CompileTimeEnvoirnment, Expander};

trace::init_depth_var!();

mod ast;
mod evaluator;
mod expander;
mod primitives;
mod reader;

// use trace::trace;
// #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
// struct Scope(usize);
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

impl Ast {
    // pub fn list_with_length(self, length: usize) -> Result<Vec<Ast>, Ast> {
    //     match self {
    //         Self::List(l) if l.len() == length => Ok(l),
    //         _ => Err(self),
    //     }
    // }

    // pub fn datum_to_syntax(self) -> Self {
    //     match self {
    //         Self::List(l) => Self::List(l.into_iter().map(Self::datum_to_syntax).collect()),
    //         Self::Syntax(_) => self,
    //         Self::Symbol(s) => Self::Syntax(Syntax::new(s)),
    //         _ => self,
    //     }
    // }
    // fn syntax_to_datum(self) -> Self {
    //     match self {
    //         Self::List(l) => Self::List(l.into_iter().map(Self::syntax_to_datum).collect()),
    //         Self::Syntax(Syntax(s, _)) => Self::Symbol(s),
    //         _ => self,
    //     }
    // }
    // fn identifier(&self) -> bool {
    //         matches!(self, Self::Syntax(_))
    //     }
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
                    expander.namespace_syntax_introduce(ast.datum_to_syntax(None, None, None)),
                    CompileTimeEnvoirnment::new(),
                )
            })
            .inspect(|e| println!("after expansion: {e}"))
            .and_then(|ast| expander.compile(ast))
            .inspect(|e| println!("after expansion part 2: {e}"))
            .and_then(|ast| expander.run_time_eval(ast));
        match ast {
            Ok(expr) => println!("{expr}"),
            Err(e) => println!("{e}"),
        }
    }
}
