use std::collections::HashSet;

use crate::ast::{syntax::Syntax, Symbol};

pub enum Adjust {
    Only {
        symbols: HashSet<Symbol>,
    },
    Prefix {
        symbol: Symbol,
    },
    AllExcept {
        prefix_symbol: Symbol,
        symbols: HashSet<Symbol>,
    },
    Rename {
        to_id: Syntax<Symbol>,
        from_symbol: Symbol,
    },
}

const LAYERS: [&str; 4] = ["raw", "raw/no-just-meta", "phaseless", "path"];

fn is_nested(layer: Symbol, want_layer: Symbol) -> bool {
    want_layer.1 == 0
        && layer.1 == 0
        && LAYERS
            .into_iter()
            .position(|l| &*layer.0 == l)
            .is_some_and(|pos| LAYERS.split_at(pos).1.contains(&&*want_layer.0))
}
fn parse_and_perform_requires() {}
fn identifiers_to_symbol_set() {}
fn perform_initial_require() {}
fn perform_require() {}
fn bind_all_provides() {}
