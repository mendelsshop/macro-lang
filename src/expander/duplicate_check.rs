use std::collections::HashMap;

use crate::ast::{syntax::Syntax, Ast, Symbol};

use super::phase::Phase;

pub type DuplicateMap = HashMap<Symbol, Vec<Syntax<Symbol>>>;

#[allow(non_upper_case_globals)]
pub const make_check_no_duplicate_table: fn() -> DuplicateMap = DuplicateMap::new;
pub fn check_no_duplicate_ids(
    ids: Vec<Syntax<Symbol>>,
    phase: Phase,
    _s: &Ast,
    ht: DuplicateMap,
) -> Result<DuplicateMap, String> {
    ids.into_iter().try_fold(ht, |mut ht, v| {
        if let Some(ids) = ht.get_mut(&v.0) {
            if ids.iter().any(|id| id.bound_identifier(&v, phase)) {
                Err(format!("duplicate binding: {v:?}"))
            } else {
                ids.push(v);
                Ok(ht)
            }
        } else {
            ht.insert(v.0.clone(), vec![v]);
            Ok(ht)
        }
    })
}
