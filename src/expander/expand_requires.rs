use std::collections::HashSet;

use crate::ast::{syntax::Syntax, Ast, Symbol};

use super::{
    binding::ModuleBinding,
    module_path::ResolvedModulePath,
    namespace::{NameSpace, ResolvedModuleName},
    phase::Phase,
    require_and_provide::RequiresAndProvides,
};

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
fn parse_and_perform_requires(
    reqs: Ast,
    this: Option<ResolvedModulePath>,
    module_namespace: NameSpace,
    phase_shift: Phase,
    requires_and_provide: RequiresAndProvides,
    run: bool,
) -> Result<(), String> {
    Ok(())
}
fn identifiers_to_symbol_set(ids: Ast) -> Result<HashSet<Symbol>, String> {
    ids.foldl(
        |item, x| {
            x.and_then(|mut x| {
                (x.insert(Syntax::try_from(item)?.0));
                Ok(x)
            })
        },
        Ok(HashSet::new()),
    )?
}
fn perform_initial_require(
    module_path: Ast,
    this: Option<ResolvedModulePath>,
    in_syntax: Ast,
    module_namespace: NameSpace,
    requires_and_provide: RequiresAndProvides,
) -> Result<(), String> {
    perform_require(
        module_path,
        this,
        in_syntax,
        module_namespace,
        Phase(0),
        JustMeta::All,
        None,
        requires_and_provide,
        false,
        true,
    )
}

enum JustMeta {
    All,
    Specific(Phase),
}
/// run: false
/// can_shadow: false
fn perform_require(
    module_path: Ast,
    this: Option<ResolvedModulePath>,
    in_syntax: Ast,
    module_namespace: NameSpace,
    phase_shift: Phase,
    just_meta: JustMeta,
    adjust: Option<Adjust>,
    requires_and_provide: RequiresAndProvides,
    run: bool,
    can_shadow: bool,
) -> Result<(), String> {
    Ok(())
}
fn bind_all_provides(
    in_syntax: Ast,
    phase_shift: Phase,
    namespace: NameSpace,
    module_name: ResolvedModuleName,
    filter: impl FnMut(ModuleBinding) -> Option<Symbol>,
) -> Result<(), String> {
    Ok(())
}
