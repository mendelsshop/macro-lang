use std::collections::HashSet;

use crate::ast::{syntax::Syntax, Ast, Symbol};

use super::{
    binding::{Binding, ModuleBinding},
    module_path::{ModulePath, ResolvedModulePath},
    namespace::{NameSpace, ResolvedModuleName},
    phase::Phase,
    require_and_provide::RequiresAndProvides,
    Expander,
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
    let module_name = ModulePath::try_from(module_path)?
        .resolve_module_path(this)?
        .ok_or(format!(""))?;
    let bind_in_syntax = if let Some(Adjust::Rename { ref to_id, .. }) = adjust {
        Ast::Syntax(Box::new(to_id.clone().map(Ast::Symbol)))
    } else {
        in_syntax
    };

    let mut done_symbols: HashSet<Symbol> = HashSet::new();
    requires_and_provide.add_required_module(module_name.clone(), phase_shift);
    // TODO: unify resolved module path and resovled module name
    bind_all_provides(
        bind_in_syntax,
        phase_shift,
        &module_namespace,
        &module_name,
        |_| None,
    )?;
    module_namespace.namespace_module_visit(&module_name, phase_shift)?;
    if run {
        module_namespace.namespace_module_instantiate(&module_name, phase_shift, Phase(0))?;
    }
    todo!()
}
fn bind_all_provides(
    in_syntax: Ast,
    phase_shift: Phase,
    namespace: &NameSpace,
    module_name: &ResolvedModuleName,
    mut filter: impl FnMut(&ModuleBinding) -> Option<Symbol>,
) -> Result<(), String> {
    let module = namespace
        .namespace_to_module(&module_name)
        .ok_or(format!("module not declared: {module_name}"))?;
    let this = &module.self_name;
    module
        .provides
        .clone()
        .into_iter()
        .for_each(|(provide_level_phase, provides)| {
            let phase = phase_shift + provide_level_phase;
            provides.into_iter().for_each(|(symbol, binding)| {
                let from_module = &binding.from_module;
                let binding = ModuleBinding {
                    from_module: if from_module == this {
                        module_name.clone()
                    } else {
                        from_module.clone()
                    },
                    norminal_from_module: module_name.clone(),
                    norminal_from_phase: provide_level_phase,
                    norminal_from_symbol: symbol,
                    norminal_require_phase: phase_shift,
                    ..binding
                };
                if let Some(sym) = filter(&binding) {
                    Expander::add_binding(
                        sym.datum_to_syntax(
                            in_syntax.scope_set(),
                            in_syntax.shifted_multi_scope_set(),
                            None,
                            None,
                        ),
                        phase,
                        Binding::Module(binding),
                    );
                }
            });
        });
    Ok(())
}
