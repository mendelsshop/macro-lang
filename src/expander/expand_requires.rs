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
    in_syntax: &Ast,
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

#[derive(PartialEq)]
enum JustMeta {
    All,
    Specific(Phase),
}
/// run: false
/// can_shadow: false
fn perform_require(
    module_path: Ast,
    this: Option<ResolvedModulePath>,
    in_syntax: &Ast,
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
        &Ast::Syntax(Box::new(to_id.clone().map(Ast::Symbol)))
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
        |binding| {
            let symbol = &binding.nominal_from_symbol;
            let provide_phase = binding.nominal_from_phase;
            let adjusted_symbol = match &adjust {
                _ if just_meta != JustMeta::All
                    && just_meta != JustMeta::Specific(provide_phase) =>
                {
                    None
                }
                Some(Adjust::Only { symbols }) => symbols.get(symbol).cloned().inspect(|s| {
                    done_symbols.insert(s.clone());
                }),
                // TODO: symbol number properly
                Some(Adjust::Prefix { symbol: adjust }) => {
                    Some(Symbol(format!("{adjust}{}", symbol.0).into(), symbol.1))
                }
                Some(Adjust::AllExcept {
                    prefix_symbol,
                    symbols,
                }) => symbols
                    .get(symbol)
                    .inspect(|s| {
                        done_symbols.insert((*s).clone());
                    })
                    .is_none()
                    .then_some(Symbol(
                        format!("{prefix_symbol}{}", symbol.0).into(),
                        symbol.1,
                    )),
                // TODO: to id seems to be a syntax object, does that mean I need to keep the
                // syntax stuff that was origanlly there, because it passes through a bunch of
                // datum to syntaxes, maybe just also attach a syntax object with ()
                Some(Adjust::Rename { to_id, from_symbol }) => {
                    (from_symbol == symbol).then(|| -> Symbol {
                        done_symbols.insert(symbol.clone());
                        to_id.0.clone()
                    })
                }
                None => Some(symbol.clone()),
            };
            {
                let this = adjusted_symbol.as_ref();
                if let Some(ref adjusted_symbol) = this {
                    {
                        let s = (*adjusted_symbol).clone().datum_to_syntax(
                            in_syntax.scope_set(),
                            in_syntax.shifted_multi_scope_set(),
                            None,
                            None,
                        );
                        let bind_phase = phase_shift + provide_phase;
                        requires_and_provide.check_not_required_or_defined(&s, bind_phase)?;
                        requires_and_provide.add_defined_or_required_id(
                            s,
                            bind_phase,
                            binding.clone(),
                            can_shadow,
                        )
                    };
                }

                this
            };
            Ok(adjusted_symbol)
        },
    )?;

    module_namespace.namespace_module_visit(&module_name, phase_shift)?;
    if run {
        module_namespace.namespace_module_instantiate(&module_name, phase_shift, Phase(0))?;
    }
    if let Some(needs_symbols) = adjust
        .and_then(|adjust| match adjust {
            Adjust::Only { symbols } => Some(symbols),
            Adjust::AllExcept { symbols, .. } => Some(symbols),
            Adjust::Rename { from_symbol, .. } => Some(HashSet::from([from_symbol])),
            _ => None,
        })
        .filter(|need_symbols| need_symbols.len() != done_symbols.len())
    {
        needs_symbols.into_iter().try_for_each(|need_symbol| {
            if done_symbols.contains(&need_symbol) {
                Ok(())
            } else {
                Err(format!("not in nested spec: {need_symbol}"))
            }
        })
    } else {
        Ok(())
    }
}
fn bind_all_provides(
    in_syntax: &Ast,
    phase_shift: Phase,
    namespace: &NameSpace,
    module_name: &ResolvedModuleName,
    mut filter: impl FnMut(&ModuleBinding) -> Result<Option<Symbol>, String>,
) -> Result<(), String> {
    let module = namespace
        .namespace_to_module(&module_name)
        .ok_or(format!("module not declared: {module_name}"))?;
    let this = &module.self_name;
    module
        .provides
        .clone()
        .into_iter()
        .try_for_each(|(provide_level_phase, provides)| {
            let phase = phase_shift + provide_level_phase;
            provides.into_iter().try_for_each(|(symbol, binding)| {
                let from_module = &binding.from_module;
                let binding = ModuleBinding {
                    from_module: if from_module == this {
                        module_name.clone()
                    } else {
                        from_module.clone()
                    },
                    nominal_from_module: module_name.clone(),
                    nominal_from_phase: provide_level_phase,
                    nominal_from_symbol: symbol,
                    nominal_require_phase: phase_shift,
                    ..binding
                };
                if let Some(sym) = filter(&binding)? {
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
                Ok(())
            })
        })
}
