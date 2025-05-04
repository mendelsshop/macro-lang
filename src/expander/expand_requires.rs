use std::collections::HashSet;

use matcher::match_syntax;

use crate::{
    ast::{syntax::Syntax, Ast, Symbol},
    sexpr,
};

use super::{
    binding::{Binding, ModuleBinding},
    module_path::{ModulePath, ResolvedModulePath},
    namespace::{NameSpace, ResolvedModuleName},
    phase::Phase,
    require_and_provide::RequiresAndProvides,
    Expander,
};

#[derive(Clone)]
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
#[macro_export]
macro_rules! matches_to {
    ($e:expr => $s:path) => {
        match $e {
            $s(e) => Some(e),
            _ => None,
        }
    };
    ($e:expr => $s:path | this) => {
        match $e {
            $s(v) => Ok(v),
            e => Err(e),
        }
    };
    ($e:expr => $s:path | $r:expr) => {
        match $e {
            $s(e) => Ok(e),
            _ => Err($r),
        }
    };
}
#[derive(PartialEq, Clone, Copy)]
enum Layer {
    Raw,
    RawNoJustMeta,
    Phaseless,
    Path,
}
const LAYERS: [Layer; 4] = [
    Layer::Raw,
    Layer::RawNoJustMeta,
    Layer::Phaseless,
    Layer::Path,
];

fn is_nested(layer: Layer, want_layer: Layer) -> bool {
    LAYERS
        .into_iter()
        .position(|l| layer == l)
        .is_some_and(|pos| LAYERS.split_at(pos).1.contains(&want_layer))
}
/// run defaults to false
pub fn parse_and_perform_requires(
    reqs: Ast,
    this: Option<ResolvedModulePath>,
    module_namespace: &NameSpace,
    phase_shift: Phase,
    requires_and_provide: &RequiresAndProvides,
    run: bool,
) -> Result<(), String> {
    fn parse_and_perform_requires_loop(
        reqs: Ast,
        top_req: Option<&Ast>,
        phase_shift: Phase,
        just_meta: JustMeta,
        adjust: Option<Adjust>,
        layer: Layer,
        this: Option<ResolvedModulePath>,
        module_namespace: &NameSpace,
        requires_and_provide: &RequiresAndProvides,
        run: bool,
    ) -> Result<(), String> {
        reqs.to_list_checked()?.into_iter().try_for_each(|req| {
            let check_nested = |want_layer| {
                is_nested(layer, want_layer)
                    .then_some(())
                    .ok_or(format!("invalid nesting: {req}"))
            };
            let fm: Option<Syntax<Symbol>> = if let Ast::Syntax(ref p) = req {
                Some(p)
            } else {
                None
            }
            .and_then(|s| {
                if let Ast::Pair(ref req) = s.0 {
                    Some(req)
                } else {
                    None
                }
            })
            .and_then(|p| p.0.clone().try_into().ok());
            match fm {
                Some(fm) if fm.0 == "for-meta".into() => {
                    check_nested(Layer::RawNoJustMeta)?;
                    let m = match_syntax!(
                        (for_meta phase_level spec ...)
                    )(req.clone())?;
                    // (&req).clone(),
                    let phase = parse_phase_from_syntax(m.phase_level, &req)?;
                    let spec = m.spec;
                    parse_and_perform_requires_loop(
                        spec,
                        top_req.or(Some(&req)),
                        phase_shift + phase,
                        just_meta,
                        (&adjust).clone(),
                        Layer::Phaseless,
                        (&this).clone(),
                        module_namespace,
                        (&requires_and_provide).clone(),
                        run,
                    )
                }
                Some(fm) if fm.0 == "for-syntax".into() => {
                    check_nested(Layer::RawNoJustMeta)?;
                    let m = match_syntax!( (for_syntax  spec ...))((&req).clone())?;
                    let spec = m.spec;
                    parse_and_perform_requires_loop(
                        spec,
                        top_req.or(Some(&req)),
                        phase_shift + Phase::Normal(1),
                        just_meta,
                        (&adjust).clone(),
                        Layer::Phaseless,
                        (&this).clone(),
                        module_namespace,
                        (&requires_and_provide).clone(),
                        run,
                    )
                }
                Some(fm) if fm.0 == "for-template".into() => {
                    check_nested(Layer::RawNoJustMeta)?;
                    let m = match_syntax!( (for_template  spec ...))(req.clone())?;
                    let spec = m.spec;
                    parse_and_perform_requires_loop(
                        spec,
                        top_req.or(Some(&req)),
                        phase_shift - Phase::Normal(1),
                        just_meta,
                        adjust.clone(),
                        Layer::Phaseless,
                        this.clone(),
                        module_namespace,
                        requires_and_provide,
                        run,
                    )
                }
                Some(fm) if fm.0 == "for-label".into() => {
                    check_nested(Layer::RawNoJustMeta)?;
                    let m = match_syntax!( (for_label  spec ...))(req.clone())?;
                    let spec = m.spec;
                    parse_and_perform_requires_loop(
                        spec,
                        top_req.or(Some(&req)),
                        Phase::Label,
                        just_meta,
                        adjust.clone(),
                        Layer::Phaseless,
                        this.clone(),
                        module_namespace,
                        requires_and_provide,
                        run,
                    )
                }
                Some(fm) if fm.0 == "just-meta".into() => {
                    check_nested(Layer::Raw)?;
                    let m = match_syntax!( (just_meta phase_level spec ...))(req.clone())?;

                    let phase = parse_phase_from_syntax(m.phase_level, &req)?;
                    let spec = m.spec;
                    parse_and_perform_requires_loop(
                        spec,
                        top_req.or(Some(&req)),
                        phase_shift + phase,
                        just_meta,
                        adjust.clone(),
                        Layer::RawNoJustMeta,
                        this.clone(),
                        module_namespace,
                        requires_and_provide,
                        run,
                    )
                }
                Some(fm) if fm.0 == "only".into() => {
                    check_nested(Layer::Phaseless)?;
                    let m = match_syntax!( (only  spec id ...))(req.clone())?;
                    let spec = sexpr!((#(m.spec)));
                    parse_and_perform_requires_loop(
                        spec,
                        top_req.or(Some(&req)),
                        phase_shift,
                        just_meta,
                        Some(Adjust::Only {
                            symbols: identifiers_to_symbol_set(m.id)?,
                        }),
                        Layer::Path,
                        this.clone(),
                        module_namespace,
                        requires_and_provide,
                        run,
                    )
                }
                Some(fm) if fm.0 == "prefix".into() => {
                    check_nested(Layer::Phaseless)?;
                    let m = match_syntax!( (prefix prefix:id spec ))(req.clone())?;
                    let spec = sexpr!((#(m.spec)));
                    parse_and_perform_requires_loop(
                        spec,
                        top_req.or(Some(&req)),
                        phase_shift,
                        just_meta,
                        Some(Adjust::Prefix {
                            symbol: identifier_symbol(m.prefix_id)?,
                        }),
                        Layer::Path,
                        this.clone(),
                        module_namespace,
                        requires_and_provide,
                        run,
                    )
                }
                Some(fm) if fm.0 == "all-except".into() => {
                    check_nested(Layer::Phaseless)?;
                    let m = match_syntax!( (all_except  spec id ... ))(req.clone())?;
                    let spec = sexpr!((#(m.spec)));
                    parse_and_perform_requires_loop(
                        spec,
                        top_req.or(Some(&req)),
                        phase_shift,
                        just_meta,
                        Some(Adjust::AllExcept {
                            prefix_symbol: "||".into(),
                            symbols: identifiers_to_symbol_set(m.id)?,
                        }),
                        Layer::Path,
                        this.clone(),
                        module_namespace,
                        requires_and_provide,
                        run,
                    )
                }
                Some(fm) if fm.0 == "prefix-all-except".into() => {
                    check_nested(Layer::Phaseless)?;
                    let m = match_syntax!(
                        (all_except prefix:id spec id ... )
                    )(req.clone())?;
                    let spec = sexpr!((#(m.spec)));
                    parse_and_perform_requires_loop(
                        spec,
                        top_req.or(Some(&req)),
                        phase_shift,
                        just_meta,
                        Some(Adjust::AllExcept {
                            prefix_symbol: identifier_symbol(m.prefix_id)?,
                            symbols: identifiers_to_symbol_set(m.id)?,
                        }),
                        Layer::Path,
                        this.clone(),
                        module_namespace,
                        requires_and_provide,
                        run,
                    )
                }
                Some(fm) if fm.0 == "rename".into() => {
                    check_nested(Layer::Phaseless)?;
                    let m = match_syntax!(
                        (all_except spec to:id  from:id  )
                    )(req.clone())?;
                    let spec = sexpr!((#(m.spec)));
                    parse_and_perform_requires_loop(
                        spec,
                        top_req.or(Some(&req)),
                        phase_shift,
                        just_meta,
                        Some(Adjust::Rename {
                            from_symbol: identifier_symbol(m.from_id)?,
                            to_id: m.to_id.try_into()?,
                        }),
                        Layer::Path,
                        this.clone(),
                        module_namespace,
                        requires_and_provide,
                        run,
                    )
                }
                _ => {
                    let module_path = req
                        .clone()
                        .syntax_to_datum()
                        .try_into()
                        .map_err(|_| format!("bad require spec: {req}"))?;

                    perform_require(
                        module_path,
                        this.clone(),
                        top_req.unwrap_or(&req),
                        module_namespace.clone(),
                        phase_shift,
                        just_meta,
                        adjust.clone(),
                        requires_and_provide,
                        run,
                        false,
                    )
                }
            }
        })
    }
    parse_and_perform_requires_loop(
        reqs,
        None,
        phase_shift,
        JustMeta::All,
        None,
        Layer::Raw,
        this,
        module_namespace,
        requires_and_provide,
        run,
    )
}

fn parse_phase_from_syntax(phase: Ast, req: &Ast) -> Result<Phase, String> {
    matches_to!(phase => Ast::Syntax)
        .and_then(|s| match s.0 {
            Ast::Number(e) => {
                Some(e).and_then(|n| (n.round() == n).then_some(Phase::Normal(n as isize)))
            }
            Ast::Boolean(false) => Some(Phase::Label),
            _ => None,
        })
        .ok_or(format!("bad phase: {req}"))
}

fn identifier_symbol(s: Ast) -> Result<Symbol, String> {
    Ok(TryInto::<Syntax<Symbol>>::try_into(s)?.0)
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
pub fn perform_initial_require(
    module_path: ModulePath,
    this: Option<ResolvedModulePath>,
    in_syntax: &Ast,
    module_namespace: NameSpace,
    requires_and_provide: &RequiresAndProvides,
) -> Result<(), String> {
    perform_require(
        module_path,
        this,
        in_syntax,
        module_namespace,
        Phase::Normal(0),
        JustMeta::All,
        None,
        requires_and_provide,
        false,
        true,
    )
}

#[derive(PartialEq, Clone, Copy)]
enum JustMeta {
    All,
    Specific(Phase),
}
/// run: false
/// can_shadow: false
fn perform_require(
    module_path: ModulePath,
    this: Option<ResolvedModulePath>,
    in_syntax: &Ast,
    module_namespace: NameSpace,
    phase_shift: Phase,
    just_meta: JustMeta,
    adjust: Option<Adjust>,
    requires_and_provide: &RequiresAndProvides,
    run: bool,
    can_shadow: bool,
) -> Result<(), String> {
    let module_name = module_path.resolve_module_path(this)?.ok_or(format!(""))?;
    let bind_in_syntax = if let Some(Adjust::Rename { ref to_id, .. }) = adjust {
        &Ast::Syntax(Box::new(to_id.clone().map(Ast::Symbol)))
    } else {
        in_syntax
    };

    let mut done_symbols: HashSet<Symbol> = HashSet::new();
    requires_and_provide.add_required_module(module_name.clone(), phase_shift);
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
                Some(Adjust::Only { symbols }) => symbols
                    .get(symbol)
                    .cloned()
                    .inspect(|s| {
                        done_symbols.insert(s.clone());
                    })
                    .map(SymbolOrSyntax::Symbol),
                Some(Adjust::Prefix { symbol: adjust }) => Some(SymbolOrSyntax::Symbol(Symbol(
                    format!("{adjust}{}", symbol.0).into(),
                ))),
                Some(Adjust::AllExcept {
                    prefix_symbol,
                    symbols,
                }) => symbols
                    .get(symbol)
                    .inspect(|s| {
                        done_symbols.insert((*s).clone());
                    })
                    .is_none()
                    .then_some(SymbolOrSyntax::Symbol(Symbol(
                        format!("{prefix_symbol}{}", symbol.0).into(),
                    ))),
                Some(Adjust::Rename { to_id, from_symbol }) => (from_symbol == symbol).then(|| {
                    done_symbols.insert(symbol.clone());
                    SymbolOrSyntax::Syntax(to_id.clone())
                }),
                None => Some(SymbolOrSyntax::Symbol(symbol.clone())),
            };
            {
                let this = adjusted_symbol.as_ref();
                if let Some(ref adjusted_symbol) = this {
                    {
                        let s = (*adjusted_symbol).clone().datum_to_syntax(in_syntax);
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
        module_namespace.namespace_module_instantiate(
            &module_name,
            phase_shift,
            Phase::Normal(0),
        )?;
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
#[derive(Clone)]
enum SymbolOrSyntax {
    Symbol(Symbol),
    Syntax(Syntax<Symbol>),
}

impl SymbolOrSyntax {
    fn datum_to_syntax(self, syntax: &Ast) -> Syntax<Symbol> {
        match self {
            Self::Symbol(symbol) => symbol.datum_to_syntax(
                syntax.scope_set(),
                syntax.shifted_multi_scope_set(),
                None,
                None,
            ),
            Self::Syntax(syntax) => syntax,
        }
    }
}
fn bind_all_provides(
    in_syntax: &Ast,
    phase_shift: Phase,
    namespace: &NameSpace,
    module_name: &ResolvedModuleName,
    mut filter: impl FnMut(&ModuleBinding) -> Result<Option<SymbolOrSyntax>, String>,
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
                        sym.datum_to_syntax(in_syntax),
                        phase,
                        Binding::Module(binding),
                    );
                }
                Ok(())
            })
        })
}
