use std::collections::HashSet;

use crate::{
    ast::{syntax::Syntax, Ast, Symbol},
    expander::module_path::ModulePath,
    matches_to,
};

use super::{
    expand_context::ExpandContext, module_path::ResolvedModulePath, phase::Phase,
    require_and_provide::RequiresAndProvides, Expander,
};

#[derive(PartialEq, Clone, Copy)]
enum Layer {
    Raw,
    Phaseless,
    Id,
}

const LAYERS: [Layer; 3] = [Layer::Raw, Layer::Phaseless, Layer::Id];
fn is_nested(layer: Layer, want_layer: Layer) -> bool {
    LAYERS
        .into_iter()
        .position(|l| layer == l)
        .is_some_and(|pos| LAYERS.split_at(pos).1.contains(&want_layer))
}

pub fn parse_and_expand_provides(
    specs: Ast,
    require_and_provide: &RequiresAndProvides,
    self_name: Option<ResolvedModulePath>,
    phase: Phase,
    context: ExpandContext,
    expand: fn(&mut Expander, s: Ast, ctx: ExpandContext) -> Result<Ast, String>,
    rebuild: fn(Ast, Ast) -> Ast,
) -> Result<Vec<Ast>, String> {
    fn parse_and_expand_provides_loop(
        specs: Ast,
        at_phase: Phase,
        protected: bool,
        layer: Layer,
        require_and_provide: &RequiresAndProvides,
        self_name: Option<ResolvedModulePath>,
        phase: Phase,
        context: ExpandContext,
        expand: fn(&mut Expander, s: Ast, ctx: ExpandContext) -> Result<Ast, String>,
        rebuild: fn(Ast, Ast) -> Ast,
    ) -> Result<Vec<Ast>, String> {
        specs.foldl(
            |spec, current| {
                let mut current = current?;
                let check_nested = |want_layer| {
                    is_nested(layer, want_layer)
                        .then_some(())
                        .ok_or(format!("invalid nesting: {spec}"))
                };
                let fm: Option<Syntax<Symbol>> = matches_to!(&spec => Ast::Syntax)
                    .and_then(|s| matches_to!(&s.0 => Ast::Pair))
                    .and_then(|p| p.0.clone().try_into().ok());

                match fm {
                    Some(fm) if fm.0 == "for-meta".into() => todo!(),
                    Some(fm) if fm.0 == "for-syntax".into() => todo!(),
                    Some(fm) if fm.0 == "for-label".into() => todo!(),
                    Some(fm) if fm.0 == "protect".into() => todo!(),
                    Some(fm) if fm.0 == "rename".into() => todo!(),
                    Some(fm) if fm.0 == "struct".into() => todo!(),
                    Some(fm) if fm.0 == "all-from".into() => todo!(),
                    Some(fm) if fm.0 == "all-from-except".into() => todo!(),
                    Some(fm) if fm.0 == "all-defined".into() => todo!(),
                    Some(fm) if fm.0 == "all-defined-except".into() => todo!(),
                    Some(fm) if fm.0 == "prefix-all-defined".into() => todo!(),
                    Some(fm) if fm.0 == "prefix-all-defined-except".into() => todo!(),
                    Some(fm) if fm.0 == "expand".into() => todo!(),
                    _ => match spec.clone().try_into() {
                        Ok(spec_ident) => {
                            parse_identifier(
                                &spec_ident,
                                spec_ident.0.clone(),
                                at_phase,
                                require_and_provide,
                            );
                            current.push(spec);
                            Ok(current)
                        }
                        Err(_) => Err(format!("bad provide spec: {spec}")),
                    },
                }
            },
            Ok(vec![]),
        )?
    }
    parse_and_expand_provides_loop(
        specs,
        phase,
        false,
        Layer::Raw,
        require_and_provide,
        self_name,
        phase,
        context,
        expand,
        rebuild,
    )
}

fn parse_identifier(
    spec: &Syntax<Symbol>,
    symbol: Symbol,
    at_phase: Phase,
    require_and_provide: &RequiresAndProvides,
) -> Result<(), String> {
    let b = Expander::resolve(spec, at_phase, false)
        .map_err(|_| format!("provided identifier is not defined or required {spec}"))?;
    require_and_provide.add_provide(symbol, at_phase, b, spec)
}

fn parse_struct(
    id_struct: Syntax<Symbol>,
    // this can technically, be a references and array
    fields: Vec<Syntax<Symbol>>,
    at_phase: Phase,
    require_and_provide: &RequiresAndProvides,
) -> Result<(), String> {
    macro_rules! fmt {
        ($fmt:literal) => {{
            let sym: Symbol = format!($fmt, id_struct.0).as_str().into();
            sym.datum_to_syntax(
                Some(id_struct.1.clone()),
                Some(id_struct.2.clone()),
                Some(id_struct.3.clone()),
                None,
            )
        }};
        ($fmt:literal, $e:expr) => {{
            let sym: Symbol = format!($fmt, id_struct.0, $e).as_str().into();
            sym.datum_to_syntax(
                Some(id_struct.1.clone()),
                Some(id_struct.2.clone()),
                Some(id_struct.3.clone()),
                None,
            )
        }};
    }
    [fmt!("{}"), fmt!("make-{}"), fmt!("struct:{}"), fmt!("{}?")]
        .into_iter()
        .try_for_each(|id| parse_identifier(&id.clone(), id.0, at_phase, require_and_provide))?;
    fields.into_iter().try_for_each(|field| {
        let get_id = fmt!("{}-{}", field);
        let set_id = fmt!("set-{}-{}!", field);
        parse_identifier(&get_id.clone(), get_id.0, at_phase, require_and_provide)?;
        parse_identifier(&set_id.clone(), set_id.0, at_phase, require_and_provide)
    })
}

fn parse_all_from(
    mod_path_syntax: Ast,
    self_name: Option<ResolvedModulePath>,
    except_ids: Vec<Syntax<Symbol>>,
    at_phase: Phase,
    require_and_provide: &RequiresAndProvides,
) -> Result<(), String> {
    let mod_path = mod_path_syntax.syntax_to_datum();
    let module_path: ModulePath = mod_path.try_into()?;
    let module_name = module_path
        .resolve_module_path(self_name)?
        .ok_or(format!(""))?;
    parse_all_from_module(
        module_name,
        &None,
        except_ids,
        None,
        at_phase,
        require_and_provide,
    )
}
fn parse_all_from_module(
    mod_name: ResolvedModulePath,
    matching_syntax: &Option<Ast>,
    except_ids: Vec<Syntax<Symbol>>,
    prefix_symbol: Option<Symbol>,
    at_phase: Phase,
    require_and_provide: &RequiresAndProvides,
) -> Result<(), String> {
    let requireds = require_and_provide
        .extract_module_requires(&mod_name, at_phase)
        .ok_or(format!(
            "no requires from module path: {mod_name} at phase: {at_phase}"
        ))?
        .clone();
    //.into_iter();
    let add_prefix = |sym: Symbol| {
        prefix_symbol
            .clone()
            .map_or::<Symbol, _>(sym.clone(), |prefix_symbol| {
                Symbol(format!("{prefix_symbol}{}", sym.0).into(), sym.1)
            })
    };
    let mut found = HashSet::new();
    for i in &requireds {
        let id = &i.id;
        let phase = i.phase;
        if !(matching_syntax.as_ref().is_some_and(|matching_syntax| {
            !id.free_identifier(
                &id.0.clone().datum_to_syntax(
                    matching_syntax.scope_set(),
                    matching_syntax.shifted_multi_scope_set(),
                    None,
                    None,
                ),
                phase,
            ) | (except_ids.iter().any(|except_id| {
                id.free_identifier(except_id, phase) && (found.insert(except_id) || true)
            }))
        })) {
            require_and_provide.add_provide(
                add_prefix(id.0.clone()),
                phase,
                Expander::resolve(&id, phase, false)?,
                id,
            );
        }
    }
    if found.len() != except_ids.len() {
        for except_id in &except_ids {
            if !(found.contains(except_id)
                || requireds
                    .iter()
                    .any(|i| i.id.free_identifier(except_id, i.phase)))
            {
                return Err(matching_syntax.as_ref().map_or_else(
                    || format!("exluded identifier was not required in the module {except_id}"),
                    |_| format!("exluded identifier was not defined in the module {except_id}"),
                ));
            }
        }
    }
    Ok(())
}
