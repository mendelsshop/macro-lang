use crate::{
    ast::{syntax::Syntax, Ast, Symbol},
    expander::module_path::ModulePath,
};

use super::{
    expand_context::ExpandContext, module_path::ResolvedModulePath, phase::Phase,
    require_and_provide::RequiresAndProvides, Expander,
};

#[derive(PartialEq)]
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
) -> Result<(), String> {
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
    ) -> Result<(), String> {
        todo!()
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
    fields: Vec<Syntax<Symbol>>,
    at_phase: Phase,
    require_and_provide: &RequiresAndProvides,
) -> Result<(), String> {
    todo!()
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
        None,
        except_ids,
        None,
        at_phase,
        require_and_provide,
    )
}
fn parse_all_from_module(
    mod_name: ResolvedModulePath,
    matching_syntax: Option<Ast>,
    except_ids: Vec<Syntax<Symbol>>,
    prefix_symbol: Option<Symbol>,
    at_phase: Phase,
    require_and_provide: &RequiresAndProvides,
) -> Result<(), String> {
    todo!()
}
