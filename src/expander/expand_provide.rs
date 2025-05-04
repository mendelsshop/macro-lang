use std::collections::HashSet;

use matcher::match_syntax;

use crate::{
    ast::{syntax::Syntax, Ast, Symbol},
    expander::{expand::rebuild, module_path::ModulePath},
    list, matches_to, sexpr,
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

impl Expander {
    pub fn parse_and_expand_provides(
        &mut self,
        specs: Ast,
        require_and_provide: &RequiresAndProvides,
        self_name: Option<ResolvedModulePath>,
        phase: Phase,
        context: ExpandContext,
    ) -> Result<Ast, String> {
        self.parse_and_expand_provides_loop(
            specs,
            phase,
            false,
            Layer::Raw,
            require_and_provide,
            self_name,
            phase,
            context,
        )
    }
    fn parse_and_expand_provides_loop(
        &mut self,
        specs: Ast,
        at_phase: Phase,
        protected: bool,
        layer: Layer,
        require_and_provide: &RequiresAndProvides,
        self_name: Option<ResolvedModulePath>,
        phase: Phase,
        context: ExpandContext,
    ) -> Result<Ast, String> {
        // TODO: optimize the appends using cps/boxed fns (basically append in reverse)
        // or maybe convert to vec which has better end insertion speed and see if the linked list
        // to vector is not that bad
        specs.foldl(
            |spec, current| {
                let  current = current?;
                let check_nested = |want_layer| {
                    is_nested(layer, want_layer)
                        .then_some(())
                        .ok_or(format!("invalid nesting: {spec}"))
                };
                let fm: Option<Syntax<Symbol>> = matches_to!(&spec => Ast::Syntax)
                    .and_then(|s| matches_to!(&s.0 => Ast::Pair))
                    .and_then(|p| p.0.clone().try_into().ok());

                match fm {
                    Some(fm) if fm.0 == "for-meta".into() => {
                        check_nested(Layer::Raw)?;
                        let m = match_syntax!(
                            (for_meta phase_level spec ...)
                        )(spec.clone())?;
                        let p = m.phase_level.clone();
                        let p = parse_phase_from_syntax(p, &spec)?;

                        let new_spec = rebuild(
                            spec,
                            sexpr!((#(m.for_meta)
                                    #(m.phase_level)
                                    . #(self.parse_and_expand_provides_loop(m.spec,
                                        p + at_phase,
                                        protected,
                                        layer,
                                        require_and_provide,
                                        self_name.clone(),
                                        phase,
                                        context.clone())?)))
                        );
                        Ok(current.append(list!(new_spec)))
                    }
                    Some(fm) if fm.0 == "for-syntax".into() => {
                        check_nested(Layer::Raw)?;
                        let m = match_syntax!(
                            (for_syntax spec ...)
                        )(spec.clone(),)?;

                        let new_spec = rebuild(
                            spec,
                            sexpr!((#(m.for_syntax)
                                    . #(self.parse_and_expand_provides_loop(m.spec,
                                        Phase::Normal(1) + at_phase,
                                        protected,
                                        layer,
                                        require_and_provide,
                                        self_name.clone(),
                                        phase,
                                        context.clone())?)))
                        );
                        Ok(current.append(list!(new_spec)))
                    }
                    Some(fm) if fm.0 == "for-label".into() => {
                        check_nested(Layer::Raw)?;
                        let m = match_syntax!(
                            (for_label spec ...)
                        )(spec.clone())?;

                        let new_spec = rebuild(
                            spec,
                            sexpr!((#(m.for_label)
                                    . #(self.parse_and_expand_provides_loop(m.spec,
                                        Phase::Label,
                                        protected,
                                        layer,
                                        require_and_provide,
                                        self_name.clone(),
                                        phase,
                                        context.clone())?)))
                        );
                        Ok(current.append(list!(new_spec)))
                    }
                    Some(fm) if fm.0 == "protect".into() => {
                        check_nested(Layer::Phaseless)?;
                        if protected {
                            return Err(format!("invalid nesting {spec}"));
                        }
                        let m = match_syntax!(
                            (protect spec ...)
                        )(spec.clone())?;

                        let new_spec = rebuild(
                            spec,
                            sexpr!((#(m.protect)
                                    . #(self.parse_and_expand_provides_loop(m.spec,
                                        at_phase,
                                        true,
                                        layer,
                                        require_and_provide,
                                        self_name.clone(),
                                        phase,
                                        context.clone())?)))
                        );
                        Ok(current.append(list!(new_spec)))
                    }
                    Some(fm) if fm.0 == "rename".into() => {
                        check_nested(Layer::Phaseless)?;
                        let m = match_syntax!( (rename from:id to:id))(spec.clone(),)?;
                        let symbol: Syntax<Symbol> = m.to_id.try_into()?;
                        parse_identifier(&m.from_id.try_into()?, symbol.0, at_phase, require_and_provide);
                        Ok(current.append(list!(spec)))
                    }
                    Some(fm) if fm.0 == "struct".into() => {
                        check_nested(Layer::Phaseless)?;
                        let m = match_syntax!( (rename struct:id (field:id ...)))(spec.clone(),)?;
                        parse_struct(
                            m.struct_id.try_into()?,
                            to_id_list(m.field_id)?,
                            at_phase,
                            require_and_provide);
                        Ok(current.append(list!(spec)))
                    }
                    Some(fm) if fm.0 == "all-from".into() => {
                        check_nested(Layer::Phaseless)?;
                        let m = match_syntax!( (all_from mod_path))(spec.clone(),)?;
                        parse_all_from(m.mod_path, self_name.clone(), vec![], at_phase, require_and_provide)?;
                        Ok(current.append(list!(spec)))
                    }
                    Some(fm) if fm.0 == "all-from-except".into() => {
                        check_nested(Layer::Phaseless)?;
                        let m = match_syntax!((all_from mod_path id))(spec.clone())?;
                        parse_all_from(m.mod_path, self_name.clone(), to_id_list(m.id)?, at_phase, require_and_provide)?;
                        Ok(current.append(list!(spec)))
                    }
                    Some(fm) if fm.0 == "all-defined".into() => {
                        check_nested(Layer::Phaseless)?;
                        let _ = match_syntax!( (all_defined))(spec.clone(),)?;
                        parse_all_from_module( self_name.clone().ok_or(format!("no module path providied in (provide (all-defined)) {spec}"))?, &Some(spec.clone()),vec![],None, at_phase, require_and_provide)?;
                        Ok(current.append(list!(spec)))
                    }
                    Some(fm) if fm.0 == "all-defined-except".into() => {
                        check_nested(Layer::Phaseless)?;
                        let m = match_syntax!( (all_defined_except id ...))(spec.clone(),)?;
                        parse_all_from_module(self_name.clone().ok_or(format!("no module path providied in (provide (all-defined)) {spec}"))?,
                            &Some(spec.clone()),
                            to_id_list(m.id)?,
                            None, at_phase, require_and_provide)?;
                        Ok(current.append(list!(spec)))
                    }
                    Some(fm) if fm.0 == "prefix-all-defined".into() => {
                        check_nested(Layer::Phaseless)?;
                        let m = match_syntax!( (prefix_all_defined prefix:id))(spec.clone(),)?;
                        let symbol: Syntax<Symbol> = m.prefix_id.try_into()?;
                        parse_all_from_module(self_name.clone().ok_or(format!("no module path providied in (provide (prefix-all-defined)) {spec}"))?,
                            &Some(spec.clone()),
                            vec![],
                            Some(symbol.0),
                            at_phase,
                            require_and_provide)?;
                        Ok(current.append(list!(spec)))
                    }
                    Some(fm) if fm.0 == "prefix-all-defined-except".into() => {
                        check_nested(Layer::Phaseless)?;
                        let m = match_syntax!( (all_defined_except prefix:id id ...))(spec.clone(),)?;
                        let symbol: Syntax<Symbol> = m.prefix_id.try_into()?;
                        parse_all_from_module(self_name.clone().ok_or(format!("no module path providied in (provide (all-defined)) {spec}"))?,
                            &Some(spec.clone()),
                            to_id_list(m.id)?,
                            Some(symbol.0) , at_phase, require_and_provide)?;
                        Ok(current.append(list!(spec)))
                    }
                    Some(fm) if fm.0 == "expand".into() => {
                        // TODO: we do not have to clone spec as we are just verifiying and not
                        // using the result of match
                        match_syntax!( (expand (id . datum)))(spec.clone(),)?;
                        let m = match_syntax!( (expand form))(spec.clone(),)?;
                        let exp_spec = self.expand(m.form, context.clone())?;
                        if
                            !matches!(exp_spec, Ast::Syntax(ref s) if  matches!(&s.0, Ast::Pair(p) if p.0.clone().try_into().is_ok_and(|i: Syntax<Symbol>| &*i.0.0 == "begin") )) {
                            return Err(format!( "expansion of `provide` spec does not start `begin`: {spec}"));
                        }
                        let e_m  =match_syntax!( (begin spec ...))(exp_spec,)?;

                        self.parse_and_expand_provides_loop(e_m.spec, at_phase, protected, layer, require_and_provide, self_name.clone(), phase, context.clone())


                    }
                    _ => match spec.clone().try_into() {
                        Ok(spec_ident) => {
                            parse_identifier(
                                &spec_ident,
                                spec_ident.0.clone(),
                                at_phase,
                                require_and_provide,
                            );
                        Ok(current.append(list!(spec)))
                        }
                        Err(_) => Err(format!("bad provide spec: {spec}")),
                    },
                }
            },
            Ok(Ast::TheEmptyList),
        )?
    }
}

fn to_id_list(fields: Ast) -> Result<Vec<Syntax<Symbol>>, String> {
    fields
        .map_to_list_checked(|a| a.try_into())
        .map_err(|e| e.unwrap_or("not a list".to_string()))
}

fn parse_phase_from_syntax(phase: Ast, spec: &Ast) -> Result<Phase, String> {
    matches_to!(phase => Ast::Syntax)
        .and_then(|s| match s.0 {
            Ast::Number(e) => {
                Some(e).and_then(|n| (n.round() == n).then_some(Phase::Normal(n as isize)))
            }
            Ast::Boolean(false) => Some(Phase::Label),
            _ => None,
        })
        .ok_or(format!("bad phase: {spec}"))
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
                Symbol(format!("{prefix_symbol}{}", sym.0).into())
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
