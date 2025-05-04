use std::{collections::BTreeSet, rc::Rc};

use itertools::Either;
use matcher::match_syntax_as;

use crate::{
    ast::{
        scope::{AdjustScope, Scope},
        syntax::Syntax,
        Ast, Symbol,
    },
    expander::{
        expand::rebuild,
        expand_requires::perform_initial_require,
        module_path::{build_module_name, ModulePath, SubModulePathElement},
        require_and_provide::RequiresAndProvides,
    },
    sexpr, UniqueNumberManager,
};

use super::{
    expand_context::{Context, ExpandContext},
    module_path::ResolvedModulePath,
    namespace::NameSpace,
    phase::Phase,
    Expander,
};
// TODO: match_syntax!( (#%module_begin body ...))
match_syntax_as!(ModuleBeginMatcher as (module_begin body ...));
match_syntax_as!(ModuleMatcher as (module module_name:id initial_require body ...));
impl Expander {
    pub fn core_form_module(&mut self, syntax: Ast, context: ExpandContext) -> Result<Ast, String> {
        if context.context != Context::TopLevel {
            Err(format!("allowed only at the top level: {syntax}"))
        } else {
            self.expand_module(syntax, context, None, Phase::Label)
        }
    }
    pub fn core_form_module_star(
        &mut self,
        syntax: Ast,
        _context: ExpandContext,
    ) -> Result<Ast, String> {
        Err(format!("illegal use (not in module top level): {syntax}"))
    }
    pub fn core_form_module_begin(
        &mut self,
        syntax: Ast,
        context: ExpandContext,
    ) -> Result<Ast, String> {
        if context.context != Context::ModuleBegin {
            Err(format!("not in a module-defintion context: {syntax}"))
        } else {
            context
                .module_begin_k
                .ok_or("no module begin k found".to_string())
                .and_then(|k| {
                    k(
                        self,
                        syntax,
                        ExpandContext {
                            module_begin_k: None,
                            ..context
                        },
                    )
                })
        }
    }
    // keep_enclosing_scope_at_phase: defaults to labaled phase
    pub fn expand_module(
        &mut self,
        syntax: Ast,
        context: ExpandContext,
        enclosing_self: Option<ResolvedModulePath>,
        keep_enclosing_scope_at_phase: Phase,
    ) -> Result<Ast, String> {
        let m = ModuleMatcher::matches(syntax.clone())?;
        let initial_require = m.initial_require.clone().syntax_to_datum();
        let for_submodule = enclosing_self.is_some();
        let keep_enclosing_scope_at_phase_or_initial_require = (keep_enclosing_scope_at_phase
            != Phase::Label)
            .then_some(Either::Left(keep_enclosing_scope_at_phase))
            .or_else(|| {
                TryInto::<ModulePath>::try_into(initial_require)
                    .ok()
                    .map(Either::Right)
            })
            .ok_or(format!("no a module path: {}", m.initial_require))?;
        let outside_scope = UniqueNumberManager::new_scope();
        let inside_scope = UniqueNumberManager::new_scope();
        let new_module_scopes = {
            let mut scopes = BTreeSet::from([inside_scope.clone(), outside_scope.clone()]);
            if keep_enclosing_scope_at_phase != Phase::Label {
                scopes.extend(context.module_scopes.clone());
            }
            scopes
        };
        let value = m.module_name_id.clone();
        let original = format!("{value}");
        let self_path = build_module_name(
            &SubModulePathElement::from(Syntax::<Symbol>::try_from(value)?.0),
            enclosing_self.clone(),
            &original,
        )?;
        let module_namespace = context
            .namespace
            .make_module_namespace(self_path.clone(), for_submodule);
        let apply_module_scopes = make_apply_module_scopes(
            outside_scope,
            inside_scope.clone(),
            context.clone(),
            keep_enclosing_scope_at_phase != Phase::Label,
        );
        let bodies = m.body.map(|b| Ok(apply_module_scopes(b)))?;
        let require_and_provides = RequiresAndProvides::default();
        match keep_enclosing_scope_at_phase_or_initial_require {
            Either::Left(phase) => {
                let module = enclosing_self.as_ref().unwrap_or_else(|| unreachable!());
                require_and_provides.add_required_module(module.clone(), phase);
                module_namespace.namespace_module_visit(&module, keep_enclosing_scope_at_phase)?;
            }
            Either::Right(initial_require) => perform_initial_require(
                initial_require,
                Some(self_path.clone()),
                &m.initial_require,
                module_namespace.clone(),
                &require_and_provides.clone(),
            )?,
        }
        let phase = Phase::Normal(0);
        let module_begin_k = {
            // cloning so can be used after fn
            let require_and_provides = require_and_provides.clone();
            let inside_scope = inside_scope.clone();
            let module_namespace = module_namespace.clone();
            let new_module_scopes = new_module_scopes.clone();
            let syntax = syntax.clone();
            let self_path = self_path.clone();
            let enclosing_self = enclosing_self.clone();
            let m = m.clone();
            Rc::new(
                move |this: &mut Expander, module_begin: Ast, context: ExpandContext| {
                    // cloning so not fully moved by fn
                    let require_and_provides = require_and_provides.clone();
                    let inside_scope = inside_scope.clone();
                    let module_namespace = module_namespace.clone();
                    let new_module_scopes = new_module_scopes.clone();
                    let syntax = syntax.clone();
                    let self_path = self_path.clone();
                    let m = m.clone();
                    let enclosing_self = enclosing_self.clone();
                    let module_begin_m = ModuleBeginMatcher::matches(module_begin.clone())?;
                    require_and_provides.reset_provides();
                    let bodies = module_begin_m
                        .body
                        .map(|b| Ok(b.add_scope(inside_scope.clone())))?;
                    let expression_expanded_bodys = pass_1_and_2_loop(
                        bodies,
                        phase,
                        context.clone(),
                        module_namespace.clone(),
                        new_module_scopes.clone(),
                        syntax.clone(),
                        self_path.clone(),
                        require_and_provides.clone(),
                    )?;
                    let fully_expanded_bodys_except_post_submodules = resolve_provides(
                        expression_expanded_bodys,
                        syntax.clone(),
                        require_and_provides.clone(),
                        phase,
                        self_path.clone(),
                        context.clone(),
                    )?;
                    let submodule_context = ExpandContext {
                        namespace: module_namespace.clone(),
                        module_scopes: new_module_scopes,
                        ..context
                    };
                    let declare_enclosing_module = {
                        let fully_expanded_bodys_except_post_submodules =
                            fully_expanded_bodys_except_post_submodules.clone();
                        let self_path = self_path.clone();
                        let module_begin_m = module_begin_m.clone();
                        move || {
                            declare_module_for_expansion(
                                fully_expanded_bodys_except_post_submodules.clone(),
                                m.clone(),
                                module_begin_m.clone(),
                                require_and_provides.clone(),
                                module_namespace.clone(),
                                self_path.clone(),
                                enclosing_self.clone(),
                            )
                        }
                    };
                    let fully_expanded_bodys = expand_post_submodules(
                        fully_expanded_bodys_except_post_submodules,
                        declare_enclosing_module,
                        syntax,
                        self_path,
                        submodule_context,
                    )?;
                    Ok(rebuild(
                        module_begin,
                        sexpr!((#(module_begin_m.module_begin) . #(fully_expanded_bodys))),
                    ))
                },
            )
        };
        let module_begin = ensure_module_begin(
            bodies,
            inside_scope,
            new_module_scopes.clone(),
            context.clone(),
            phase,
            syntax.clone(),
        )?;
        let expanded_module_body = self.expand(
            module_begin,
            ExpandContext {
                context: Context::ModuleBegin,
                namespace: module_namespace,
                module_scopes: new_module_scopes,
                module_begin_k: Some(module_begin_k),
                use_site_scopes: Some(Rc::default()),
                ..context
            },
        )?;

        let rator =
            sexpr!((#(m.module) #( m.module_name_id)#( m.initial_require) #(expanded_module_body)));
        Ok(require_and_provides
            .attach_require_provide_properties(rebuild(syntax, rator), self_path))
    }
}

fn expand_post_submodules(
    fully_expanded_bodys_except_post_submodules: Ast,
    declare_enclosing_module: impl FnMut() -> Result<Ast, String>,
    syntax: Ast,
    self_path: ResolvedModulePath,
    submodule_context: ExpandContext,
) -> Result<Ast, String> {
    todo!()
}

fn declare_module_for_expansion(
    fully_expanded_bodys_except_post_submodules: Ast,
    m: ModuleMatcher,
    module_begin_m: ModuleBeginMatcher,
    require_and_provides: RequiresAndProvides,
    module_namespace: NameSpace,
    self_path: ResolvedModulePath,
    enclosing_self: Option<ResolvedModulePath>,
) -> Result<Ast, String> {
    todo!()
}

fn resolve_provides(
    expression_expanded_bodys: Ast,
    syntax: Ast,
    require_and_provides: RequiresAndProvides,
    phase: Phase,
    self_path: ResolvedModulePath,
    context: ExpandContext,
) -> Result<Ast, String> {
    todo!()
}

fn pass_1_and_2_loop(
    bodies: Ast,
    phase: Phase,
    context: ExpandContext,
    module_namespace: NameSpace,
    new_module_scopes: BTreeSet<Scope>,
    syntax: Ast,
    self_path: ResolvedModulePath,
    require_and_provides_clone: RequiresAndProvides,
) -> Result<Ast, String> {
    todo!()
}

fn ensure_module_begin(
    bodies: Ast,
    inside_scope: Scope,
    new_module_scopes: BTreeSet<Scope>,
    context: ExpandContext,
    phase: Phase,
    syntax: Ast,
) -> Result<Ast, String> {
    todo!()
}

fn make_apply_module_scopes(
    outside_scope: Scope,
    inside_scope: Scope,
    context: ExpandContext,
    keep_enclosing_scope_at_phase: bool,
) -> impl Fn(Ast) -> Ast {
    |syntax| todo!()
}
