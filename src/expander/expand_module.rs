use std::collections::BTreeSet;

use itertools::Either;

use crate::{
    ast::{scope::Scope, syntax::Syntax, Ast, Symbol},
    expander::{
        expand_requires::perform_initial_require,
        module_path::{build_module_name, ModulePath, SubModulePathElement},
        r#match::match_syntax,
        require_and_provide::RequiresAndProvides,
    },
    sexpr, UniqueNumberManager,
};

use super::{
    expand_context::{Context, ExpandContext},
    module_path::ResolvedModulePath,
    phase::Phase,
    Expander,
};

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
        let m = match_syntax(
            syntax,
            sexpr!((module "id:module-name" "initial-require" body "...")),
        )?;
        let initial_require = m("initial-require".into())
            .ok_or("internal error")?
            .syntax_to_datum();
        let for_submodule = enclosing_self.is_some();
        let keep_enclosing_scope_at_phase_or_initial_require = (keep_enclosing_scope_at_phase
            != Phase::Label)
            .then_some(Either::Left(keep_enclosing_scope_at_phase))
            .or_else(|| {
                TryInto::<ModulePath>::try_into(initial_require)
                    .ok()
                    .map(Either::Right)
            })
            .ok_or(format!(
                "no a module path: {}",
                m("initial-require".into()).ok_or("internal error")?
            ))?;
        let outside_scope = UniqueNumberManager::new_scope();
        let inside_scope = UniqueNumberManager::new_scope();
        let new_module_scopes = {
            let mut scopes = BTreeSet::from([inside_scope.clone(), outside_scope.clone()]);
            if keep_enclosing_scope_at_phase != Phase::Label {
                scopes.extend(context.module_scopes.clone());
            }
            scopes
        };
        let value = m("id:module-name".into()).ok_or("internal error")?;
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
            inside_scope,
            context,
            keep_enclosing_scope_at_phase != Phase::Label,
        );
        let bodies = m("body".into())
            .ok_or("internal error")?
            .map(|b| Ok(apply_module_scopes(b)))?;
        let require_and_provides = RequiresAndProvides::default();
        match keep_enclosing_scope_at_phase_or_initial_require {
            Either::Left(phase) => {
                let module = enclosing_self.unwrap_or_else(|| unreachable!());
                require_and_provides.add_required_module(module.clone(), phase);
                module_namespace.namespace_module_visit(&module, keep_enclosing_scope_at_phase)?;
            }
            Either::Right(initial_require) => perform_initial_require(
                initial_require,
                Some(self_path),
                &m("initial-require".into()).ok_or("internal error")?,
                module_namespace,
                require_and_provides,
            )?,
        }
        let phase = Phase::Normal(0);
        todo!()
    }
}

fn make_apply_module_scopes(
    outside_scope: Scope,
    inside_scope: Scope,
    context: ExpandContext,
    keep_enclosing_scope_at_phase: bool,
) -> impl Fn(Ast) -> Ast {
    |syntax| todo!()
}
