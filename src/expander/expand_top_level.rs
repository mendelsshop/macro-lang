use matcher::match_syntax;

use crate::{
    ast::{scope::AdjustScope, Ast},
    UniqueNumberManager,
};

use super::{
    expand_context::{Context, ExpandContext},
    expand_requires::parse_and_perform_requires,
    require_and_provide::RequiresAndProvides,
    Expander,
};

impl Expander {
    pub fn core_form_define_values(&mut self, s: Ast, _ctx: ExpandContext) -> Result<Ast, String> {
        Err(format!("not allowed in an expression postion: {s} "))
    }
    pub fn core_form_define_syntaxes(
        &mut self,
        s: Ast,
        _ctx: ExpandContext,
    ) -> Result<Ast, String> {
        Err(format!("not allowed in an expression postion: {s} "))
    }
    pub fn core_form_begin_for_syntax(
        &mut self,
        s: Ast,
        _ctx: ExpandContext,
    ) -> Result<Ast, String> {
        Err(format!("not yet supported here: {s} "))
    }
    pub fn core_form_require(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        (ctx.context != Context::TopLevel)
            .then_some(())
            .ok_or(format!("allowed only in module or top level {s}"))
            // TODO: .and_then(|_| match_syntax!( (#%require req ...))(s.clone()))
            .and_then(|_| match_syntax!( (require req ...))(s.clone()))
            .map(|m| m.req)
            .and_then(|reqs| {
                let sc = UniqueNumberManager::new_scope();
                reqs.map(|req| Ok(req.add_scope(sc.clone())))
            })
            .and_then(|reqs| {
                parse_and_perform_requires(
                    reqs,
                    None,
                    &ctx.namespace,
                    ctx.phase,
                    &RequiresAndProvides::default(),
                    false,
                )
            })
            .map(|_| s)
    }
    pub fn core_form_define_provide(&mut self, s: Ast, _ctx: ExpandContext) -> Result<Ast, String> {
        Err(format!("not allowed outside of a module body: {s} "))
    }
}
