use crate::ast::Ast;

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
        todo!()
    }
}
