use crate::{ast::Ast, expander::{expand_context::ExpandContext, Expander}};

impl Expander {

    pub fn core_form_module(&mut self, s: Ast, ctx: ExpandContext)-> Result<Ast, String> {
        // partially expand
        // does this mean to expand until find a define/define-syntax/require/provide
        todo!()
    }
}
