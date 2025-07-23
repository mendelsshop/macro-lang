use std::collections::VecDeque;

use crate::{
    ast::Ast,
    expander::{expand_context::ExpandContext, Expander},
};

impl Expander {
    pub fn core_form_module(&mut self, s: Ast, ctx: ExpandContext) -> Result<Ast, String> {
        // partially expand
        // does this mean to expand until find a define/define-syntax/require/provide
        let module_m = matcher::match_syntax!((module name_name language_name body...))(s)?;
        todo!()
    }

    pub fn expand_module_partially(
        &mut self,
        mut s: VecDeque<Ast>,
        ctx: ExpandContext,
        result: &mut Vec<Ast>,
    ) -> Result<(), String> {
        match s.pop_front() {
            Some(expr) => {
                let expr = self.expand(expr, ctx.clone())?;
                if let Ok(sym) = Self::core_form_symbol(expr.clone()) {
                    match &*sym {
                        "define-values" => {}
                        "begin-for-syntax" => {}
                        "begin" => {}
                        "define-syntaxes" => {}
                        "provide" => {}
                        "require" => {}
                        _ => {
                            result.push(expr);
                        }
                    }
                } else {
                    result.push(expr);
                }
                self.expand_module_partially(s, ctx, result)
            }
            None => Ok(()),
        }
    }
}
