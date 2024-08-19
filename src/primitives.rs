use std::rc::Rc;

use crate::ast::{Ast, Function, Pair};

impl Ast {
    pub fn primitive_datum_to_syntax(self) -> Result<Self, String> {
        let arity = self.size();
        let Self::Pair(e) = self else {
            Err(format!("arity error: expected 2 argument, got {arity}",))?
        };
        let Pair(scopes, Self::Pair(syntax_object)) = *e else {
            Err(format!("arity error: expected 2 argument, got {arity}"))?
        };
        let Pair(syntax_object, Self::TheEmptyList) = *syntax_object else {
            Err(format!("arity error: expected 1 argument, got {arity}"))?
        };
        Ok(syntax_object.datum_to_syntax(scopes.scope_set()))
    }
    pub fn primitive_syntax_to_datum(self) -> Result<Self, String> {
        let Self::Pair(e) = self else {
            Err(format!(
                "arity error: expected 1 argument, got {}",
                self.size()
            ))?
        };
        let Pair(e, Self::TheEmptyList) = *e else {
            Err(format!(
                "arity error: expected 1 argument, got {}",
                e.size()
            ))?
        };
        Ok(e.syntax_to_datum())
    }
    pub fn primitive_syntax_e(self) -> Result<Self, String> {
        let Self::Pair(e) = self else {
            Err(format!(
                "arity error: expected 1 argument, got {}, syntax e",
                self.size()
            ))?
        };
        let Pair(Self::Syntax(e), Self::TheEmptyList) = *e else {
            Err(format!(
                "arity error: expected 1 argument, got {} or got non syntax object, syntax e",
                e.size()
            ))?
        };
        Ok(e.0)
    }
    pub fn primitive_cons(self) -> Result<Self, String> {
        let Self::Pair(e) = self else {
            Err(format!(
                "arity error: expected 2 argument, got {}",
                self.size()
            ))?
        };
        let Pair(ref fst, Self::Pair(ref last)) = *e else {
            Err(format!(
                "arity error: expected 2 argument, got {}",
                e.size()
            ))?
        };
        let Pair(ref snd, Self::TheEmptyList) = **last else {
            Err(format!(
                "arity error: expected 2 argument, got {}",
                e.size()
            ))?
        };
        Ok(Self::Pair(Box::new(Pair(fst.clone(), snd.clone()))))
    }
    pub fn primitive_car(self) -> Result<Self, String> {
        let Self::Pair(e) = self else {
            Err(format!(
                "arity error: expected 1 argument, got {}, car",
                self.size()
            ))?
        };

        let Pair(Self::Pair(e), Self::TheEmptyList) = *e else {
            Err(format!(
                "arity error: expected 1 argument, got {} or given non pair, car",
                e.size()
            ))?
        };
        let Pair(fst, _) = *e;
        Ok(fst)
    }
    pub fn primitive_cdr(self) -> Result<Self, String> {
        let Self::Pair(e) = self else {
            Err(format!(
                "arity error: expected 1 argument, got {}, cdr",
                self.size()
            ))?
        };
        let Pair(Self::Pair(e), Self::TheEmptyList) = *e else {
            Err(format!(
                "arity error: expected 1 argument, got {} or given non pair, cdr",
                e.size()
            ))?
        };
        let Pair(_, snd) = *e;
        Ok(snd)
    }

    pub fn primitive_list(self) -> Result<Self, String> {
        Ok(self)
    }
    pub fn primitive_map(self) -> Result<Self, String> {
        let Self::Pair(e) = self else {
            Err(format!(
                "arity error: expected 2 argument, got {}, map",
                self.size()
            ))?
        };

        let Pair(Self::Function(ref f), Self::Pair(ref last)) = *e else {
            Err(format!(
                "arity error: expected 2 argument, got {}, or given non function {}, map",
                e.size(),
                e.0
            ))?
        };
        let Pair(ref l, Self::TheEmptyList) = **last else {
            Err(format!(
                "arity error: expected 2 argument, got {}",
                e.size()
            ))?
        };
        l.map(|a| f.apply(Self::Pair(Box::new(Pair(a, Self::TheEmptyList)))))
    }
}

pub fn new_primitive_env(mut adder: impl FnMut(Rc<str>, Ast)) {
    // add code here
    adder(
        "datum->syntax".into(),
        Ast::Function(Function::Primitive(Ast::primitive_datum_to_syntax)),
    );
    adder(
        "syntax->datum".into(),
        Ast::Function(Function::Primitive(Ast::primitive_syntax_to_datum)),
    );
    adder(
        "syntax-e".into(),
        Ast::Function(Function::Primitive(Ast::primitive_syntax_e)),
    );
    adder(
        "cons".into(),
        Ast::Function(Function::Primitive(Ast::primitive_cons)),
    );
    adder(
        "car".into(),
        Ast::Function(Function::Primitive(Ast::primitive_car)),
    );
    adder(
        "cdr".into(),
        Ast::Function(Function::Primitive(Ast::primitive_cdr)),
    );
    adder(
        "list".into(),
        Ast::Function(Function::Primitive(Ast::primitive_list)),
    );
    adder(
        "map".into(),
        Ast::Function(Function::Primitive(Ast::primitive_map)),
    );
}
