use std::rc::Rc;

use crate::{
    ast::{Ast, Function, Pair},
    evaluator::Values,
};

impl Ast {
    pub fn primitive_plus(self) -> Result<Values, String> {
        todo!()
    }
    pub fn primitive_random(self) -> Result<Values, String> {
        todo!()
    }
    // TODO: these are all going to need access to the expander
    pub fn primitive_free_identifier(self) -> Result<Values, String> {
        todo!()
    }
    pub fn primitive_bound_identifier(self) -> Result<Values, String> {
        todo!()
    }
    pub fn primitive_datum_to_syntax(self) -> Result<Values, String> {
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
        // TODO: properties and location
        Ok(Values::Single(syntax_object.datum_to_syntax(
            scopes.scope_set(),
            scopes.shifted_multi_scope_set(),
            None,
            None,
        )))
    }
    pub fn primitive_syntax_to_datum(self) -> Result<Values, String> {
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
        Ok(Values::Single(e.syntax_to_datum()))
    }
    pub fn primitive_syntax_e(self) -> Result<Values, String> {
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
        Ok(Values::Single(e.0))
    }
    pub fn primitive_cons(self) -> Result<Values, String> {
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
        Ok(Values::Single(Self::Pair(Box::new(Pair(
            fst.clone(),
            snd.clone(),
        )))))
    }
    pub fn primitive_car(self) -> Result<Values, String> {
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
        Ok(Values::Single(fst))
    }
    pub fn primitive_cdr(self) -> Result<Values, String> {
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
        Ok(Values::Single(snd))
    }

    pub const fn primitive_list(self) -> Result<Values, String> {
        Ok(Values::Single(self))
    }
    pub fn primitive_map(self) -> Result<Values, String> {
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
        l.map(|a| f.apply_single(Self::Pair(Box::new(Pair(a, Self::TheEmptyList)))))
            .map(Values::Single)
    }
    pub fn primitive_values(self) -> Result<Values, String> {
        match self {
            Self::Pair(p) if p.1 == Self::TheEmptyList => Ok(Values::Single(p.0)),
            _ => self.to_list_checked().map(Values::Many),
        }
    }
    pub fn primitive_null(self) -> Result<Values, String> {
        match self {
            Self::Pair(p) if *p == Pair(Self::TheEmptyList, Self::TheEmptyList) => {
                Ok(Values::Single(Self::Boolean(true)))
            }
            _ => Ok(Values::Single(Self::Boolean(false))),
        }
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
    adder(
        "null?".into(),
        Ast::Function(Function::Primitive(Ast::primitive_null)),
    );
    adder(
        "values".into(),
        Ast::Function(Function::Primitive(Ast::primitive_values)),
    );
    adder(
        "bound-identifier=?".into(),
        Ast::Function(Function::Primitive(Ast::primitive_bound_identifier)),
    );
    adder(
        "free-identifier=?".into(),
        Ast::Function(Function::Primitive(Ast::primitive_free_identifier)),
    );
    adder(
        "random".into(),
        Ast::Function(Function::Primitive(Ast::primitive_random)),
    );
    adder(
        "+".into(),
        Ast::Function(Function::Primitive(Ast::primitive_plus)),
    )
}
