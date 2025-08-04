use std::{
    collections::{BTreeSet, HashMap},
    iter::{self},
    rc::Rc,
};

use fallible_iterator::{self, convert, FallibleIterator};
use itertools::{Either, Itertools};
use matcher::{match_syntax, match_syntax_as};

#[derive(Clone)]
struct Pass1And2Loop {
    context: ExpandContext,
    module_namespace: NameSpace,
    new_module_scopes: BTreeSet<Scope>,
    inside_scope: Scope,
    syntax: Ast,
    self_path: ResolvedModulePath,
    require_and_provides_clone: RequiresAndProvides,
}
use crate::{
    ast::{
        scope::{AdjustScope, Scope},
        syntax::Syntax,
        Ast, Symbol,
    },
    expander::{
        binding::{Binding, ModuleBinding},
        expand::rebuild,
        expand_requires::{parse_and_perform_requires, perform_initial_require},
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
#[derive(Clone)]
struct ResolveProvidesStruct {
    syntax: Ast,
    require_and_provides: RequiresAndProvides,
    self_path: ResolvedModulePath,
    context: ExpandContext,
}

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
        let apply_module_scopes = self.make_apply_module_scopes(
            outside_scope,
            inside_scope.clone(),
            context.clone(),
            keep_enclosing_scope_at_phase != Phase::Label,
        );
        let bodies = m.body.map(|b| Ok(apply_module_scopes(b)))?;
        drop(apply_module_scopes);
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
                    let bodies = {
                        let inside_scope = inside_scope.clone();
                        module_begin_m
                            .body
                            .clone()
                            .to_list()
                            .into_iter()
                            .map(move |b| (b.add_scope(inside_scope.clone())))
                    };
                    let expression_expanded_bodys = this.pass_1_and_2_loop(
                        bodies,
                        phase,
                        Pass1And2Loop {
                            context: context.clone(),
                            module_namespace: module_namespace.clone(),
                            new_module_scopes: new_module_scopes.clone(),
                            inside_scope: inside_scope,
                            syntax: syntax.clone(),
                            self_path: self_path.clone(),
                            require_and_provides_clone: require_and_provides.clone(),
                        },
                    )?;
                    let fully_expanded_bodys_except_post_submodules = this.resolve_provides(
                        expression_expanded_bodys,
                        phase,
                        ResolveProvidesStruct {
                            syntax: syntax.clone(),
                            require_and_provides: require_and_provides.clone(),
                            self_path: self_path.clone(),
                            context: context.clone(),
                        },
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
                    let fully_expanded_bodys = this.expand_post_submodules(
                        fully_expanded_bodys_except_post_submodules,
                        declare_enclosing_module,
                        syntax,
                        phase,
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
    fn make_apply_module_scopes(
        &self,
        outside_scope: Scope,
        inside_scope: Scope,
        context: ExpandContext,
        keep_enclosing_scope_at_phase: bool,
    ) -> impl Fn(Ast) -> Ast + use<'_> {
        move |syntax| {
            let s_without_enclosing = if keep_enclosing_scope_at_phase {
                syntax
            } else {
                self.remove_use_site_scopes(
                    syntax.remove_scopes(context.module_scopes.clone()),
                    &context,
                )
            };

            s_without_enclosing
                .add_scope(outside_scope.clone())
                .add_scope(inside_scope.clone())
        }
    }
    fn pass_1_and_2_loop<'a>(
        &mut self,
        bodies: impl Iterator<Item = Ast> + Clone + 'a,
        phase: Phase,
        info: Pass1And2Loop,
        // -> impl Iterator<Item = Result<Ast, String>> {
        // wish i could just do this but require nested impl traits or the like, for contiunation
        // maybe
    ) -> Result<Vec<Ast>, String> {
        let info_clone = info.clone();
        let partial_body_ctx = ExpandContext {
            context: Context::Module,
            phase,
            namespace: info.module_namespace.clone(),
            only_immediate: true,
            post_expansion_scope: Some(info.inside_scope),
            module_scopes: info.new_module_scopes,
            ..info.context
        };
        let partially_expanded_bodies = self.partially_expand_bodys(
            bodies,
            info.syntax,
            phase,
            partial_body_ctx.clone(),
            info.module_namespace,
            info.self_path,
            info.require_and_provides_clone,
            info_clone,
        )?;
        let body_ctx = ExpandContext {
            only_immediate: false,
            post_expansion_scope: None,
            ..partial_body_ctx
        };
        self.finish_expanding_body_expressions(partially_expanded_bodies, phase, body_ctx)
    }
    // use process_results like iterator but take it in from origianl function so now lifetime
    // issues, and in order not keep on changing the underlying iterator, backwards implement a
    // trait made for process results, i.e. if Map struct (how a map is repr in type system)
    // contains an iterator that implement process_results iterator then implement for Map struct
    // too, if we want to go crazy have a marker trait, called HasIterator for iterator adapater
    // structs
    fn partially_expand_bodys(
        &mut self,
        bodies: impl Iterator<Item = Ast>,
        s: Ast,
        phase: Phase,
        partial_body_ctx: ExpandContext,
        module_namespace: NameSpace,
        self_path: ResolvedModulePath,
        require_and_provides_clone: RequiresAndProvides,
        pass_1_and_2_loop_info: Pass1And2Loop,
    ) -> Result<Vec<Ast>, String> {
        let mut defined_symbols = HashMap::new();
        bodies
            // TODO: maybe make flat_map_ok = map + flatten_ok
            .map(move |body| {
                let expanded_body = self.expand(body, partial_body_ctx.clone())?;
                if let Ok(sym) = Self::core_form_symbol(expanded_body.clone(), phase) {
                    match &*sym.0 {
                        "begin" => {
                            let begin_m = match_syntax!((begin e ...))(expanded_body)?;
                            self.partially_expand_bodys(
                                begin_m.e.to_list_checked()?.into_iter(),
                                s.clone(),
                                phase,
                                partial_body_ctx.clone(),
                                module_namespace.clone(),
                                self_path.clone(),
                                require_and_provides_clone.clone(),
                                pass_1_and_2_loop_info.clone(),
                            )
                        }
                        "begin-for-syntax" => {
                            let begin_for_syntax_m =
                                match_syntax!((begin_for_syntax e ...))(expanded_body)?;
                            let nested_bodies = self.pass_1_and_2_loop(
                                begin_for_syntax_m.e.to_list_checked()?.into_iter(),
                                phase,
                                pass_1_and_2_loop_info.clone(),
                            )?;
                            self.eval_nested_bodies(
                                nested_bodies.clone(),
                                phase + Phase::Normal(1),
                                module_namespace.clone(),
                                self_path.clone(),
                            )?;
                            Ok(vec![rebuild(s.clone(), sexpr!((#(begin_for_syntax_m.begin_for_syntax) . #(nested_bodies.into_iter().fold(Ast::TheEmptyList, |_, _| todo!())))))])
                        }
                        "define-values" => Ok({
                            let define_values_m = match_syntax!((define_values (id ...) rhs))(expanded_body.clone())?;
                            let ids = self.remove_use_site_scopes(define_values_m.id, &partial_body_ctx);
                            check_ids_unbound(ids.clone(), phase, require_and_provides_clone.clone())?;
                            let syms = select_defined_symbols_and_bindings(ids, &mut defined_symbols, self_path.clone(), phase, require_and_provides_clone.clone())?;
                            vec![expanded_body]

                        }),
                        "define-syntaxes" => Ok({
                            let define_syntaxes_m = match_syntax!((define_syntaxes (id ...) rhs))(expanded_body.clone())?;
                            let ids = self.remove_use_site_scopes(define_syntaxes_m.id, &partial_body_ctx);
                             check_ids_unbound(ids.clone(),phase, require_and_provides_clone.clone())?;
                            let syms = select_defined_symbols_and_bindings(ids.clone(), &mut defined_symbols, self_path.clone(), phase, require_and_provides_clone.clone())?;
                            let (values, rhs) = self.expand_and_eval_for_syntaxes_binding(define_syntaxes_m.rhs, syms.len(), partial_body_ctx.clone())?;
                            syms.into_iter().zip(values).for_each(|(sym, val)| {
                                // TODO: is there something wrong expand_and_eval_for_syntaxes_binding thats making incompatible types or something else
                                // module_namespace.namespace_set_transformer(phase, sym, val);
                                todo!()
                            });
                            vec![rebuild(expanded_body, sexpr!((#(define_syntaxes_m.define_syntaxes) #(ids) #(rhs))))]
                        }),
                        "#%require" => Ok({
                            let ready_body = self.remove_use_site_scopes(expanded_body.clone(), &partial_body_ctx);
                            let require_m = match_syntax!((require req ...))(ready_body)?;
                            parse_and_perform_requires(require_m.req, Some(self_path.clone()), &module_namespace, phase, &require_and_provides_clone, false)?;
                            vec![expanded_body]
                        }),
                        "#%provide" => Ok(vec![expanded_body]),
                        "module" => self.expand_submodule(expanded_body, self_path.clone(), partial_body_ctx.clone()),
                        "module*" => Ok(vec![expanded_body]),
                        _ => Ok(vec![expanded_body]),
                    }
                } else {
                    Ok(vec![expanded_body])
                }
            })
            .flatten_ok()
            .collect()
    }

    fn expand_submodule(
        &self,
        expanded_body: Ast,
        self_path: ResolvedModulePath,
        partial_body_ctx: ExpandContext,
    ) -> Result<Vec<Ast>, String> {
        todo!()
    }

    fn eval_nested_bodies(
        &self,
        nested_bodies: Vec<Ast>,
        normal: Phase,
        module_namespace: NameSpace,
        self_path: ResolvedModulePath,
    ) -> Result<(), String> {
        todo!()
    }
    fn finish_expanding_body_expressions(
        &mut self,
        partially_expanded_bodys: Vec<Ast>,
        phase: Phase,
        body_ctx: ExpandContext,
    ) -> Result<Vec<Ast>, String> {
        partially_expanded_bodys
            .into_iter()
            .map(move |body| {
                if let Ok(sym) = Self::core_form_symbol(body.clone(), phase) {
                    match &*sym.0 {
                        "define-values" => {
                            let define_values_m =
                                match_syntax!((define_values (id ...) rhs))(body.clone())?;
                            let expanded_rhs = self.expand(define_values_m.rhs, body_ctx.clone())?;
                            Ok(vec![rebuild(body, sexpr!((#(define_values_m.define_values) #(define_values_m.id) #(expanded_rhs))))])
                        }
                        "define-syntaxes" | "#%require" | "#%provide" | "begin-for-syntax"
                        | "module" | "module*" => Ok(vec![body]),
                        _ => Ok(vec![self.expand(body, body_ctx.clone())?]),
                    }
                } else {
                    // TODO: only if because not core symbol, but if its cause resolve failed than
                    // just propagate the error
                    Ok(vec![self.expand(body, body_ctx.clone())?])
                }
            })
            .flatten_ok()
            .collect()
    }
    fn resolve_provides(
        &mut self,
        expression_expanded_bodys: Vec<Ast>,
        phase: Phase,
        info: ResolveProvidesStruct,
    ) -> Result<Vec<Ast>, String> {
        expression_expanded_bodys
            .into_iter()
            .map(move |body| {
                if let Ok(sym) = Self::core_form_symbol(body.clone(), phase) {
                    match &*sym.0 {
                        "#%provide" => {
                            let provide_m = match_syntax!((provide spec))(body.clone())?;
                            let specs = self.parse_and_expand_provides(provide_m.spec, &info.require_and_provides, Some(info.self_path.clone()), phase, info.context.clone())?;
                            // TODO: @ before specs: 
                            // (rebuild (car bodys)
                            // `(,(m '#%provide) ,@specs))
                            Ok(vec![rebuild(body, sexpr!((#(provide_m.provide) #(specs) )))])
                        },
                        "begin-for-syntax" => {
                            let begin_for_syntax_m =
                                match_syntax!((begin_for_syntax e ...))(body.clone())?;
                            let nested_bodies = self.resolve_provides(
                            begin_for_syntax_m.e.to_list(),
                                phase + Phase::Normal(1),
                                info.clone()
                            )?;
                            Ok(vec![rebuild(body, sexpr!((#(begin_for_syntax_m.begin_for_syntax) . #(nested_bodies.into_iter().fold(Ast::TheEmptyList, |_, _| todo!())))))])
                        },
                        _ => Ok(vec![body]),
                    }
                } else {
                    Ok(vec![body])
                }
            })
            .flatten_ok()
            .collect()
    }
    fn expand_post_submodules(
        &mut self,
        fully_expanded_bodys_except_post_submodules: Vec<Ast>,
        declare_enclosing_module: impl FnMut() -> Result<Ast, String>,
        syntax: Ast,
        phase: Phase,
        self_path: ResolvedModulePath,
        submodule_context: ExpandContext,
    ) -> Result<Ast, String> {
        fully_expanded_bodys_except_post_submodules
            .into_iter()
            .map(move |body| {
                if let Ok(sym) = Self::core_form_symbol(body.clone(), phase) {
                    match &*sym.0 {
                        "module*" => todo!(),
                        "begin-for-syntax" => todo!(),
                        _ => Ok(vec![body]),
                    }
                } else {
                    Ok(vec![body])
                }
            })
            .flatten_ok()
            .try_fold(Ast::TheEmptyList, |_, _: Result<Ast, String>| todo!())
    }
}

fn select_defined_symbols_and_bindings(
    ids: Ast,
    defined_symbols: &mut HashMap<String, Syntax<Symbol>>,
    self_path: ResolvedModulePath,
    phase: Phase,
    require_and_provides_clone: RequiresAndProvides,
) -> Result<Vec<Symbol>, String> {
    ids.map_to_list_checked(|id| {
        let id: Syntax<Symbol> = id.try_into()?;
        let symbol = id.0 .0.to_string();
        let local_symbol = iter::once(symbol.clone())
            .chain((0..).map(move |i| format!("{}{i}", &symbol)))
            .find(|id| !defined_symbols.contains_key(id))
            .unwrap();
        defined_symbols.insert(local_symbol.clone(), id.clone());
        let local_sym: Symbol = Symbol(local_symbol.clone().into());
        let module_binding = ModuleBinding {
            from_module: self_path.clone(),
            from_phase: phase,
            from_symbol: local_sym.clone(),
            nominal_from_module: self_path.clone(),
            nominal_from_phase: phase,
            nominal_from_symbol: local_sym.clone(),
            nominal_require_phase: Phase::Normal(0),
        };
        let b = Binding::Module(module_binding.clone());
        Expander::add_binding(id.clone(), phase, b)?;
        require_and_provides_clone.add_defined_or_required_id(
            id,
            phase,
            module_binding.clone(),
            false,
        );
        Ok(local_sym)
    })
    .map_err(|e| e.unwrap_or("bad list".to_string()))
}

fn check_ids_unbound(
    ids: Ast,
    phase: Phase,
    require_and_provides_clone: RequiresAndProvides,
) -> Result<(), String> {
    ids.foldl_pair(
        |id, _, _| require_and_provides_clone.check_not_required_or_defined(&id.try_into()?, phase),
        Ok(()),
    )
}

fn declare_module_for_expansion(
    fully_expanded_bodys_except_post_submodules: Vec<Ast>,
    m: ModuleMatcher,
    module_begin_m: ModuleBeginMatcher,
    require_and_provides: RequiresAndProvides,
    module_namespace: NameSpace,
    self_path: ResolvedModulePath,
    enclosing_self: Option<ResolvedModulePath>,
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
