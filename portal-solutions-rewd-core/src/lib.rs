use std::{
    collections::BTreeSet,
    mem::{replace, take},
    sync::Arc,
};

use swc_atoms::Atom;
use swc_common::{Mark, Span, Spanned, SyntaxContext};
use swc_ecma_ast::{
    ArrayLit, AssignExpr, AssignOp, BinExpr, BinaryOp, CallExpr, Class, ClassMember,
    ComputedPropName, Decl, ExportDecl, Expr, ExprOrSpread, ExprStmt, Id, Ident, IdentName,
    KeyValueProp, Lit, MemberExpr, MemberProp, MethodKind, ModuleDecl, ModuleItem, Number,
    PrivateName, PrivateProp, Prop, PropName, PropOrSpread, SeqExpr, Stmt, Str, ThisExpr, VarDecl,
    VarDeclarator,
};
use swc_ecma_visit::{VisitMut, VisitMutWith};
#[derive(Clone)]
#[non_exhaustive]
pub struct CommonConfig<'a> {
    pub name: Atom,
    pub rename: Arc<dyn Fn(&str) -> Option<Atom> + 'a>,
}

pub struct FRewrite<'a> {
    pub core: Expr,
    pub cfg: CommonConfig<'a>,
}
impl FRewrite<'_> {
    fn func(&mut self, a: Expr, span: Span) -> Expr {
        let s = a.span();
        return Expr::Call(CallExpr {
            span: a.span(),
            ctxt: Default::default(),
            callee: swc_ecma_ast::Callee::Expr(Box::new(Expr::Member(MemberExpr {
                span: a.span(),
                obj: Box::new(self.core.clone()),
                prop: swc_ecma_ast::MemberProp::Ident(IdentName {
                    span: a.span(),
                    sym: Atom::new("f"),
                }),
            }))),
            type_args: None,
            args: [ExprOrSpread {
                spread: None,
                expr: Box::new(a),
            }]
            .into_iter()
            .chain(
                [span.hi().0, span.lo().0]
                    .into_iter()
                    .map(|a| ExprOrSpread {
                        spread: None,
                        expr: Box::new(Expr::Lit(Lit::Num(Number {
                            span: s,
                            raw: None,
                            value: a as f64,
                        }))),
                    }),
            )
            .collect(),
        });
    }
    fn prop(&mut self, a: Expr, span: Span, k: &str, prop: PropName) -> Expr {
        let s = a.span();
        return Expr::Call(CallExpr {
            span: a.span(),
            ctxt: Default::default(),
            callee: swc_ecma_ast::Callee::Expr(Box::new(Expr::Member(MemberExpr {
                span: a.span(),
                obj: Box::new(self.core.clone()),
                prop: swc_ecma_ast::MemberProp::Ident(IdentName {
                    span: a.span(),
                    sym: Atom::new(k),
                }),
            }))),
            type_args: None,
            args: [
                ExprOrSpread {
                    spread: None,
                    expr: Box::new(a),
                },
                ExprOrSpread {
                    spread: None,
                    expr: Box::new(match prop {
                        PropName::Ident(ident_name) => Expr::Lit(Lit::Str(Str {
                            span: ident_name.span,
                            value: ident_name.sym,
                            raw: None,
                        })),
                        PropName::Str(s) => Expr::Lit(Lit::Str(s)),
                        PropName::Num(number) => Expr::Lit(Lit::Num(number)),
                        PropName::Computed(computed_prop_name) => *computed_prop_name.expr,
                        PropName::BigInt(big_int) => Expr::Lit(Lit::BigInt(big_int)),
                    }),
                },
            ]
            .into_iter()
            .chain(
                [span.hi().0, span.lo().0]
                    .into_iter()
                    .map(|a| ExprOrSpread {
                        spread: None,
                        expr: Box::new(Expr::Lit(Lit::Num(Number {
                            span: s,
                            raw: None,
                            value: a as f64,
                        }))),
                    }),
            )
            .collect(),
        });
    }
    fn class(&mut self, c: &mut Class, id: Ident) {
        let mut s = vec![];
        let mut i = vec![];
        let mut ix: usize = 0;
        // let s = c.span;
        for m in c.body.iter_mut() {
            match m {
                ClassMember::Method(m) => {
                    let prop = match &mut m.key {
                        swc_ecma_ast::PropName::Computed(computed_prop_name) => {
                            // let id2 = Ident::new_private(Atom::new("key"), c.span);
                            let name = Atom::new(format!("{}$key${ix}", &self.cfg.name));
                            ix += 1;
                            computed_prop_name.expr = Box::new(Expr::Assign(AssignExpr {
                                span: c.span,
                                op: AssignOp::Assign,
                                left: swc_ecma_ast::AssignTarget::Simple(
                                    swc_ecma_ast::SimpleAssignTarget::Member(MemberExpr {
                                        span: c.span,
                                        obj: Box::new(Expr::Ident(id.clone())),
                                        prop: swc_ecma_ast::MemberProp::PrivateName(PrivateName {
                                            span: c.span,
                                            name: name.clone(),
                                        }),
                                    }),
                                ),
                                right: take(&mut computed_prop_name.expr),
                            }));
                            swc_ecma_ast::PropName::Computed(ComputedPropName {
                                span: computed_prop_name.span,
                                expr: Box::new(Expr::Member(MemberExpr {
                                    span: c.span,
                                    obj: Box::new(Expr::Ident(id.clone())),
                                    prop: swc_ecma_ast::MemberProp::PrivateName(PrivateName {
                                        span: c.span,
                                        name,
                                    }),
                                })),
                            })
                        }
                        a => a.clone(),
                    };
                    let e = match m.is_static {
                        true => Expr::Ident(id.clone()),
                        false => Expr::Member(MemberExpr {
                            span: m.span,
                            obj: Box::new(Expr::Ident(id.clone())),
                            prop: PropName::Ident(IdentName {
                                span: m.span,
                                sym: Atom::new("prototype"),
                            })
                            .into(),
                        }),
                    };
                    let e = match m.kind {
                        MethodKind::Method => Expr::Member(MemberExpr {
                            span: m.span,
                            obj: Box::new(e),
                            prop: prop.into(),
                        }),
                        MethodKind::Getter => self.prop(e, m.span, "g", prop),
                        MethodKind::Setter => self.prop(e, m.span, "s", prop),
                    };
                    s.push(self.func(e, m.span));
                }
                ClassMember::PrivateMethod(m) if m.kind == MethodKind::Method => {
                    match m.is_static {
                        true => {
                            let e = Expr::Ident(id.clone());
                            let e = Expr::Member(MemberExpr {
                                span: m.span,
                                obj: Box::new(e),
                                prop: swc_ecma_ast::MemberProp::PrivateName(m.key.clone()),
                            });
                            s.push(self.func(e, m.span));
                        }
                        false => {
                            let e = Expr::This(ThisExpr { span: id.span });
                            let e = Expr::Member(MemberExpr {
                                span: m.span,
                                obj: Box::new(e),
                                prop: swc_ecma_ast::MemberProp::PrivateName(m.key.clone()),
                            });
                            i.push(self.func(e, m.span));
                        }
                    }
                }
                _ => {}
            }
        }
        if s.len() != 0 {
            c.body.push(ClassMember::PrivateProp(PrivateProp {
                span: c.span,
                ctxt: SyntaxContext::empty().apply_mark(Mark::new()),
                key: PrivateName {
                    span: c.span,
                    name: Atom::new(format!("{}$clinit", &self.cfg.name)),
                },
                type_ann: None,
                is_static: true,
                decorators: Default::default(),
                accessibility: None,
                is_optional: false,
                is_override: false,
                readonly: true,
                definite: false,
                value: Some(Box::new(Expr::Seq(SeqExpr {
                    span: c.span,
                    exprs: s.into_iter().map(Box::new).collect(),
                }))),
            }));
        }
        if i.len() != 0 {
            c.body.push(ClassMember::PrivateProp(PrivateProp {
                span: c.span,
                ctxt: SyntaxContext::empty().apply_mark(Mark::new()),
                key: PrivateName {
                    span: c.span,
                    name: Atom::new(format!("{}$init", &self.cfg.name)),
                },
                type_ann: None,
                is_static: false,
                decorators: Default::default(),
                accessibility: None,
                is_optional: false,
                is_override: false,
                readonly: true,
                definite: false,
                value: Some(Box::new(Expr::Seq(SeqExpr {
                    span: c.span,
                    exprs: i.into_iter().map(Box::new).collect(),
                }))),
            }));
        }
        c.body.extend((0..ix).map(|ix| {
            let name = Atom::new(format!("{}$key${ix}", &self.cfg.name));
            ClassMember::PrivateProp(PrivateProp {
                span: c.span,
                ctxt: SyntaxContext::empty().apply_mark(Mark::new()),
                key: PrivateName { span: c.span, name },
                type_ann: None,
                is_static: true,
                decorators: Default::default(),
                accessibility: None,
                is_optional: false,
                is_override: false,
                readonly: true,
                definite: false,
                value: None,
            })
        }));
    }
}
impl VisitMut for FRewrite<'_> {
    fn visit_mut_private_name(&mut self, node: &mut PrivateName) {
        node.visit_mut_children_with(self);
        if node
            .name
            .strip_prefix(&*self.cfg.name)
            .is_some_and(|a| a.starts_with("$"))
        {
            node.name = Atom::new(format!("${}", node.name));
        }
    }
    fn visit_mut_expr(&mut self, node: &mut Expr) {
        node.visit_mut_children_with(self);
        *node = match take(node) {
            Expr::Fn(f) => match Expr::Fn(f) {
                node => match node.span() {
                    span => self.func(node, span),
                },
            },
            Expr::Arrow(a) => match Expr::Arrow(a) {
                node => match node.span() {
                    span => self.func(node, span),
                },
            },
            Expr::Class(mut c) => {
                let s = c.span();
                let id = c
                    .ident
                    .get_or_insert_with(|| {
                        Ident::new_private(Atom::new(format!("{}$Class", &self.cfg.name)), s)
                    })
                    .clone();
                self.class(&mut *c.class, id);
                Expr::Class(c)
            }
            Expr::Object(o) => {
                let mut props: Vec<(&'static str, PropName, Span)> = vec![];
                for p in o.props.iter().filter_map(|a| a.as_prop()).map(|a| &**a) {
                    match p {
                        Prop::Getter(g) => props.push(("g", g.key.clone(), g.span)),
                        Prop::Setter(g) => props.push(("s", g.key.clone(), g.span)),
                        Prop::Method(g) => props.push(("m", g.key.clone(), g.span())),
                        _ => {}
                    }
                }
                props
                    .into_iter()
                    .fold(Expr::Object(o), |a, (k, prop, span)| {
                        self.prop(a, span, k, prop)
                    })
            }
            node => node,
        };
    }
    fn visit_mut_stmts(&mut self, node: &mut Vec<swc_ecma_ast::Stmt>) {
        node.visit_mut_children_with(self);
        *node = node
            .drain(..)
            .flat_map(|a| match a {
                Stmt::Decl(Decl::Class(mut c)) => {
                    self.class(&mut *c.class, c.ident.clone());
                    vec![Stmt::Decl(Decl::Class(c))]
                }
                Stmt::Decl(Decl::Fn(f)) => {
                    let span = f.span();
                    let e = self.func(Expr::Ident(f.ident.clone()), span);
                    vec![
                        Stmt::Decl(Decl::Fn(f)),
                        Stmt::Expr(ExprStmt {
                            span,
                            expr: Box::new(e),
                        }),
                    ]
                }
                a => vec![a],
            })
            .collect();
    }
    fn visit_mut_module(&mut self, node: &mut swc_ecma_ast::Module) {
        node.visit_mut_children_with(self);
        node.body = node
            .body
            .drain(..)
            .flat_map(|a| match a {
                ModuleItem::Stmt(Stmt::Decl(Decl::Class(mut c))) => {
                    self.class(&mut *c.class, c.ident.clone());
                    vec![ModuleItem::Stmt(Stmt::Decl(Decl::Class(c)))]
                }
                ModuleItem::Stmt(Stmt::Decl(Decl::Fn(f))) => {
                    let span = f.span();
                    let e = self.func(Expr::Ident(f.ident.clone()), span);
                    vec![
                        ModuleItem::Stmt(Stmt::Decl(Decl::Fn(f))),
                        ModuleItem::Stmt(Stmt::Expr(ExprStmt {
                            span,
                            expr: Box::new(e),
                        })),
                    ]
                }
                ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                    span,
                    decl: Decl::Class(mut c),
                })) => {
                    self.class(&mut *c.class, c.ident.clone());
                    vec![ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                        span,
                        decl: Decl::Class(c),
                    }))]
                }
                ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                    span: s2,
                    decl: Decl::Fn(f),
                })) => {
                    let span = f.span();
                    let e = self.func(Expr::Ident(f.ident.clone()), span);
                    vec![
                        ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                            span: s2,
                            decl: Decl::Fn(f),
                        })),
                        ModuleItem::Stmt(Stmt::Expr(ExprStmt {
                            span,
                            expr: Box::new(e),
                        })),
                    ]
                }
                a => vec![a],
            })
            .collect();
    }
}
pub struct CoreRewrite<'a> {
    pub core: Expr,
    pub cfg: CommonConfig<'a>,
    pub decls: BTreeSet<Id>,
}
impl CoreRewrite<'_> {
    pub fn rewrite(&self, sym: &mut Atom) {
        if let Some(r) = (self.cfg.rename)(&**sym) {
            *sym = r;
        }
    }
}
impl VisitMut for CoreRewrite<'_> {
    fn visit_mut_stmts(&mut self, node: &mut Vec<Stmt>) {
        let old = take(&mut self.decls);
        node.visit_mut_children_with(self);
        let old = replace(&mut self.decls, old);
        node.insert(
            0,
            Stmt::Decl(Decl::Var(Box::new(VarDecl {
                span: Span::dummy_with_cmt(),
                ctxt: Default::default(),
                kind: swc_ecma_ast::VarDeclKind::Let,
                declare: false,
                decls: old
                    .into_iter()
                    .map(|a| VarDeclarator {
                        span: Span::dummy_with_cmt(),
                        init: None,
                        definite: false,
                        name: swc_ecma_ast::Pat::Ident(a.into()),
                    })
                    .collect(),
            }))),
        );
    }
    fn visit_mut_module(&mut self, node: &mut swc_ecma_ast::Module) {
        let old = take(&mut self.decls);
        node.visit_mut_children_with(self);
        let old = replace(&mut self.decls, old);
        node.body.insert(
            0,
            ModuleItem::Stmt(Stmt::Decl(Decl::Var(Box::new(VarDecl {
                span: Span::dummy_with_cmt(),
                ctxt: Default::default(),
                kind: swc_ecma_ast::VarDeclKind::Let,
                declare: false,
                decls: old
                    .into_iter()
                    .map(|a| VarDeclarator {
                        span: Span::dummy_with_cmt(),
                        init: None,
                        definite: false,
                        name: swc_ecma_ast::Pat::Ident(a.into()),
                    })
                    .collect(),
            })))),
        );
    }
    fn visit_mut_with_stmt(&mut self, node: &mut swc_ecma_ast::WithStmt) {
        node.visit_mut_children_with(self);
        node.obj = Box::new(Expr::Call(CallExpr {
            span: node.span,
            ctxt: Default::default(),
            callee: swc_ecma_ast::Callee::Expr(Box::new(Expr::Member(MemberExpr {
                span: node.span,
                obj: Box::new(self.core.clone()),
                prop: swc_ecma_ast::MemberProp::Ident(IdentName {
                    span: node.span,
                    sym: Atom::new("$with"),
                }),
            }))),
            args: [
                ExprOrSpread {
                    expr: take(&mut node.obj),
                    spread: None,
                },
                ExprOrSpread {
                    spread: None,
                    expr: Box::new(Expr::Lit(Lit::Str(Str {
                        span: node.span,
                        value: Atom::new(&*self.cfg.name),
                        raw: None,
                    }))),
                },
            ]
            .into_iter()
            .collect(),
            type_args: None,
        }))
    }
    fn visit_mut_member_expr(&mut self, node: &mut MemberExpr) {
        node.visit_mut_children_with(self);
        if let MemberProp::PrivateName(_) = &node.prop {
            return;
        }
        if let MemberProp::Ident(i) = &mut node.prop {
            self.rewrite(&mut i.sym);
            return;
        }
        let camobj = Ident::new_private(Atom::new(format!("{}$camobj", &self.cfg.name)), node.span);
        self.decls.insert(camobj.to_id());
        // let cammem = Ident::new_private(Atom::new(format!("{}$cammem",&self.cfg.name)), node.span);
        node.obj = Box::new(Expr::Assign(AssignExpr {
            span: node.span,
            op: AssignOp::Assign,
            left: camobj.clone().into(),
            right: take(&mut node.obj),
        }));
        node.prop = swc_ecma_ast::MemberProp::Computed(ComputedPropName {
            span: node.span,
            expr: Box::new(Expr::Call(CallExpr {
                span: node.span,
                ctxt: Default::default(),
                callee: swc_ecma_ast::Callee::Expr(Box::new(Expr::Member(MemberExpr {
                    span: node.span,
                    obj: Box::new(self.core.clone()),
                    prop: swc_ecma_ast::MemberProp::Ident(IdentName {
                        span: node.span,
                        sym: Atom::new("$member"),
                    }),
                }))),
                args: [
                    ExprOrSpread {
                        spread: None,
                        expr: camobj.into(),
                    },
                    ExprOrSpread {
                        expr: match take(&mut node.prop) {
                            swc_ecma_ast::MemberProp::Ident(ident_name) => {
                                Box::new(Expr::Lit(Lit::Str(Str {
                                    span: ident_name.span,
                                    value: ident_name.sym,
                                    raw: None,
                                })))
                            }
                            swc_ecma_ast::MemberProp::PrivateName(private_name) => todo!(),
                            swc_ecma_ast::MemberProp::Computed(computed_prop_name) => {
                                computed_prop_name.expr
                            }
                        },
                        spread: None,
                    },
                    ExprOrSpread {
                        spread: None,
                        expr: Box::new(Expr::Lit(Lit::Str(Str {
                            span: node.span,
                            value: Atom::new(&*self.cfg.name),
                            raw: None,
                        }))),
                    },
                ]
                .into_iter()
                .collect(),
                type_args: None,
            })),
        })
    }
    fn visit_mut_prop(&mut self, node: &mut Prop) {
        if let Prop::Shorthand(s) = node {
            *node = Prop::KeyValue(KeyValueProp {
                key: s.clone().into(),
                value: s.clone().into(),
            });
        }
        node.visit_mut_children_with(self);
    }
    fn visit_mut_expr(&mut self, node: &mut Expr) {
        node.visit_mut_children_with(self);
        *node = match take(node) {
            Expr::Bin(BinExpr {
                left,
                right,
                span,
                op: BinaryOp::In,
            }) if !left.is_private_name() => {
                let camobj =
                    Ident::new_private(Atom::new(format!("{}$camobj", &self.cfg.name)), span);
                let cammem =
                    Ident::new_private(Atom::new(format!("{}$cammem", &self.cfg.name)), span);
                self.decls.insert(camobj.to_id());
                self.decls.insert(cammem.to_id());
                Expr::Seq(SeqExpr {
                    span,
                    exprs: [
                        Box::new(Expr::Assign(AssignExpr {
                            span,
                            op: AssignOp::Assign,
                            left: cammem.clone().into(),
                            right: left,
                        })),
                        Box::new(Expr::Bin(BinExpr {
                            span,
                            op: BinaryOp::In,
                            left: Box::new(Expr::Call(CallExpr {
                                span: span,
                                ctxt: Default::default(),
                                callee: swc_ecma_ast::Callee::Expr(Box::new(Expr::Member(
                                    MemberExpr {
                                        span: span,
                                        obj: Box::new(self.core.clone()),
                                        prop: swc_ecma_ast::MemberProp::Ident(IdentName {
                                            span: span,
                                            sym: Atom::new("$member"),
                                        }),
                                    },
                                ))),
                                args: [
                                    ExprOrSpread {
                                        spread: None,
                                        expr: Box::new(Expr::Assign(AssignExpr {
                                            span,
                                            op: AssignOp::Assign,
                                            left: camobj.clone().into(),
                                            right: right,
                                        })),
                                    },
                                    ExprOrSpread {
                                        expr: cammem.into(),
                                        spread: None,
                                    },
                                    ExprOrSpread {
                                        spread: None,
                                        expr: Box::new(Expr::Lit(Lit::Str(Str {
                                            span: span,
                                            value: Atom::new(&*self.cfg.name),
                                            raw: None,
                                        }))),
                                    },
                                ]
                                .into_iter()
                                .collect(),
                                type_args: None,
                            })),
                            right: camobj.into(),
                        })),
                    ]
                    .into_iter()
                    .collect(),
                })
            }
            node => node,
        }
    }
    fn visit_mut_ident(&mut self, node: &mut Ident) {
        node.visit_mut_children_with(self);
        self.rewrite(&mut node.sym);
    }
    fn visit_mut_private_name(&mut self, node: &mut PrivateName) {
        node.visit_mut_children_with(self);
        self.rewrite(&mut node.name);
    }
}
