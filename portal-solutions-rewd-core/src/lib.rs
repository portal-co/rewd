use std::mem::take;

use swc_atoms::Atom;
use swc_common::{Mark, Span, Spanned, SyntaxContext};
use swc_ecma_ast::{
    AssignExpr, AssignOp, CallExpr, Class, ClassMember, ComputedPropName, Decl, ExportDecl, Expr,
    ExprOrSpread, ExprStmt, Ident, IdentName, Lit, MemberExpr, MethodKind, ModuleDecl, ModuleItem,
    Number, PrivateName, PrivateProp, Prop, PropName, SeqExpr, Stmt, Str, ThisExpr,
};
use swc_ecma_visit::{VisitMut, VisitMutWith};

pub struct FRewrite {
    pub core: Expr,
}
impl FRewrite {
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
                            let name = Atom::new(format!("$key${ix}"));
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
                    name: Atom::new("$clinit"),
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
                    name: Atom::new("$init"),
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
            let name = Atom::new(format!("$key${ix}"));
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
impl VisitMut for FRewrite {
    fn visit_mut_private_name(&mut self, node: &mut PrivateName) {
        node.visit_mut_children_with(self);
        if node.name.starts_with("$") {
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
                    .get_or_insert_with(|| Ident::new_private(Atom::new("Class"), s))
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
