use crate::assert_unreachable;
use crate::term::{Name, RcPtr, SyntaxContext, Term};
use ariadne::{Color, Label};
use grammar::syntactic::{ParseTree, Ptr};

pub(crate) trait BuiltinType {
    type ElimRules;
    fn new_from_pattern_rules<'src>(
        ctx: &SyntaxContext<'src>,
        rules: &[Ptr<ParseTree<'src>>],
    ) -> Result<Option<Self::ElimRules>, ()>;
}

pub(crate) struct BuiltinUnit;
pub(crate) struct BuiltinPair;
pub(crate) struct BuiltinBool;
pub(crate) struct BuiltinBottom;

impl BuiltinType for BuiltinUnit {
    type ElimRules = RcPtr<Term>;

    fn new_from_pattern_rules<'src>(
        ctx: &SyntaxContext<'src>,
        rules: &[Ptr<ParseTree<'src>>],
    ) -> Result<Option<Self::ElimRules>, ()> {
        if rules.len() != 1 {
            return Ok(None);
        }
        match rules.first() {
            Some(Ptr {
                location,
                data:
                    box ParseTree::PatternRule {
                        constructor,
                        variables,
                        body,
                    },
            }) => match constructor.get_literal() {
                "Unit" if variables.is_empty() => match Term::new_from_expr(ctx, body) {
                    None => Err(()),
                    Some(tree) => Ok(Some(tree)),
                },
                "Unit" => Err(ctx.error(location.start, |builder| {
                    builder
                        .with_message("Illegal elimination for Unit type")
                        .with_label(
                            Label::new((ctx.source_name, variables[0].location.clone()))
                                .with_color(Color::Red)
                                .with_message("unexpected variable(s)"),
                        )
                        .finish()
                })),
                _ => Ok(None),
            },
            _ => assert_unreachable!(),
        }
    }
}

impl BuiltinType for BuiltinPair {
    type ElimRules = (Option<Name>, Option<Name>, RcPtr<Term>);

    fn new_from_pattern_rules<'src>(
        ctx: &SyntaxContext<'src>,
        rules: &[Ptr<ParseTree<'src>>],
    ) -> Result<Option<Self::ElimRules>, ()> {
        if rules.len() != 1 {
            return Ok(None);
        }
        match rules.first() {
            Some(Ptr {
                location,
                data:
                    box ParseTree::PatternRule {
                        constructor,
                        variables,
                        body,
                    },
            }) => match constructor.get_literal() {
                "Pair" if variables.len() == 2 => {
                    let (left, _left_guard) = Term::new_from_parameter(ctx, &variables[0])
                        .map(|name| ctx.push_variable(name))
                        .map(|(x, y)| (Some(x), Some(y)))
                        .unwrap_or((None, None));
                    let (right, _right_guard) = Term::new_from_parameter(ctx, &variables[1])
                        .map(|name| ctx.push_variable(name))
                        .map(|(x, y)| (Some(x), Some(y)))
                        .unwrap_or((None, None));
                    match Term::new_from_expr(ctx, body) {
                        None => Err(()),
                        Some(body) => Ok(Some((left, right, body))),
                    }
                }
                "Pair" => Err(ctx.error(location.start, |builder| {
                    builder
                        .with_message("Illegal elimination for Sigma type")
                        .with_label(
                            Label::new((ctx.source_name, location.clone()))
                                .with_color(Color::Red)
                                .with_message(
                                    "the number parameter is not unmatched for Pair constructor",
                                ),
                        )
                        .finish()
                })),
                _ => Ok(None),
            },
            _ => assert_unreachable!(),
        }
    }
}

impl BuiltinType for BuiltinBottom {
    type ElimRules = ();

    fn new_from_pattern_rules<'src>(
        _: &SyntaxContext<'src>,
        rules: &[Ptr<ParseTree<'src>>],
    ) -> Result<Option<Self::ElimRules>, ()> {
        if rules.is_empty() {
            Ok(Some(()))
        } else {
            Ok(None)
        }
    }
}

impl BuiltinType for BuiltinBool {
    type ElimRules = (RcPtr<Term>, RcPtr<Term>);

    fn new_from_pattern_rules<'src>(
        ctx: &SyntaxContext<'src>,
        rules: &[Ptr<ParseTree<'src>>],
    ) -> Result<Option<Self::ElimRules>, ()> {
        if rules.len() != 2 {
            return Ok(None);
        }
        fn basic_info<'a, 'src: 'a>(
            tree: &'a ParseTree<'src>,
        ) -> (&'src str, usize, &'a Ptr<ParseTree<'src>>) {
            match tree {
                ParseTree::PatternRule {
                    constructor,
                    variables,
                    body,
                } => (constructor.get_literal(), variables.len(), body),
                _ => assert_unreachable!(),
            }
        }
        let info = [
            basic_info(rules[0].data.as_ref()),
            basic_info(rules[1].data.as_ref()),
        ];
        match (info[0], info[1]) {
            (("True", 0, true_body), ("False", 0, false_body))
            | (("False", 0, false_body), ("True", 0, true_body)) => {
                let r#true = Term::new_from_expr(ctx, true_body);
                let r#false = Term::new_from_expr(ctx, false_body);
                let branches =
                    r#true.and_then(move |r#true| r#false.map(move |r#false| (r#true, r#false)));
                match branches {
                    None => Err(()),
                    Some(branches) => Ok(Some(branches)),
                }
            }
            (("True", i, _), ("False", j, _)) | (("False", i, _), ("True", j, _)) => {
                let report_error = |idx: usize| {
                    ctx.error(rules[idx].location.start, |builder| {
                        builder
                            .with_message("Illegal elimination for Bool type")
                            .with_label(
                                Label::new((ctx.source_name, rules[idx].location.clone()))
                                    .with_color(Color::Red)
                                    .with_message(format!(
                                        "unexpected parameter(s) for {} constructor",
                                        info[idx].0
                                    )),
                            )
                            .finish()
                    })
                };
                if i > 0 {
                    report_error(0);
                }
                if j > 0 {
                    report_error(1);
                }
                Err(())
            }
            (("True", _, _), ("True", _, _)) | (("False", _, _), ("False", _, _)) => {
                ctx.error(rules[0].location.start, |builder| {
                    builder
                        .with_message("Overlapped patterns")
                        .with_label(
                            Label::new((ctx.source_name, rules[0].location.clone()))
                                .with_color(Color::Red)
                                .with_message(format!(
                                    "the pattern {} is already covered here",
                                    info[0].0
                                )),
                        )
                        .with_label(
                            Label::new((ctx.source_name, rules[1].location.clone()))
                                .with_color(Color::Red)
                                .with_message("...however, it appears again later"),
                        )
                        .finish()
                });
                Err(())
            }
            _ => Ok(None),
        }
    }
}
