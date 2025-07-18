use itertools::Itertools;

use ruff_macros::{ViolationMetadata, derive_message_formats};
use ruff_python_ast::helpers::contains_effect;
use ruff_python_ast::parenthesize::parenthesized_range;
use ruff_python_ast::{self as ast, Stmt};
use ruff_python_parser::{TokenKind, Tokens};
use ruff_python_semantic::Binding;
use ruff_text_size::{Ranged, TextRange, TextSize};

use crate::checkers::ast::Checker;
use crate::fix::edits::delete_stmt;
use crate::{Edit, Fix, FixAvailability, Violation};

/// ## What it does
/// Checks for the presence of unused variables in function scopes.
///
/// ## Why is this bad?
/// A variable that is defined but not used is likely a mistake, and should
/// be removed to avoid confusion.
///
/// If a variable is intentionally defined-but-not-used, it should be
/// prefixed with an underscore, or some other value that adheres to the
/// [`lint.dummy-variable-rgx`] pattern.
///
/// ## Example
/// ```python
/// def foo():
///     x = 1
///     y = 2
///     return x
/// ```
///
/// Use instead:
/// ```python
/// def foo():
///     x = 1
///     return x
/// ```
///
/// ## Fix safety
///
/// This rule's fix is marked as unsafe because removing an unused variable assignment may
/// delete comments that are attached to the assignment.
///
/// ## Options
/// - `lint.dummy-variable-rgx`
#[derive(ViolationMetadata)]
pub(crate) struct UnusedVariable {
    pub name: String,
}

impl Violation for UnusedVariable {
    const FIX_AVAILABILITY: FixAvailability = FixAvailability::Sometimes;

    #[derive_message_formats]
    fn message(&self) -> String {
        let UnusedVariable { name } = self;
        format!("Local variable `{name}` is assigned to but never used")
    }

    fn fix_title(&self) -> Option<String> {
        let UnusedVariable { name } = self;
        Some(format!("Remove assignment to unused variable `{name}`"))
    }
}

/// Return the [`TextRange`] of the token before the next match of the predicate
fn match_token_before<F>(tokens: &Tokens, location: TextSize, f: F) -> Option<TextRange>
where
    F: Fn(TokenKind) -> bool,
{
    for (prev, current) in tokens.after(location).iter().tuple_windows() {
        if f(current.kind()) {
            return Some(prev.range());
        }
    }
    None
}

/// Return the [`TextRange`] of the token after the next match of the predicate, skipping over
/// any bracketed expressions.
fn match_token_after<F>(tokens: &Tokens, location: TextSize, f: F) -> Option<TextRange>
where
    F: Fn(TokenKind) -> bool,
{
    // Track the bracket depth.
    let mut nesting = 0u32;

    for (current, next) in tokens.after(location).iter().tuple_windows() {
        match current.kind() {
            TokenKind::Lpar | TokenKind::Lsqb | TokenKind::Lbrace => {
                nesting = nesting.saturating_add(1);
            }
            TokenKind::Rpar | TokenKind::Rsqb | TokenKind::Rbrace => {
                nesting = nesting.saturating_sub(1);
            }
            _ => {}
        }

        // If we're in nested brackets, continue.
        if nesting > 0 {
            continue;
        }

        if f(current.kind()) {
            return Some(next.range());
        }
    }
    None
}

/// Return the [`TextRange`] of the token matching the predicate or the first mismatched
/// bracket, skipping over any bracketed expressions.
fn match_token_or_closing_brace<F>(tokens: &Tokens, location: TextSize, f: F) -> Option<TextRange>
where
    F: Fn(TokenKind) -> bool,
{
    // Track the nesting level.
    let mut nesting = 0u32;

    for token in tokens.after(location) {
        match token.kind() {
            TokenKind::Lpar | TokenKind::Lsqb | TokenKind::Lbrace => {
                nesting = nesting.saturating_add(1);
            }
            TokenKind::Rpar | TokenKind::Rsqb | TokenKind::Rbrace => {
                if nesting == 0 {
                    return Some(token.range());
                }
                nesting = nesting.saturating_sub(1);
            }
            _ => {}
        }

        // If we're in nested brackets, continue.
        if nesting > 0 {
            continue;
        }

        if f(token.kind()) {
            return Some(token.range());
        }
    }
    None
}

/// Generate a [`Edit`] to remove an unused variable assignment to a [`Binding`].
fn remove_unused_variable(binding: &Binding, checker: &Checker) -> Option<Fix> {
    let node_id = binding.source?;
    let statement = checker.semantic().statement(node_id);
    let parent = checker.semantic().parent_statement(node_id);
    let isolation = Checker::isolation(checker.semantic().parent_statement_id(node_id));

    // First case: simple assignment (`x = 1`)
    if let Stmt::Assign(ast::StmtAssign { targets, value, .. }) = statement {
        if let Some(target) = targets
            .iter()
            .find(|target| binding.range() == target.range())
        {
            if target.is_name_expr() {
                return if targets.len() > 1
                    || contains_effect(value, |id| checker.semantic().has_builtin_binding(id))
                {
                    // If the expression is complex (`x = foo()`), remove the assignment,
                    // but preserve the right-hand side.
                    let start = parenthesized_range(
                        target.into(),
                        statement.into(),
                        checker.comment_ranges(),
                        checker.locator().contents(),
                    )
                    .unwrap_or(target.range())
                    .start();
                    let end = match_token_after(checker.tokens(), target.end(), |token| {
                        token == TokenKind::Equal
                    })?
                    .start();
                    let edit = Edit::deletion(start, end);
                    Some(Fix::unsafe_edit(edit))
                } else {
                    // If (e.g.) assigning to a constant (`x = 1`), delete the entire statement.
                    let edit = delete_stmt(statement, parent, checker.locator(), checker.indexer());
                    Some(Fix::unsafe_edit(edit).isolate(isolation))
                };
            }
        } else {
            let name = binding.name(checker.source());
            let renamed = format!("_{name}");
            if checker.settings().dummy_variable_rgx.is_match(&renamed) {
                let edit = Edit::range_replacement(renamed, binding.range());

                return Some(Fix::unsafe_edit(edit).isolate(isolation));
            }
        }
    }

    // Second case: simple annotated assignment (`x: int = 1`)
    if let Stmt::AnnAssign(ast::StmtAnnAssign {
        target,
        value: Some(value),
        ..
    }) = statement
    {
        if target.is_name_expr() {
            return if contains_effect(value, |id| checker.semantic().has_builtin_binding(id)) {
                // If the expression is complex (`x = foo()`), remove the assignment,
                // but preserve the right-hand side.
                let start = statement.start();
                let end =
                    match_token_after(checker.tokens(), start, |token| token == TokenKind::Equal)?
                        .start();
                let edit = Edit::deletion(start, end);
                Some(Fix::unsafe_edit(edit))
            } else {
                // If (e.g.) assigning to a constant (`x = 1`), delete the entire statement.
                let edit = delete_stmt(statement, parent, checker.locator(), checker.indexer());
                Some(Fix::unsafe_edit(edit).isolate(isolation))
            };
        }
    }

    // Third case: with_item (`with foo() as x:`)
    if let Stmt::With(ast::StmtWith { items, .. }) = statement {
        // Find the binding that matches the given `Range`.
        // TODO(charlie): Store the `WithItem` in the `Binding`.
        for item in items {
            if let Some(optional_vars) = &item.optional_vars {
                if optional_vars.range() == binding.range() {
                    // Find the first token before the `as` keyword.
                    let start =
                        match_token_before(checker.tokens(), item.context_expr.start(), |token| {
                            token == TokenKind::As
                        })?
                        .end();

                    // Find the first colon, comma, or closing bracket after the `as` keyword.
                    let end = match_token_or_closing_brace(checker.tokens(), start, |token| {
                        token == TokenKind::Colon || token == TokenKind::Comma
                    })?
                    .start();

                    let edit = Edit::deletion(start, end);
                    return Some(Fix::unsafe_edit(edit));
                }
            }
        }
    }

    None
}

/// F841
pub(crate) fn unused_variable(checker: &Checker, name: &str, binding: &Binding) {
    if binding.is_unpacked_assignment() {
        return;
    }

    let mut diagnostic = checker.report_diagnostic(
        UnusedVariable {
            name: name.to_string(),
        },
        binding.range(),
    );
    if let Some(fix) = remove_unused_variable(binding, checker) {
        diagnostic.set_fix(fix);
    }
}
