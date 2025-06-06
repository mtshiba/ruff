use ruff_python_ast::{Expr, StmtIf};

use ruff_macros::{ViolationMetadata, derive_message_formats};
use ruff_python_ast::stmt_if::if_elif_branches;
use ruff_text_size::Ranged;

use crate::Violation;
use crate::checkers::ast::Checker;

/// ## What it does
/// Checks for `if` statements that use non-empty tuples as test conditions.
///
/// ## Why is this bad?
/// Non-empty tuples are always `True`, so an `if` statement with a non-empty
/// tuple as its test condition will always pass. This is likely a mistake.
///
/// ## Example
/// ```python
/// if (False,):
///     print("This will always run")
/// ```
///
/// Use instead:
/// ```python
/// if False:
///     print("This will never run")
/// ```
///
/// ## References
/// - [Python documentation: The `if` statement](https://docs.python.org/3/reference/compound_stmts.html#the-if-statement)
#[derive(ViolationMetadata)]
pub(crate) struct IfTuple;

impl Violation for IfTuple {
    #[derive_message_formats]
    fn message(&self) -> String {
        "If test is a tuple, which is always `True`".to_string()
    }
}

/// F634
pub(crate) fn if_tuple(checker: &Checker, stmt_if: &StmtIf) {
    for branch in if_elif_branches(stmt_if) {
        let Expr::Tuple(tuple) = &branch.test else {
            continue;
        };
        if tuple.is_empty() {
            continue;
        }
        checker.report_diagnostic(IfTuple, branch.test.range());
    }
}
