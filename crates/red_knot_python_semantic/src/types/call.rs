use super::context::InferContext;
use super::diagnostic::CALL_NON_CALLABLE;
use super::{Signature, Type, TypeArrayDisplay, UnionBuilder};
use crate::Db;
use ruff_python_ast as ast;

mod arguments;
mod bind;

pub(super) use arguments::{Argument, CallArguments};
pub(super) use bind::{bind_call, CallBinding};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CallOutcome<'db> {
    Callable {
        binding: CallBinding<'db>,
    },
    NotCallable {
        not_callable_ty: Type<'db>,
    },
    Union {
        called_ty: Type<'db>,
        outcomes: Box<[CallOutcome<'db>]>,
    },
    PossiblyUnboundDunderCall {
        called_ty: Type<'db>,
        call_outcome: Box<CallOutcome<'db>>,
    },
}

impl<'db> CallOutcome<'db> {
    /// Create a new `CallOutcome::Callable` with given binding.
    pub(super) fn callable(binding: CallBinding<'db>) -> CallOutcome<'db> {
        CallOutcome::Callable { binding }
    }

    /// Create a new `CallOutcome::NotCallable` with given not-callable type.
    pub(super) fn not_callable(not_callable_ty: Type<'db>) -> CallOutcome<'db> {
        CallOutcome::NotCallable { not_callable_ty }
    }

    /// Create a new `CallOutcome::Union` with given wrapped outcomes.
    pub(super) fn union(
        called_ty: Type<'db>,
        outcomes: impl IntoIterator<Item = CallOutcome<'db>>,
    ) -> CallOutcome<'db> {
        CallOutcome::Union {
            called_ty,
            outcomes: outcomes.into_iter().collect(),
        }
    }

    /// Get the return type of the call, or `None` if not callable.
    pub(super) fn return_type(&self, db: &'db dyn Db) -> Option<Type<'db>> {
        match self {
            Self::Callable { binding } => Some(binding.return_type()),
            Self::NotCallable { not_callable_ty: _ } => None,
            Self::Union {
                outcomes,
                called_ty: _,
            } => outcomes
                .iter()
                // If all outcomes are NotCallable, we return None; if some outcomes are callable
                // and some are not, we return a union including Unknown.
                .fold(None, |acc, outcome| {
                    let ty = outcome.return_type(db);
                    match (acc, ty) {
                        (None, None) => None,
                        (None, Some(ty)) => Some(UnionBuilder::new(db).add(ty)),
                        (Some(builder), ty) => Some(builder.add(ty.unwrap_or(Type::unknown()))),
                    }
                })
                .map(UnionBuilder::build),
            Self::PossiblyUnboundDunderCall { call_outcome, .. } => call_outcome.return_type(db),
        }
    }

    /// Get the return type of the call, emitting default diagnostics if needed.
    pub(super) fn unwrap_with_diagnostic(
        &self,
        context: &InferContext<'db>,
        node: ast::AnyNodeRef,
    ) -> Type<'db> {
        match self.return_type_result(context, node) {
            Ok(return_ty) => return_ty,
            Err(NotCallableError::Type {
                not_callable_ty,
                return_ty,
            }) => {
                context.report_lint(
                    &CALL_NON_CALLABLE,
                    node,
                    format_args!(
                        "Object of type `{}` is not callable",
                        not_callable_ty.display(context.db())
                    ),
                );
                return_ty
            }
            Err(NotCallableError::UnionElement {
                not_callable_ty,
                called_ty,
                return_ty,
            }) => {
                context.report_lint(
                    &CALL_NON_CALLABLE,
                    node,
                    format_args!(
                        "Object of type `{}` is not callable (due to union element `{}`)",
                        called_ty.display(context.db()),
                        not_callable_ty.display(context.db()),
                    ),
                );
                return_ty
            }
            Err(NotCallableError::UnionElements {
                not_callable_tys,
                called_ty,
                return_ty,
            }) => {
                context.report_lint(
                    &CALL_NON_CALLABLE,
                    node,
                    format_args!(
                        "Object of type `{}` is not callable (due to union elements {})",
                        called_ty.display(context.db()),
                        not_callable_tys.display(context.db()),
                    ),
                );
                return_ty
            }
            Err(NotCallableError::PossiblyUnboundDunderCall {
                callable_ty: called_ty,
                return_ty,
            }) => {
                context.report_lint(
                    &CALL_NON_CALLABLE,
                    node,
                    format_args!(
                        "Object of type `{}` is not callable (possibly unbound `__call__` method)",
                        called_ty.display(context.db())
                    ),
                );
                return_ty
            }
        }
    }

    /// Get the return type of the call as a result.
    pub(super) fn return_type_result(
        &self,
        context: &InferContext<'db>,
        node: ast::AnyNodeRef,
    ) -> Result<Type<'db>, NotCallableError<'db>> {
        // TODO should this method emit diagnostics directly, or just return results that allow the
        // caller to decide about emitting diagnostics? Currently it emits binding diagnostics, but
        // only non-callable diagnostics in the union case, which is inconsistent.
        match self {
            Self::Callable { binding } => {
                // TODO: Move this out of the `CallOutcome` and into `TypeInferenceBuilder`?
                // This check is required everywhere where we call `return_type_result`
                // from the TypeInferenceBuilder.
                binding.report_diagnostics(context, node);
                Ok(binding.return_type())
            }
            Self::NotCallable { not_callable_ty } => Err(NotCallableError::Type {
                not_callable_ty: *not_callable_ty,
                return_ty: Type::unknown(),
            }),
            Self::PossiblyUnboundDunderCall {
                called_ty,
                call_outcome,
            } => Err(NotCallableError::PossiblyUnboundDunderCall {
                callable_ty: *called_ty,
                return_ty: call_outcome
                    .return_type(context.db())
                    .unwrap_or(Type::unknown()),
            }),
            Self::Union {
                outcomes,
                called_ty,
            } => {
                let mut not_callable = vec![];
                let mut union_builder = UnionBuilder::new(context.db());
                for outcome in outcomes {
                    let return_ty = match outcome {
                        Self::NotCallable { not_callable_ty } => {
                            not_callable.push(*not_callable_ty);
                            Type::unknown()
                        }
                        _ => outcome.unwrap_with_diagnostic(context, node),
                    };
                    union_builder = union_builder.add(return_ty);
                }
                let return_ty = union_builder.build();
                match not_callable[..] {
                    [] => Ok(return_ty),
                    [elem] => Err(NotCallableError::UnionElement {
                        not_callable_ty: elem,
                        called_ty: *called_ty,
                        return_ty,
                    }),
                    _ if not_callable.len() == outcomes.len() => Err(NotCallableError::Type {
                        not_callable_ty: *called_ty,
                        return_ty,
                    }),
                    _ => Err(NotCallableError::UnionElements {
                        not_callable_tys: not_callable.into_boxed_slice(),
                        called_ty: *called_ty,
                        return_ty,
                    }),
                }
            }
        }
    }
}

pub(super) enum CallDunderResult<'db> {
    CallOutcome(CallOutcome<'db>),
    PossiblyUnbound(CallOutcome<'db>),
    MethodNotAvailable,
}

impl<'db> CallDunderResult<'db> {
    pub(super) fn return_type(&self, db: &'db dyn Db) -> Option<Type<'db>> {
        match self {
            Self::CallOutcome(outcome) => outcome.return_type(db),
            Self::PossiblyUnbound { .. } => None,
            Self::MethodNotAvailable => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum NotCallableError<'db> {
    /// The type is not callable.
    Type {
        not_callable_ty: Type<'db>,
        return_ty: Type<'db>,
    },
    /// A single union element is not callable.
    UnionElement {
        not_callable_ty: Type<'db>,
        called_ty: Type<'db>,
        return_ty: Type<'db>,
    },
    /// Multiple (but not all) union elements are not callable.
    UnionElements {
        not_callable_tys: Box<[Type<'db>]>,
        called_ty: Type<'db>,
        return_ty: Type<'db>,
    },
    PossiblyUnboundDunderCall {
        callable_ty: Type<'db>,
        return_ty: Type<'db>,
    },
}

impl<'db> NotCallableError<'db> {
    /// The return type that should be used when a call is not callable.
    pub(super) fn return_type(&self) -> Type<'db> {
        match self {
            Self::Type { return_ty, .. } => *return_ty,
            Self::UnionElement { return_ty, .. } => *return_ty,
            Self::UnionElements { return_ty, .. } => *return_ty,
            Self::PossiblyUnboundDunderCall { return_ty, .. } => *return_ty,
        }
    }

    /// The resolved type that was not callable.
    ///
    /// For unions, returns the union type itself, which may contain a mix of callable and
    /// non-callable types.
    pub(super) fn called_type(&self) -> Type<'db> {
        match self {
            Self::Type {
                not_callable_ty, ..
            } => *not_callable_ty,
            Self::UnionElement { called_ty, .. } => *called_ty,
            Self::UnionElements { called_ty, .. } => *called_ty,
            Self::PossiblyUnboundDunderCall {
                callable_ty: called_ty,
                ..
            } => *called_ty,
        }
    }
}
