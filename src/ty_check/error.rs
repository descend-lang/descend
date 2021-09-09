use super::Ty;
use crate::ast::internal::Place;
use crate::ast::{Ident, Ownership, PlaceExpr};
use crate::error;
use crate::error::{default_format, ErrorReported};
use crate::parser::SourceCode;
use annotate_snippets::display_list::DisplayList;
use annotate_snippets::snippet::{Annotation, AnnotationType, Slice, Snippet};

#[must_use]
#[derive(Debug)]
pub enum TyError {
    MultiError(Vec<TyError>),
    MutabilityNotAllowed(Ty),
    CtxError(CtxError),
    SubTyError(SubTyError),
    // "Trying to violate existing borrow of {:?}.",
    // p1 under own1 is in conflict because of BorrowingError
    ConflictingBorrow(Box<PlaceExpr>, Ownership, BorrowingError),
    PrvValueAlreadyInUse(String),
    // No loan the reference points to has a type that fits the reference element type
    ReferenceToIncompatibleType,
    // ownership of reference and loan it refers to do not fit
    ReferenceToWrongOwnership,
    // This would mean that the reference points to nothing, e.g., because the value was moved
    // out from under the reference which is forbidden.
    ReferenceToDeadTy,
    // TODO remove as soon as possible
    String(String),
}

impl<'a> std::iter::FromIterator<TyError> for TyError {
    fn from_iter<T: IntoIterator<Item = TyError>>(iter: T) -> Self {
        TyError::MultiError(iter.into_iter().collect())
    }
}

impl TyError {
    pub fn emit(&self, source: &SourceCode) -> ErrorReported {
        match &self {
            TyError::MultiError(errs) => {
                for err in errs {
                    err.emit(source);
                }
            }
            TyError::MutabilityNotAllowed(ty) => {
                if let Some(span) = ty.span {
                    let label = "mutability not allowed";
                    let (begin_line, begin_column) = source.get_line_col(span.begin);
                    let (_, end_column) = source.get_line_col(span.begin);
                    let snippet = error::single_line_snippet(
                        source,
                        label,
                        begin_line,
                        begin_column,
                        end_column,
                    );
                    eprintln!("{}", DisplayList::from(snippet).to_string());
                } else {
                    eprintln!("{:?}", &self);
                };
            }
            TyError::String(str) => {
                let snippet = Snippet {
                    title: Some(Annotation {
                        id: None,
                        label: Some(str),
                        annotation_type: AnnotationType::Error,
                    }),
                    footer: vec![],
                    slices: vec![Slice {
                        source: "",
                        line_start: 0,
                        origin: None,
                        annotations: vec![],
                        fold: false,
                    }],
                    opt: default_format(),
                };
                eprintln!("{}", DisplayList::from(snippet).to_string());
            }
            TyError::CtxError(CtxError::IdentNotFound(ident)) => {
                if let Some(span) = ident.span {
                    let label = "identifier not found in context";
                    let (begin_line, begin_column) = source.get_line_col(span.begin);
                    let (end_line, end_column) = source.get_line_col(span.end);
                    if begin_line != end_line {
                        panic!("an identifier can't span multiple lines")
                    }
                    let snippet = error::single_line_snippet(
                        source,
                        label,
                        begin_line,
                        begin_column,
                        end_column,
                    );
                    eprintln!("{}", DisplayList::from(snippet).to_string());
                } else {
                    eprintln!("{:?}", &self);
                };
            }
            TyError::ConflictingBorrow(pl_expr, _own, conflict) => {
                if let Some(pl_expr_span) = pl_expr.span {
                    match conflict {
                        BorrowingError::BorrowNotInReborrowList(place) => {
                            let label = "cannot borrow";
                            let (begin_line, begin_column) =
                                source.get_line_col(pl_expr_span.begin);
                            let (_, end_column) = source.get_line_col(pl_expr_span.end);
                            let snippet = error::single_line_snippet(
                                source,
                                label,
                                begin_line,
                                begin_column,
                                end_column,
                            );
                            eprintln!("{}", DisplayList::from(snippet).to_string());
                            eprintln!("conflicting with {:?}", place);
                        }
                        BorrowingError::TemporaryConflictingBorrow(_prv) => {
                            eprintln!("{:?}", conflict)
                        }
                        BorrowingError::ConflictingOwnership => eprintln!("{:?}", conflict),
                        BorrowingError::CtxError(ctx_err) => eprintln!("{:?}", ctx_err),
                        BorrowingError::TyError(ty_err) => {
                            ty_err.emit(source);
                        }
                    }
                }
            }
            err => {
                eprintln!("{:?}", err);
            }
        };
        ErrorReported
    }
}

impl From<CtxError> for TyError {
    fn from(err: CtxError) -> Self {
        TyError::CtxError(err)
    }
}
impl From<SubTyError> for TyError {
    fn from(err: SubTyError) -> Self {
        TyError::SubTyError(err)
    }
}

#[must_use]
#[derive(Debug)]
pub enum SubTyError {
    CtxError(CtxError),
    // format!("{} lives longer than {}.", shorter, longer)
    NotOutliving(String, String),
    // format!("No loans bound to provenance.")
    PrvNotUsedInBorrow(String),
    // TODO remove asap
    Dummy,
}

#[must_use]
#[derive(Debug)]
pub enum CtxError {
    //format!("Identifier: {} not found in context.", ident)),
    IdentNotFound(Ident),
    //"Cannot find identifier {} in kinding context",
    KindedIdentNotFound(Ident),
    // "Typing Context is missing the provenance value {}",
    PrvValueNotFound(String),
    // format!("{} is not declared", prv_rel.longer));
    PrvIdentNotFound(Ident),
    // format!("{} is not defined as outliving {}.", l, s)
    OutlRelNotDefined(Ident, Ident),
}

impl From<CtxError> for SubTyError {
    fn from(err: CtxError) -> Self {
        SubTyError::CtxError(err)
    }
}

#[must_use]
#[derive(Debug)]
pub enum BorrowingError {
    CtxError(CtxError),
    // "Trying to use place expression with {} capability while it refers to a \
    //     loan with {} capability.",
    // checked_own, ref_own
    ConflictingOwnership,
    // The borrowing place is not in the reborrow list
    BorrowNotInReborrowList(Place),
    TemporaryConflictingBorrow(String),
    TyError(Box<TyError>),
}

impl From<TyError> for BorrowingError {
    fn from(err: TyError) -> Self {
        BorrowingError::TyError(Box::new(err))
    }
}
impl From<CtxError> for BorrowingError {
    fn from(err: CtxError) -> Self {
        BorrowingError::CtxError(err)
    }
}
