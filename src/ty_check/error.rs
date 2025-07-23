use super::Ty;
use crate::arena_ast::internal::Place;
use crate::arena_ast::printer::PrintState;
use crate::arena_ast::{BaseExec, DataTy, Expr, Ident, NatEvalError, Ownership, PlaceExpr, TyKind};
use crate::error;
use crate::error::{default_format, ErrorReported};
use crate::parser::SourceCode;
use annotate_snippets::display_list::DisplayList;
use annotate_snippets::snippet::{Annotation, AnnotationType, Slice, Snippet};

#[must_use]
#[derive(Debug)]
pub enum TyError<'a> {
    MultiError(Vec<TyError<'a>>),
    MutabilityNotAllowed(Ty<'a>),
    CtxError(CtxError<'a>),
    SubTyError(SubTyError<'a>),
    // Standard data type mismatch, expected type followed by actual type
    MismatchedDataTypes(DataTy<'a>, DataTy<'a>, Expr<'a>),
    // "Trying to violate existing borrow of {:?}.",
    // p1 under own1 is in conflict because of BorrowingError
    ConflictingBorrow(Box<PlaceExpr<'a>>, Ownership, BorrowingError<'a>),
    PrvValueAlreadyInUse(String),
    // No loan the reference points to has a type that fits the reference element type
    ReferenceToIncompatibleType,
    // ownership of reference and loan it refers to do not fit
    ReferenceToWrongOwnership,
    // This would mean that the reference points to nothing, e.g., because the value was moved
    // out from under the reference which is forbidden.
    ReferenceToDeadTy,
    // Assignment to a constant place expression.
    AssignToConst(PlaceExpr<'a>), //, Box<Expr>),
    // Assigning to a view is forbidden
    AssignToView,
    // Trying to split a non-view array.
    SplittingNonViewArray,
    // Expected a different type
    ExpectedTupleType(TyKind<'a>, PlaceExpr<'a>),
    // Trying to borrow uniquely but place is not mutable
    ConstBorrow(PlaceExpr<'a>),
    // The borrowed view type is at least paritally dead
    BorrowingDeadView,
    IllegalExec,
    // Trying to type an expression with dead type
    DeadTy,
    // When a parallel collection consits of other parallel elements, a for-with requires an
    // identifier for these elements.
    MissingParallelCollectionIdent,
    // If a provenance place holder is not substituted for a real provenance
    CouldNotInferProvenance,
    // The annotated or inferred type of the pattern does not fit the pattern.
    PatternAndTypeDoNotMatch,
    UnexpectedType,
    // The thread hierarchy dimension referred to does not exist
    IllegalDimension,
    UnifyError(UnifyError<'a>),
    MissingMain,
    NatEvalError(NatEvalError<'a>),
    CannotInferGenericArg(Ident<'a>),
    UnsafeRequired,
    // TODO remove as soon as possible
    String(String),
}

impl<'a> FromIterator<TyError<'a>> for TyError<'a> {
    fn from_iter<T: IntoIterator<Item = TyError<'a>>>(iter: T) -> Self {
        TyError::MultiError(iter.into_iter().collect())
    }
}

impl<'a> TyError<'a> {
    pub fn emit(&self, source: &'a SourceCode<'a>) -> ErrorReported {
        match &self {
            TyError::MultiError(errs) => {
                for err in errs {
                    err.emit(source);
                }
            }
            TyError::MismatchedDataTypes(expec, actual, actual_expr) => {
                let label = "mismatched types";
                let mut expec_printer = PrintState::new();
                expec_printer.print_dty(expec);
                let mut actual_printer = PrintState::new();
                actual_printer.print_dty(actual);
                let annotation = format!(
                    "expected `{}` but found `{}`",
                    expec_printer.get(),
                    actual_printer.get()
                );
                let expr_span = actual_expr.span.unwrap();
                let (begin_line, begin_column) = source.get_line_col(expr_span.begin);
                let (_, end_column) = source.get_line_col(expr_span.end);
                let snippet = error::single_line_snippet(
                    source,
                    label,
                    &annotation,
                    begin_line,
                    begin_column,
                    end_column,
                );
                eprintln!("{}", DisplayList::from(snippet));
            }
            TyError::MutabilityNotAllowed(ty) => {
                if let Some(span) = ty.span {
                    let label = "mutability not allowed";
                    let (begin_line, begin_column) = source.get_line_col(span.begin);
                    let (_, end_column) = source.get_line_col(span.begin);
                    let snippet = error::single_line_snippet(
                        source,
                        label,
                        label,
                        begin_line,
                        begin_column,
                        end_column,
                    );
                    eprintln!("{}", DisplayList::from(snippet));
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
                eprintln!("{}", DisplayList::from(snippet));
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
                        label,
                        begin_line,
                        begin_column,
                        end_column,
                    );
                    eprintln!("{}", DisplayList::from(snippet));
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
                                label,
                                begin_line,
                                begin_column,
                                end_column,
                            );
                            eprintln!("{}", DisplayList::from(snippet));
                            eprintln!("conflicting with {:?}", place);
                        }
                        BorrowingError::TemporaryConflictingBorrow(_prv) => {
                            eprintln!("{:?}", conflict)
                        }
                        BorrowingError::ConflictingOwnership => eprintln!("{:?}", conflict),
                        BorrowingError::ConflictingAccess => eprintln!("{:?}", conflict),
                        BorrowingError::CtxError(ctx_err) => eprintln!("{:?}", ctx_err),
                        BorrowingError::WrongDevice(under, from) => {
                            eprintln!("error: wrong device\nunder:{:?}\nfrom:{:?}", under, from)
                        }

                        BorrowingError::CannotNarrow
                        | BorrowingError::Conflict { .. }
                        | BorrowingError::NatEvalError(_)
                        | BorrowingError::DivergingExec
                        | BorrowingError::MultipleDistribs => eprintln!("{:?}", conflict),
                        BorrowingError::TyError(ty_err) => {
                            ty_err.emit(source);
                        }
                    }
                } else {
                    eprintln!("Span was None: {:?}", self)
                }
            }
            TyError::ConstBorrow(p) => {
                eprintln!("const borrow: {:?}", p)
            }
            TyError::ExpectedTupleType(ty_kind, pl_expr) => {
                if let Some(pl_expr_span) = pl_expr.span {
                    let label = format!("expected tuple type but found `{:?}`", ty_kind);
                    let (begin_line, begin_column) = source.get_line_col(pl_expr_span.begin);
                    let (_, end_column) = source.get_line_col(pl_expr_span.end);
                    let snippet = error::single_line_snippet(
                        source,
                        &label,
                        &label,
                        begin_line,
                        begin_column,
                        end_column,
                    );
                    eprintln!("{}", DisplayList::from(snippet));
                } else {
                    eprintln!("{:?}", &self);
                };
            }
            err => {
                eprintln!("{:?}", err);
            }
        };
        ErrorReported
    }
}

impl<'a> From<CtxError<'a>> for TyError<'a> {
    fn from(err: CtxError<'a>) -> Self {
        TyError::CtxError(err)
    }
}
impl<'a> From<SubTyError<'a>> for TyError<'a> {
    fn from(err: SubTyError<'a>) -> Self {
        TyError::SubTyError(err)
    }
}
impl<'a> From<UnifyError<'a>> for TyError<'a> {
    fn from(err: UnifyError<'a>) -> Self {
        TyError::UnifyError(err)
    }
}
impl<'a> From<NatEvalError<'a>> for TyError<'a> {
    fn from(err: NatEvalError<'a>) -> Self {
        TyError::NatEvalError(err)
    }
}

#[must_use]
#[derive(Debug)]
pub enum SubTyError<'a> {
    CtxError(CtxError<'a>),
    // format!("{} lives longer than {}.", shorter, longer)
    NotOutliving(String, String),
    // format!("No loans bound to provenance.")
    PrvNotUsedInBorrow(String),
    // Subtyping checks fail if the memory kinds are not equal
    MemoryKindsNoMatch,
    // Subtyping checks fail if the ownership of supposedly subtyped references do not match
    OwnershipNoMatch,
    // TODO remove asap
    Dummy,
}

#[must_use]
#[derive(Debug)]
pub enum UnifyError<'a> {
    // Cannot unify the two terms
    CannotUnify,
    // A type variable has to be equal to a term that is referring to the same type variable
    InfiniteType,
    SubTyError(SubTyError<'a>),
}

impl<'a> From<SubTyError<'a>> for UnifyError<'a> {
    fn from(err: SubTyError<'a>) -> Self {
        UnifyError::SubTyError(err)
    }
}

#[must_use]
#[derive(Debug)]
pub enum CtxError<'a> {
    //format!("Identifier: {} not found in context.", ident)),
    IdentNotFound(Ident<'a>),
    //"Cannot find identifier {} in kinding context",
    KindedIdentNotFound(Ident<'a>),
    // "Typing Context is missing the provenance value {}",
    PrvValueNotFound(String),
    // format!("{} is not declared", prv_rel.longer));
    PrvIdentNotFound(Ident<'a>),
    // format!("{} is not de<'a>ined as outliving {}.", l, s)
    OutlRelNotDefined(Ident<'a>, Ident<'a>),
    // TODO move to TyError
    IllegalProjection,
}

impl<'a> From<CtxError<'a>> for SubTyError<'a> {
    fn from(err: CtxError<'a>) -> Self {
        SubTyError::CtxError(err)
    }
}

#[must_use]
#[derive(Debug)]
pub enum BorrowingError<'a> {
    Conflict {
        checked: PlaceExpr<'a>,
        existing: PlaceExpr<'a>,
    },
    CtxError(CtxError<'a>),
    // "Trying to use place expression with {} capability while it refers to a \
    //     loan with {} capability.",
    // checked_own, ref_own
    ConflictingOwnership,
    ConflictingAccess,
    // The borrowing place is not in the reborrow list
    BorrowNotInReborrowList(Place<'a>),
    TemporaryConflictingBorrow(String),
    WrongDevice(BaseExec<'a>, BaseExec<'a>),
    MultipleDistribs,
    CannotNarrow,
    DivergingExec,
    TyError(Box<TyError<'a>>),
    NatEvalError(NatEvalError<'a>),
}

impl<'a> From<TyError<'a>> for BorrowingError<'a> {
    fn from(err: TyError<'a>) -> Self {
        BorrowingError::TyError(Box::new(err))
    }
}
impl<'a> From<CtxError<'a>> for BorrowingError<'a> {
    fn from(err: CtxError<'a>) -> Self {
        BorrowingError::CtxError(err)
    }
}
impl<'a> From<NatEvalError<'a>> for BorrowingError<'a> {
    fn from(err: NatEvalError<'a>) -> Self {
        BorrowingError::NatEvalError(err)
    }
}
