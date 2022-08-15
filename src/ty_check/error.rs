use super::Ty;
use crate::ast::internal::Place;
use crate::ast::{
    AssociatedItem, Constraint, DataTy, FunctionName, Ident, Kind, Ownership, PlaceExpr, TyKind,
    TypeScheme,
};
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
    // Assignment to a constant place expression.
    AssignToConst(PlaceExpr), //, Box<Expr>),
    // Assigning to a view is forbidden
    AssignToView,
    // Trying to split a non-view array.
    SplittingNonViewArray,
    // Expected a different type
    ExpectedTupleType(TyKind, PlaceExpr),
    // Trying to borrow uniquely but place is not mutable
    ConstBorrow(PlaceExpr),
    // The borrowed view type is at least paritally dead
    BorrowingDeadView,
    IllegalExec,
    // A type variable has to be equal to a term that is referring to the same type variable
    InfiniteType,
    // Cannot unify the two terms
    CannotUnify,
    // Trying to type an expression with dead type
    DeadTy,
    // When a parallel collection consits of other parallel elements, a for-with requires an
    // identifier for these elements.
    MissingParallelCollectionIdent,
    // If a provenance place holder is not substituted for a real provenance
    CouldNotInferProvenance,
    // The annotated or inferred type of the pattern does not fit the pattern.
    PatternAndTypeDoNotMatch,
    UnexpectedTypeKind {
        expected_name: String,
        found: Ty,
    },
    UnexpectedDataTypeKind {
        expected_name: String,
        found: DataTy,
    },
    UnexpectedType {
        expected: Ty,
        found: Ty,
    },
    UnexpectedAssItemInImpl(AssociatedItem),
    WrongNumberOfGenericParams {
        expected: usize,
        found: usize,
    },
    MissingStructField {
        missing_field: String,
        struct_name: String,
    },
    UnexpectedStructField {
        unexpected_field: String,
        struct_name: String,
    },
    WrongKind {
        expected: Kind,
        found: Kind,
    },
    UnfullfilledConstraint(Constraint),
    IllegalProjection(String),
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
                    let (end_line, end_column) = source.get_line_col(pl_expr_span.end);
                    let snippet = error::single_line_snippet(
                        source,
                        &label,
                        begin_line,
                        begin_column,
                        end_column,
                    );
                    eprintln!("{}", DisplayList::from(snippet).to_string());
                } else {
                    eprintln!("{:?}", &self);
                };
            }
            TyError::UnexpectedTypeKind {
                expected_name,
                found,
            } => {
                eprintln!(
                    "Found unexpected type. Expected {}, found {:#?}.",
                    expected_name, found
                );
            }
            TyError::UnexpectedDataTypeKind {
                expected_name,
                found,
            } => {
                eprintln!(
                    "Found unexpected data type. Expected {}, found {:#?}.",
                    expected_name, found
                );
            }
            TyError::UnexpectedAssItemInImpl(item) => {
                eprintln!("Found unexpected item in impl: {:#?}.", item);
            }
            TyError::UnexpectedType { expected, found } => {
                eprintln!(
                    "Found unexpected type. Expected {:#?}, found {:#?}.",
                    expected, found
                );
            }
            TyError::WrongNumberOfGenericParams { expected, found } => {
                eprintln!(
                    "Wrong amount of generic arguments. Expected {}, found {}.",
                    expected, found
                );
            }
            TyError::MissingStructField {
                missing_field,
                struct_name,
            } => {
                eprintln!(
                    "Could not find struct_field \"{}\" in struct instantiation of struct \"{}\".",
                    missing_field, struct_name
                );
            }
            TyError::UnexpectedStructField {
                unexpected_field: unexpected_filed,
                struct_name,
            } => {
                eprintln!(
                    "Found unexpected struct_field \"{}\" in struct instantiation of struct \"{}\".",
                    unexpected_filed, struct_name
                );
            }
            TyError::WrongKind { expected, found } => {
                eprintln!(
                    "Wrong Kind. Expected: \"{}\" Found: \"{}\"",
                    expected, found
                );
            }
            TyError::UnfullfilledConstraint(con) => {
                eprintln!("Constraint \"{:#?}\" is not fulfilled.", con)
            }
            TyError::CtxError(ctx_error) => {
                eprintln!("CtxError {}", ctx_error)
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
    // Subtyping checks fail if the memory kinds are not equal
    MemoryKindsNoMatch,
    // TODO remove asap
    Dummy,
}

#[must_use]
#[derive(Debug)]
pub enum CtxError {
    //format!("Identifier: {} not found in context.", ident)),
    IdentNotFound(Ident),
    TraitNotFound(String),
    StructNotFound(String),
    //"Cannot find identifier {} in kinding context",
    KindedIdentNotFound(Ident),
    // "Typing Context is missing the provenance value {}",
    PrvValueNotFound(String),
    // format!("{} is not declared", prv_rel.longer));
    PrvIdentNotFound(Ident),
    // format!("{} is not defined as outliving {}.", l, s)
    OutlRelNotDefined(Ident, Ident),
    // Multiple defined objects
    MultipleDefinedFunctions(FunctionName),
    MultipleDefinedItems(String),
    MultipleDefinedStructs(String),
    MultipleDefinedTraits(String),
    MultipleDefinedImplsForTrait {
        trait_name: String,
        impl_dty: TypeScheme,
    },
    // If there the function which should be called is ambiguous
    AmbiguousFunctionCall {
        function_name: String,
        impl_dty: DataTy,
    },
    FunNotImplemented {
        function_name: String,
        trait_name: String,
        impl_dty: TypeScheme,
    },
}

impl std::fmt::Display for CtxError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            CtxError::IdentNotFound(ident) => {
                write!(f, "Identifier \"{}\" not found in context.", ident)
            }
            CtxError::TraitNotFound(trait_name) => {
                write!(f, "Trait \"{}\" not found in context.", trait_name)
            }
            CtxError::StructNotFound(struct_name) => {
                write!(f, "Struct \"{}\" not found in context.", struct_name)
            }
            CtxError::KindedIdentNotFound(ident) => {
                write!(
                    f,
                    "Cannot find identifier \"{}\" in kinding context.",
                    ident
                )
            }
            CtxError::PrvValueNotFound(prov) => {
                write!(
                    f,
                    "Typing Context is missing the provenance value \"{}\".",
                    prov
                )
            }
            CtxError::PrvIdentNotFound(prov) => {
                write!(f, "Provenance ident \"{}\" not found in context.", prov)
            }
            CtxError::OutlRelNotDefined(l, s) => {
                write!(f, "\"{}\" is not defined as outliving {}.", l, s)
            }
            CtxError::MultipleDefinedFunctions(fun_name) => {
                write!(
                    f,
                    "Found multiple definitions of function \"{:#?}\".",
                    fun_name
                )
            }
            CtxError::MultipleDefinedItems(item_name) => {
                write!(f, "Found multiple definitions of \"{}\".", item_name)
            }
            CtxError::MultipleDefinedStructs(struct_name) => {
                write!(
                    f,
                    "Found multiple definitions of trait \"{}\".",
                    struct_name
                )
            }
            CtxError::MultipleDefinedTraits(trait_name) => {
                write!(f, "Found multiple definitions of trait \"{}\".", trait_name)
            }
            CtxError::MultipleDefinedImplsForTrait {
                trait_name,
                impl_dty,
            } => {
                write!(
                    f,
                    "Found multiple implmentations of trait \"{}\" for impl_dty \"{:#?}\".",
                    trait_name, impl_dty
                )
            }
            CtxError::AmbiguousFunctionCall {
                function_name,
                impl_dty,
            } => {
                write!(
                    f,
                    "Function call of function \"{}\" for impl_dty \"{:#?}\" is ambiguous.",
                    function_name, impl_dty
                )
            }
            CtxError::FunNotImplemented {
                function_name,
                trait_name,
                impl_dty,
            } => {
                write!(
                    f,
                    "impl \"{:#?}\" for trait \"{}\" did not implement function \"{}\".",
                    impl_dty, trait_name, function_name
                )
            }
        }
    }
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
