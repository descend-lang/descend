use super::Ty;
use crate::ast::{Ident, Ownership, PlaceExpr};
use crate::error;
use crate::error::{default_format, ErrorReported};
use crate::parser::SourceCode;
use annotate_snippets::display_list::DisplayList;
use annotate_snippets::snippet::{Annotation, AnnotationType, Slice, Snippet};

#[must_use]
#[derive(Debug)]
pub struct TyError<'a> {
    err: TyErrorKind<'a>,
    source: &'a SourceCode<'a>,
}

#[derive(Debug)]
pub enum TyErrorKind<'a> {
    MultiError(Vec<TyError<'a>>),
    MutabilityNotAllowed(Ty),
    CtxError(CtxError),
    SubTyError(SubTyError),
    OwnError(OwnError),
    // TODO remove as soon as possible
    String(String),
}

impl<'a> std::iter::FromIterator<TyError<'a>> for TyError<'a> {
    fn from_iter<T: IntoIterator<Item = TyError<'a>>>(iter: T) -> Self {
        let mut iter = iter.into_iter().peekable();
        let source = iter
            .peek()
            .expect("Cannot create a MultiError from zero errors.")
            .source;
        // FIXME currently assumes that the sources for all errors are the same
        TyError::new(TyErrorKind::MultiError(iter.collect()), source)
    }
}

impl<'a> TyError<'a> {
    pub fn new(err: TyErrorKind<'a>, source: &'a SourceCode<'a>) -> Self {
        TyError { err, source }
    }

    pub fn emit(&self) -> ErrorReported {
        match &self.err {
            TyErrorKind::MultiError(errs) => {
                for err in errs {
                    err.emit();
                }
            }
            TyErrorKind::MutabilityNotAllowed(ty) => {
                if let Some(span) = ty.span {
                    let label = "mutability not allowed";
                    let (begin_line, begin_column) = self.source.get_line_col(span.start);
                    let (_, end_column) = self.source.get_line_col(span.start);
                    let snippet = error::single_line_snippet(
                        self.source,
                        label,
                        begin_line,
                        begin_column,
                        end_column,
                    );
                    println!("{}", DisplayList::from(snippet).to_string());
                } else {
                    println!("{:?}", &self.err);
                };
            }
            TyErrorKind::String(str) => {
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
                println!("{}", DisplayList::from(snippet).to_string());
            }
            TyErrorKind::CtxError(CtxError::IdentNotFound(ident)) => {
                if let Some(span) = ident.span {
                    let label = "identifier not found in context";
                    let (begin_line, begin_column) = self.source.get_line_col(span.start);
                    let (end_line, end_column) = self.source.get_line_col(span.end);
                    if begin_line != end_line {
                        panic!("an identifier can't span multiple lines")
                    }
                    let snippet = error::single_line_snippet(
                        self.source,
                        label,
                        begin_line,
                        begin_column,
                        end_column,
                    );
                    println!("{}", DisplayList::from(snippet).to_string());
                } else {
                    println!("{:?}", &self.err);
                };
            }
            err => {
                println!("{:?}", err);
            }
        };
        ErrorReported
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
pub enum OwnError {
    CtxError(CtxError),
    // "Trying to violate existing borrow of {:?}.",
    ConflictingBorrow(PlaceExpr, Ownership),
    // "Trying to use place expression with {} capability while it refers to a \
    //     loan with {} capability.",
    // checked_own, ref_own
    ConflictingOwnership(Ownership, Ownership),
}

impl From<CtxError> for OwnError {
    fn from(err: CtxError) -> Self {
        OwnError::CtxError(err)
    }
}
