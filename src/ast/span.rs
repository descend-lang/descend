//! Components for mapping between sources and AST nodes

#[derive(Clone, Copy, Debug)]
pub struct Span {
    pub begin: usize,
    pub end: usize,
}

impl Span {
    pub fn new(begin: usize, end: usize) -> Self {
        Self { begin, end }
    }
}
