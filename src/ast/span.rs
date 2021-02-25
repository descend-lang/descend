//! Components for mapping between sources and AST nodes

#[derive(Clone, Copy, Debug)]
pub struct Span {
    start: usize,
    end: usize
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
}