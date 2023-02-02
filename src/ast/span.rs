//! Components for mapping between sources and AST nodes

// Can deal with a source file of up to 4 GiB
// Before, this was storing a begin and end position with 64 bits each. The 16 Bytes are too large
// and not necessary. Span is used extensively and the new size of 8 bytes is much more suitable.
#[derive(Clone, Copy, Debug)]
pub struct Span {
    pub begin: u32,
    // TODO optimize space? by: change to offset from begin which enables u16 or u8 for the offset
    //  and is still a realistic span
    pub end: u32,
}

impl Span {
    pub fn new(begin: usize, end: usize) -> Self {
        Self {
            begin: u32::try_from(begin).expect("The input source string is unexpectedly large."),
            end: u32::try_from(end).expect("The input source string is unexpectedly large."),
        }
    }
}
