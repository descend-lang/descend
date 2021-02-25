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
    
    pub fn get_span_position(&self, text: &str) -> (usize, usize){
        let mut line_count = 1;
        let mut column_count = 0;
        let bytes = text.as_bytes();
        for (i, &letter) in bytes.iter().enumerate(){
            if letter == b'\n' {
                line_count = line_count + 1;
                column_count = 1;
            } else {
                column_count = column_count + 1;
            }
            if i >= self.start {
                return (line_count, column_count);
            }
        }
        (line_count, column_count)
    }
}