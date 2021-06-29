//! Source file representation

use peg::{error::ParseError, str::LineCol};

use crate::ast::FunDef;

use super::parse_unit;

#[derive(PartialEq, Eq, Debug)]
pub struct SourceFile {
    /// UTF-8 encoded source code
    src: String,
    /// Offsets of each line of code
    line_offsets: Vec<usize>,
}

impl SourceFile {
    /// Create new source file
    pub fn new(src: String) -> Self {
        // Generate line offsets
        let line_offsets = src
            .split("\n")
            .scan(0, |offset, line| {
                let old_offset = *offset;
                *offset += line.len() + 1;
                Some(old_offset)
            })
            .collect::<Vec<_>>();
        Self { src, line_offsets }
    }

    /// Get line and column (both 1-based) corresponding to an offset in the
    /// source string
    pub fn get_line_col(&self, offset: usize) -> Option<(usize, usize)> {
        if offset > self.src.len() {
            return None;
        }
        let mut line_num = 1;
        let mut line_off = 0;
        for (i, line_offset) in self.line_offsets.iter().enumerate().rev() {
            if *line_offset <= offset {
                line_num = i + 1;
                line_off = *line_offset;
                break;
            }
        }
        let col_num = offset - line_off + 1;
        Some((line_num, col_num))
    }

    pub fn parse_unit(&self) -> Result<Vec<FunDef>, ParseError<LineCol>> {
        parse_unit(&self.src)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        let src = String::from("");
        let src_file = SourceFile::new(src.clone());
        assert_eq!(
            src_file,
            SourceFile {
                src,
                line_offsets: vec![0]
            },
            "cannot handle empty source file"
        );
        assert_eq!(
            src_file.get_line_col(0),
            Some((1, 1)),
            "cannot get line and column in empty source file"
        );
    }

    #[test]
    fn one_line() {
        let src = String::from("one line string");
        let src_file = SourceFile::new(src.clone());
        assert_eq!(
            src_file,
            SourceFile {
                src,
                line_offsets: vec![0]
            },
            "cannot handle one line source file"
        );
        assert_eq!(
            src_file.get_line_col(4),
            Some((1, 5)),
            "cannot get line and column in one line source file"
        );
        assert_eq!(
            src_file.get_line_col(100),
            None,
            "cannot get line and column in one line source file"
        );
    }

    #[test]
    fn multi_line() {
        let src = String::from(
            r#"first,
second
third
end"#,
        );
        let src_file = SourceFile::new(src.clone());
        assert_eq!(
            src_file,
            SourceFile {
                src,
                line_offsets: vec![0, 7, 14, 20]
            },
            "cannot handle multi line source file"
        );
        assert_eq!(
            src_file.get_line_col(0),
            Some((1, 1)),
            "cannot get line and column in multi line source file (offset 0)"
        );
        assert_eq!(
            src_file.get_line_col(8),
            Some((2, 2)),
            "cannot get line and column in multi line source file (offset 8)"
        );
        assert_eq!(
            src_file.get_line_col(15),
            Some((3, 2)),
            "cannot get line and column in multi line source file (offset 15)"
        );
        assert_eq!(
            src_file.get_line_col(22),
            Some((4, 3)),
            "cannot get line and column in multi line source file (offset 22)"
        );
    }

    #[test]
    fn empty_lines() {
        let src = String::from(
            r#"first,

third
"#,
        );
        let src_file = SourceFile::new(src.clone());
        assert_eq!(
            src_file,
            SourceFile {
                src,
                line_offsets: vec![0, 7, 8, 14]
            },
            "cannot handle multi line source file with empty lines"
        );
        assert_eq!(
            src_file.get_line_col(0),
            Some((1, 1)),
            "cannot get line and column in multi line source file with empty lines (offset 0)"
        );
        assert_eq!(
            src_file.get_line_col(7),
            Some((2, 1)),
            "cannot get line and column multi line source file with empty lines (offset 7)"
        );
        assert_eq!(
            src_file.get_line_col(9),
            Some((3, 2)),
            "cannot get line and column multi line source file with empty lines (offset 9)"
        );
        assert_eq!(
            src_file.get_line_col(14),
            Some((4, 1)),
            "cannot get line and column imulti line source file with empty lines (offset 14)"
        );
    }
}
