//! Source file representation

use crate::error::{ErrorReported, FileIOError};

#[derive(PartialEq, Eq, Debug)]
pub struct SourceCode<'a> {
    /// Path to the file containing the source code
    pub file_path: Option<&'a str>,
    /// UTF-8 encoded source code
    source: String,
    /// Offsets of the beginning of each line of code
    line_offsets: Vec<u32>,
}

impl<'a> SourceCode<'a> {
    /// Read source code from file
    pub fn from_file(path: &'a str) -> Result<Self, ErrorReported> {
        let bytes =
            std::fs::read(path).map_err(|io_error| FileIOError::new(path, io_error).emit())?;
        let source = String::from_utf8_lossy(&bytes).to_string();
        Ok(Self {
            line_offsets: Self::line_offsets(&source),
            source,
            file_path: Some(path),
        })
    }

    /// Create new source file
    pub fn new(source: String) -> Self {
        Self {
            line_offsets: Self::line_offsets(&source),
            source,
            file_path: None,
        }
    }

    fn line_offsets(source: &str) -> Vec<u32> {
        source
            .split('\n')
            .scan(0, |offset, line| {
                let old_offset = *offset;
                *offset += u32::try_from(line.len()).unwrap() + 1;
                Some(old_offset)
            })
            .collect()
    }

    /// Returns a reference to the source string
    pub fn str(&self) -> &str {
        &self.source
    }

    /// Returns a slice of the source string containing the line with (0-based) line number `num`
    /// or None for EOF
    pub fn get_line(&self, num: u32) -> Option<&str> {
        let num = num as usize;
        let begin_line = self.line_offsets[num] as usize;
        if let Some(next_line_offset) = self.line_offsets.get(num + 1) {
            let end_line = (next_line_offset - 1) as usize;
            Some(&self.source[begin_line..end_line])
        } else {
            None
        }
    }

    /// Get line and column (both 0-based) corresponding to an offset in the
    /// source string
    pub fn get_line_col(&self, offset: u32) -> (u32, u32) {
        if offset
            > u32::try_from(self.source.len())
                .expect("The input source string is unexpectedly large.")
        {
            panic!("offset larger than source code string")
        }
        let mut line_num = 1;
        let mut line_off = 0;
        for (i, line_offset) in self.line_offsets.iter().enumerate().rev() {
            if *line_offset <= offset {
                line_num = u32::try_from(i).unwrap();
                line_off = *line_offset;
                break;
            }
        }
        let col_num = offset - line_off;
        (line_num, col_num)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extract_line_by_number() {
        let src = SourceCode::new(String::from("first\nsecond\nthird"));
        assert_eq!(
            src.get_line(1),
            Some("second"),
            "Expected str slice to second line, but found something different."
        );
    }

    #[test]
    fn empty() {
        let src = String::from("");
        let src_file = SourceCode::new(src.clone());
        assert_eq!(
            src_file,
            SourceCode {
                source: src,
                file_path: None,
                line_offsets: vec![0]
            },
            "cannot handle empty source file"
        );
        assert_eq!(
            src_file.get_line_col(0),
            (0, 0),
            "cannot get line and column in empty source file"
        );
    }

    #[test]
    fn one_line() {
        let src = String::from("one line string");
        let src_file = SourceCode::new(src.clone());
        assert_eq!(
            src_file,
            SourceCode {
                source: src,
                file_path: None,
                line_offsets: vec![0]
            },
            "cannot handle one line source file"
        );
        assert_eq!(
            src_file.get_line_col(4),
            (0, 4),
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
        let src_file = SourceCode::new(src.clone());
        assert_eq!(
            src_file,
            SourceCode {
                source: src,
                file_path: None,
                line_offsets: vec![0, 7, 14, 20]
            },
            "cannot handle multi line source file"
        );
        assert_eq!(
            src_file.get_line_col(0),
            (0, 0),
            "cannot get line and column in multi line source file (offset 0)"
        );
        assert_eq!(
            src_file.get_line_col(8),
            (1, 1),
            "cannot get line and column in multi line source file (offset 8)"
        );
        assert_eq!(
            src_file.get_line_col(15),
            (2, 1),
            "cannot get line and column in multi line source file (offset 15)"
        );
        assert_eq!(
            src_file.get_line_col(22),
            (3, 2),
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
        let src_file = SourceCode::new(src.clone());
        assert_eq!(
            src_file,
            SourceCode {
                source: src,
                file_path: None,
                line_offsets: vec![0, 7, 8, 14]
            },
            "cannot handle multi line source file with empty lines"
        );
        assert_eq!(
            src_file.get_line_col(0),
            (0, 0),
            "cannot get line and column in multi line source file with empty lines (offset 0)"
        );
        assert_eq!(
            src_file.get_line_col(7),
            (1, 0),
            "cannot get line and column multi line source file with empty lines (offset 7)"
        );
        assert_eq!(
            src_file.get_line_col(9),
            (2, 1),
            "cannot get line and column multi line source file with empty lines (offset 9)"
        );
        assert_eq!(
            src_file.get_line_col(14),
            (3, 0),
            "cannot get line and column imulti line source file with empty lines (offset 14)"
        );
    }
}
