

peg::parser!{
    pub grammar descent() for str {

        rule keyword() -> ()
        = 

        rule _() -> ()
            = quiet!{(
                [' '|'\n'|'\t'|'\r'] _) // 0 or more whitespaces
                / ("//" (!['\n'][_])* ['\n'] _) // Comment to EOL
                / ""}

        rule __() -> ()
            = quiet!{[' '|'\n'|'\t'|'\r'] _}
    }
}