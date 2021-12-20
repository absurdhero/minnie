use crate::grammar;
use lalrpop_util::lexer::Token;

#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    Number(String),
    Bool(bool),
    Negate(Box<Expr>),
    Op(Box<Expr>, Opcode, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Sequence(Vec<Expr>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Opcode {
    Mul,
    Div,
    Add,
    Sub,
}

pub type ParseError<'input> = lalrpop_util::ParseError<usize, Token<'input>, &'static str>;

pub fn parse(program: &str) -> Result<Box<Expr>, ParseError> {
    let parser = grammar::ExprParser::new();
    parser.parse(program)
}

#[cfg(test)]
mod tests {
    use crate::ast::Expr;

    macro_rules! parse_ok {
        ($s:literal) => {
            assert!(crate::grammar::ExprParser::new().parse($s).is_ok())
        };
    }

    macro_rules! parse_fails {
        ($s:literal) => {
            assert!(crate::grammar::ExprParser::new().parse($s).is_err())
        };
    }

    macro_rules! parses {
        ($($lhs:expr => $rhs:expr)+) => {{
             $(
                assert_eq!(Ok($rhs), crate::grammar::ExprParser::new().parse($lhs).map(|b| *b));
             )+
        }};
    }

    #[test]
    fn numeric_operations() {
        parses! {
            "22" => Expr::Number("22".to_string())
            "(22)" => Expr::Number("22".to_string())
            "(((22)))" => Expr::Number("22".to_string())
        };
        parse_fails!("((22)");

        parse_ok!("1+2");
        parse_ok!("1-2");
        parse_ok!("1 * 2");
        parse_ok!("1 / 3");
        parse_ok!("1 + 2 * 3");

        // unary minus
        parse_ok!("-2");
        parse_ok!("4 * -2");
        parse_ok!("-(1+2)");
        parse_ok!("-(-(-1))");
        parse_ok!("3--2");
    }

    #[test]
    fn conditionals() {
        parses! {
            "true" => Expr::Bool(true)
            "false" => Expr::Bool(false)
            "if true { 1 } else { 2 }" => Expr::If(
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Sequence(vec![Expr::Number("1".to_string())])),
                Box::new(Expr::Sequence(vec![Expr::Number("2".to_string())])),
            )
            "if true { 0;1 } else { 2 }" => Expr::If(
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Sequence(vec![Expr::Number("0".to_string()),
                                             Expr::Number("1".to_string())])),
                Box::new(Expr::Sequence(vec![Expr::Number("2".to_string())])),
            )
        };
        // braces required
        parse_fails!("if true 1 else 0");
        // empty braces not allowed
        parse_fails!("if true {} else {0}");
    }
}
