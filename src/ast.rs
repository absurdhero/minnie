use crate::grammar;
use lalrpop_util::lexer::Token;

pub enum Expr {
    Number(i32),
    Op(Box<Expr>, Opcode, Box<Expr>),
}

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

#[test]
fn numeric_operations() {
    assert!(grammar::ExprParser::new().parse("22").is_ok());
    assert!(grammar::ExprParser::new().parse("(22)").is_ok());
    assert!(grammar::ExprParser::new().parse("((((22))))").is_ok());
    assert!(grammar::ExprParser::new().parse("((22)").is_err());

    assert!(grammar::ExprParser::new().parse("1+2").is_ok());
    assert!(grammar::ExprParser::new().parse("1 * 2").is_ok());
    assert!(grammar::ExprParser::new().parse("1 + 2 * 3").is_ok());
}
