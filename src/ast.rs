use crate::grammar;
use lalrpop_util::lexer::Token;
use thiserror::Error;

pub type ParseError<'input> = lalrpop_util::ParseError<usize, Token<'input>, SyntaxError>;

#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum SyntaxError {
    #[error("type mismatch (expected {expected:?}, found {found:?})")]
    TypeError { expected: Type, found: Type },
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExprKind {
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

/// Types supported by the language
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    Int64,
    Bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Type,
}

impl Expr {
    pub fn new(expr: ExprKind) -> Result<Box<Expr>, ParseError<'static>> {
        expr.into()
            .map(Box::new)
            .map_err(|e| ParseError::User { error: e })
    }
}

impl ExprKind {
    pub fn into(self) -> Result<Expr, SyntaxError> {
        let ty = self.infer_type()?;
        Ok(Expr { kind: self, ty })
    }

    pub fn infer_type(&self) -> Result<Type, SyntaxError> {
        match self {
            ExprKind::Number(_) => Ok(Type::Int64),
            ExprKind::Bool(_) => Ok(Type::Bool),
            ExprKind::Negate(e) => {
                if let Expr {
                    kind: _,
                    ty: Type::Int64,
                } = **e
                {
                    Ok(Type::Int64)
                } else {
                    Err(type_error(Type::Int64, e))
                }
            }
            ExprKind::Op(e1, _, e2) => {
                if (e1.ty == Type::Int64) && (e2.ty == Type::Int64) {
                    Ok(e1.ty)
                } else {
                    Err(type_error(Type::Int64, e1))
                }
            }
            ExprKind::If(c, t, f) => {
                if c.ty != Type::Bool {
                    Err(type_error(Type::Bool, c))
                } else if t.ty == f.ty {
                    Ok(t.ty)
                } else {
                    Err(type_error(Type::Int64, f))
                }
            }
            ExprKind::Sequence(v) => Ok(v[v.len() - 1].ty),
        }
    }
}

fn type_error(expected: Type, found: &Expr) -> SyntaxError {
    SyntaxError::TypeError {
        expected,
        found: found.ty,
    }
    //ParseError::User { error: "type error" }
}

pub fn parse(program: &str) -> Result<Box<Expr>, ParseError> {
    let parser = grammar::ExprParser::new();
    parser.parse(program)
}

#[cfg(test)]
mod tests {
    use crate::ast::{Expr, ExprKind};

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
                assert_eq!(Ok($rhs), crate::grammar::ExprParser::new().parse($lhs).map(|b| b.kind));
             )+
        }};
    }

    #[test]
    fn numeric_operations() {
        parses! {
            "22" => ExprKind::Number("22".to_string())
            "(22)" => ExprKind::Number("22".to_string())
            "(((22)))" => ExprKind::Number("22".to_string())
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
            "true" => ExprKind::Bool(true)
            "false" => ExprKind::Bool(false)
            "if true { 1 } else { 2 }" => ExprKind::If(
                Expr::new(ExprKind::Bool(true)).unwrap(),
                Expr::new(ExprKind::Sequence(vec![ExprKind::Number("1".to_string()).into().unwrap()])).unwrap(),
                Expr::new(ExprKind::Sequence(vec![ExprKind::Number("2".to_string()).into().unwrap()])).unwrap(),
            )
            "if true { true;1 } else { 2 }" => ExprKind::If(
                Expr::new(ExprKind::Bool(true)).unwrap(),
                Expr::new(ExprKind::Sequence(vec![ExprKind::Bool(true).into().unwrap(),
                                                  ExprKind::Number("1".to_string()).into().unwrap()])).unwrap(),
                Expr::new(ExprKind::Sequence(vec![ExprKind::Number("2".to_string()).into().unwrap()])).unwrap(),
            )
        };

        // braces required
        parse_fails!("if true 1 else 0");
        // empty braces not allowed
        parse_fails!("if true {} else {0}");

        parse_ok!("if true {false} else {true}");
    }

    #[test]
    fn immediate_type_errors() {
        // `if` arms must match
        parse_fails!("if true {false} else {0}");
        parse_fails!("if true {1} else {true}");

        // math operators only accept numbers
        parse_fails!("true + 1");
        parse_fails!("1 + true");
        parse_fails!("true + true");
    }
}
