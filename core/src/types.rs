use crate::symbols::Symbol;
use itertools::Itertools;
use std::fmt::{Display, Formatter};

#[cfg(feature = "serialize_ast")]
use serde::Serialize;

/// Types supported by the language
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub enum Type {
    // Primitive Types
    Int64,
    Bool,
    Void,

    // Compound Types
    Function {
        params: Vec<Type>,
        returns: Box<Type>,
    },

    // can only exist in an AST that contains type errors
    Unknown,
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int64 => write!(f, "int"),
            Type::Bool => write!(f, "bool"),
            Type::Void => write!(f, "()"),
            Type::Function { params, returns } => {
                write!(
                    f,
                    "fn({}) -> {}",
                    params.iter().map(|t| t.to_string()).join(", "),
                    returns
                )
            }
            Type::Unknown => write!(f, "unknown"),
        }
    }
}

/// Stores a variable or function identifier.
///
/// During the initial parsing, identifiers are represented as `ID::Symbol`.
/// But during type analysis, identifiers are transformed into numeric IDs
/// with separate ID spaces for variables and functions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub enum ID {
    Symbol(Symbol),
    VarId(usize),
    FuncId(usize),
    PubFuncId(Symbol),
}

impl Display for ID {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ID::Symbol(symbol) | ID::PubFuncId(symbol) => {
                write!(f, "{}", symbol.as_str())
            }
            ID::VarId(id) | ID::FuncId(id) => {
                write!(f, "{}", id)
            }
        }
    }
}

impl ID {
    // unsafe accessors
    pub fn symbol(&self) -> &Symbol {
        match self {
            ID::Symbol(name) | ID::PubFuncId(name) => name,
            _ => panic!("accessed textual ID on resolved numeric ID"),
        }
    }

    pub fn id(&self) -> usize {
        match self {
            ID::VarId(id) | ID::FuncId(id) => *id,
            ID::Symbol(_) => panic!("accessed numeric ID on unresolved textual ID"),
            ID::PubFuncId(_) => panic!("accessed numeric ID on public function symbol"),
        }
    }
}
