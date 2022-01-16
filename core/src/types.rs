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

/// Stores a variable or function identifier.
///
/// During the initial parsing, identifiers are represented as ID::Name.
/// But during type analysis, identifiers are transformed into numeric IDs
/// with separate ID spaces for variables and functions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serialize_ast", derive(Serialize))]
pub enum ID {
    Name(String),
    VarId(usize),
    FuncId(usize),
    PubFuncId(String),
}

impl Display for ID {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ID::Name(name) | ID::PubFuncId(name) => {
                write!(f, "{}", name)
            }
            ID::VarId(id) | ID::FuncId(id) => {
                write!(f, "{}", id)
            }
        }
    }
}

impl ID {
    // unsafe accessors
    pub fn name(&self) -> &String {
        match self {
            ID::Name(name) | ID::PubFuncId(name) => name,
            _ => panic!("accessed textual ID on resolved numeric ID"),
        }
    }

    pub fn id(&self) -> usize {
        match self {
            ID::Name(_) => panic!("accessed numeric ID on unresolved textual ID"),
            ID::VarId(id) => *id,
            ID::FuncId(id) => *id,
            ID::PubFuncId(_) => panic!("accessed numeric ID on public function symbol"),
        }
    }
}
