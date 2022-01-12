/// Types supported by the language
#[derive(Clone, Debug, PartialEq, Eq)]
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
pub enum ID {
    Name(String),
    VarId(usize),
    FuncId(usize),
}

impl ID {
    // unsafe accessors used in their corresponding AST phases.
    pub fn name(&self) -> &String {
        if let ID::Name(name) = self {
            name
        } else {
            panic!("accessed textual ID on resolved numeric ID");
        }
    }
    pub fn id(&self) -> usize {
        match self {
            ID::Name(_) => panic!("accessed numeric ID on unresolved textual ID"),
            ID::VarId(id) => *id,
            ID::FuncId(id) => *id,
        }
    }
}
