use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

///! This Symbol Table interns Strings, takes ownership of them, and returns
///! a unique Symbol object. The Symbol has an Rc back to the String
///! stored inside the symbol table for reverse lookup and Display purposes.

#[cfg(feature = "serialize_ast")]
use serde::Serialize;

#[derive(Default, Debug)]
pub struct SymbolTable {
    table: HashMap<Rc<String>, Symbol>,
}

#[derive(Debug, Clone, Eq)]
pub struct Symbol(usize, Rc<str>);

impl SymbolTable {
    pub fn intern(&mut self, s: String) -> Symbol {
        let string = Rc::new(s);
        if let Some(sym) = self.table.get(&string) {
            return sym.clone();
        }

        let slice: Rc<str> = Rc::from(string.as_str());
        let sym = Symbol(self.table.len(), slice);
        self.table.insert(string, sym.clone());
        sym
    }

    pub fn intern_str(&mut self, s: &str) -> Symbol {
        self.intern(s.to_string())
    }
}

impl Symbol {
    pub fn as_str(&self) -> &str {
        self.1.as_ref()
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.1)
    }
}

/// Symbols are equal iff their index is equal.
///
/// It is not possible to directly compare symbols originating from different tables.
impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

/// Symbols may be compared to strings
impl PartialEq<str> for Symbol {
    fn eq(&self, other: &str) -> bool {
        self.1.as_ref() == other
    }
}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

/// For performance reasons, we hash on the index, not on the string.
/// If two symbols were interned in different symbol tables with different indices,
/// their equality and hash equality will be consistent but non-deterministic.
/// So you *must not* intermingle Symbols from different tables.
impl Hash for Symbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

#[cfg(feature = "serialize_ast")]
impl Serialize for Symbol {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.1.serialize(serializer)
    }
}
