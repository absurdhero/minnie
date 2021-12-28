use core::fmt;
use std::fmt::Formatter;
use std::ops::{Deref, Range};

///! Attach start and end locations to some data.
///! Provides conversions from tuples and ranges.

#[derive(Debug)]
pub struct Span<T> {
    pub start: usize,
    pub end: usize,
    pub item: T,
}

/// Spans can be treated as ranges e.g. when slicing into an input string
impl<T> From<Span<T>> for Range<usize> {
    fn from(span: Span<T>) -> Self {
        span.start..span.end
    }
}

impl<T> From<&Span<T>> for Range<usize> {
    fn from(span: &Span<T>) -> Self {
        span.start..span.end
    }
}

/// If T can be cloned, so can its Span
impl<T> Clone for Span<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Span {
            start: self.start,
            end: self.end,
            item: self.item.clone(),
        }
    }
}

/// Construct a span from a range and object
impl<T> From<(Range<usize>, T)> for Span<T> {
    fn from(t: (Range<usize>, T)) -> Self {
        Span {
            start: t.0.start,
            end: t.0.end,
            item: t.1,
        }
    }
}

/// Construct a span from a tuple of its three components
impl<T> From<(usize, T, usize)> for Span<T> {
    fn from(t: (usize, T, usize)) -> Self {
        Span {
            start: t.0,
            end: t.2,
            item: t.1,
        }
    }
}

/// Forward Display to the inner type
impl<T> fmt::Display for Span<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.item.fmt(f)
    }
}

/// Convenience operation for unwrapping the span
impl<T> Deref for Span<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

#[cfg(test)]
mod test {
    use crate::span::Span;

    /// PartialEq considers both the inner type and the start and end values.
    /// Equality is not implemented generally because each user
    /// of Span may need to define its own equality strategy depending on
    /// whether it cares about the location.
    impl PartialEq for Span<Box<&str>> {
        fn eq(&self, other: &Self) -> bool {
            self.start == other.start && self.end == other.end && self.item == other.item
        }
    }

    impl Eq for Span<Box<&str>> {}

    #[test]
    fn conversions() {
        assert_eq!(
            Span::from((1, Box::new("foo"), 2)),
            Span {
                start: 1,
                end: 2,
                item: Box::new("foo")
            }
        );

        assert_eq!(
            Span::from((3..3, Box::new("foo"))),
            Span {
                start: 3,
                end: 3,
                item: Box::new("foo")
            }
        );

        assert_eq!(
            100..200,
            Span {
                start: 100,
                end: 200,
                item: "foo"
            }
            .into()
        )
    }
}
