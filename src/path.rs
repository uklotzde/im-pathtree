// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::{
    borrow::Cow,
    ffi::{OsStr, OsString},
    fmt,
    hash::Hash,
};

/// Owned path segment.
pub trait PathSegment: Clone + Eq + Hash + fmt::Debug {
    fn empty() -> Self;

    /// Check if the segment is empty.
    #[must_use]
    fn is_empty(&self) -> bool;
}

/// Borrowed path segment.
pub trait PathSegmentRef<T: PathSegment>: Eq + Hash + fmt::Debug {
    /// Check if the segment is empty.
    #[must_use]
    fn is_empty(&self) -> bool;

    /// Check if the segment is equal to the given value.
    // TODO: How to avoid this unhandy equality comparison method?
    #[must_use]
    fn equals(&self, other: &T) -> bool;

    /// Convert the borrowed segment reference to an owned value.
    // TODO: How to use ToOwned for this purpose? The conflicting implementation
    // for Cow<'a, str> currently prevents this.
    #[must_use]
    fn to_owned(&self) -> T;
}

impl PathSegment for String {
    fn empty() -> Self {
        Self::new()
    }

    fn is_empty(&self) -> bool {
        self.as_str().is_empty()
    }
}

impl PathSegmentRef<String> for str {
    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn equals(&self, other: &String) -> bool {
        self == other
    }

    fn to_owned(&self) -> String {
        String::from(self)
    }
}

impl<'a> PathSegment for Cow<'a, str> {
    fn empty() -> Self {
        Cow::Borrowed("")
    }

    fn is_empty(&self) -> bool {
        self.as_ref().is_empty()
    }
}

impl<'a> PathSegmentRef<Cow<'a, str>> for str {
    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn equals(&self, other: &Cow<'a, str>) -> bool {
        self == other
    }

    fn to_owned(&self) -> Cow<'a, str> {
        Cow::Owned(String::from(self))
    }
}

impl PathSegment for OsString {
    fn empty() -> Self {
        Self::new()
    }

    fn is_empty(&self) -> bool {
        self.as_os_str().is_empty()
    }
}

impl PathSegmentRef<OsString> for OsStr {
    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn equals(&self, other: &OsString) -> bool {
        self == other
    }

    fn to_owned(&self) -> OsString {
        self.to_os_string()
    }
}

/// Decomposition of a path into segments.
pub trait SegmentedPath<S: PathSegment, R: PathSegmentRef<S> + ?Sized>:
    Clone + Eq + Hash + fmt::Debug
{
    /// Iterate over all path segments.
    ///
    /// All segments are guaranteed to be non-empty.
    // TODO: How to avoid boxing the result?
    #[must_use]
    fn segments(&self) -> Box<dyn Iterator<Item = &R> + '_>;

    /// Split the path into parent segments and the last child segment.
    ///
    /// The returned iterator excludes the last segment that is
    /// included by [`Self::segments()`].
    // TODO: How to avoid boxing the result?
    #[must_use]
    fn parent_child_segments(&self) -> (Box<dyn Iterator<Item = &R> + '_>, Option<&R>);
}

/// Absolute path with a root.
pub trait RootPath<S: PathSegment, R: PathSegmentRef<S> + ?Sized>: SegmentedPath<S, R> {
    /// Check if the path equals the root path.
    #[must_use]
    fn is_root(&self) -> bool;
}
