// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::{ffi::OsStr, fmt, hash::Hash};

/// Borrowed path segment.
pub trait PathSegment: Eq + Hash + fmt::Debug {
    /// Check if the segment is empty.
    #[must_use]
    fn is_empty(&self) -> bool;
}

impl PathSegment for str {
    fn is_empty(&self) -> bool {
        self.is_empty()
    }
}

impl PathSegment for OsStr {
    fn is_empty(&self) -> bool {
        self.is_empty()
    }
}

/// Decomposition of a path into segments.
pub trait SegmentedPath<S: PathSegment + ?Sized>: Clone + Eq + Hash + fmt::Debug {
    /// Iterate over all path segments.
    ///
    /// All segments are guaranteed to be non-empty.
    // TODO: How to avoid boxing the result?
    #[must_use]
    fn segments(&self) -> Box<dyn Iterator<Item = &S> + '_>;

    /// Split the path into parent segments and the last child segment.
    ///
    /// The returned iterator excludes the last segment that is
    /// included by [`Self::segments()`].
    // TODO: How to avoid boxing the result?
    #[must_use]
    fn parent_child_segments(&self) -> (Box<dyn Iterator<Item = &S> + '_>, Option<&S>);
}

/// [`SegmentedPath`] with a root element.
pub trait RootPath<S: PathSegment + ?Sized>: SegmentedPath<S> {
    /// Check if the path equals the root path.
    #[must_use]
    fn is_root(&self) -> bool;
}
