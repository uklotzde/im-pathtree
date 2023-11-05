// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use crate::{NodeId, PathTreeTypes};

/// Half-edge to another node in the tree.
///
/// Owns the path segment.
#[derive(Debug, Clone)]
pub struct HalfEdge<T: PathTreeTypes> {
    /// The id of the target node.
    pub node_id: NodeId,

    /// Path segment from the (implicit) source to the target node.
    pub path_segment: <T as PathTreeTypes>::PathSegment,
}

/// Half-edge to another node in the tree.
///
/// Borrows the path segment.
#[derive(Debug, Clone)]
pub struct HalfEdgeRef<'a, T: PathTreeTypes> {
    /// The id of the target node.
    pub node_id: NodeId,

    /// Path segment from the (implicit) source to the target node.
    pub path_segment: &'a T::PathSegmentRef,
}
