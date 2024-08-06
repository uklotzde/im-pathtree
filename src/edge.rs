// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::sync::Arc;

use crate::{PathTreeTypes, TreeNode};

/// Half-edge to another node in the tree.
///
/// Owns the path segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalfEdge<T: PathTreeTypes> {
    /// Path segment from the (implicit) source to the target node.
    pub path_segment: T::PathSegment,

    /// The id of the target node.
    pub node_id: T::NodeId,
}

/// Half-edge to another node in the tree.
///
/// Borrows the path segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalfEdgeRef<'a, T: PathTreeTypes> {
    /// Path segment from the (implicit) source to the target node.
    pub path_segment: &'a T::PathSegmentRef,

    /// The id of the target node.
    pub node_id: T::NodeId,
}

/// Half-edge to another node in the tree.
///
/// Borrows the path segment.
#[derive(Debug, Clone)]
pub struct HalfEdgeTreeNodeRef<'a, T: PathTreeTypes> {
    /// Path segment from the (implicit) source to the target node.
    pub path_segment: &'a T::PathSegmentRef,

    /// The target node.
    pub node: &'a Arc<TreeNode<T>>,
}
