// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::sync::Arc;

use crate::{PathTreeTypes, TreeNode};

/// Half-edge to another node in the tree.
///
/// Owns the path segment.
#[derive(Debug, Clone)]
pub struct HalfEdgeOwned<T: PathTreeTypes> {
    /// Path segment from the (implicit) source to the target node.
    pub path_segment: T::PathSegmentOwned,

    /// The id of the target node.
    pub node_id: T::NodeId,
}

impl<T: PathTreeTypes> PartialEq for HalfEdgeOwned<T> {
    fn eq(&self, other: &Self) -> bool {
        let Self {
            path_segment,
            node_id,
        } = self;
        let Self {
            node_id: other_node_id,
            path_segment: other_path_segment,
        } = other;
        node_id.eq(other_node_id) && path_segment.eq(other_path_segment)
    }
}

impl<T: PathTreeTypes> Eq for HalfEdgeOwned<T>
where
    T::NodeId: Eq,
    T::PathSegmentOwned: Eq,
{
}

/// Half-edge to another node in the tree.
///
/// Borrows the path segment.
#[derive(Debug, Clone)]
pub struct HalfEdge<'a, T: PathTreeTypes> {
    /// Path segment from the (implicit) source to the target node.
    pub path_segment: &'a T::PathSegment,

    /// The id of the target node.
    pub node_id: T::NodeId,
}

impl<'a, T: PathTreeTypes> PartialEq for HalfEdge<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        let Self {
            path_segment,
            node_id,
        } = self;
        let Self {
            node_id: other_node_id,
            path_segment: other_path_segment,
        } = other;
        node_id.eq(other_node_id) && path_segment.eq(other_path_segment)
    }
}

impl<'a, T: PathTreeTypes> Eq for HalfEdge<'a, T>
where
    T::NodeId: Eq,
    T::PathSegment: Eq,
{
}

/// Half-edge to another node in the tree.
///
/// Borrows the path segment.
#[derive(Debug, Clone)]
pub struct HalfEdgeTreeNode<'a, T: PathTreeTypes> {
    /// Path segment from the (implicit) source to the target node.
    pub path_segment: &'a T::PathSegment,

    /// The target node.
    pub node: &'a Arc<TreeNode<T>>,
}
