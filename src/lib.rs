// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

//! Immutable, path-addressable tree data structure.

mod edge;
pub use self::edge::{HalfEdge, HalfEdgeRef, HalfEdgeTreeNodeRef};

mod node;
pub use self::node::{DepthFirstDescendantsIter, InnerNode, LeafNode, Node, NodeValue};

mod path;
pub use self::path::{PathSegment, PathSegmentRef, RootPath, SegmentedPath};

mod tree;
pub use self::tree::{
    AncestorTreeNodeIter, InsertOrUpdateNodeValueError, MatchNodePath, MatchedNodePath, NewNodeId,
    ParentChildTreeNode, PathTree, PathTreeTypes, RemovedSubtree, ResolvedNodePath, TreeNode,
    TreeNodeParentChildPathConflict, UpdateNodeValueError,
};

#[cfg(feature = "im")]
type HashMap<K, V> = im::HashMap<K, V>;

#[cfg(not(feature = "im"))]
type HashMap<K, V> = std::collections::HashMap<K, V>;

#[cfg(test)]
mod tests;
