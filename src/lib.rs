// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

//! Immutable, path-addressable tree data structure.

mod edge;
pub use self::edge::{HalfEdge, HalfEdgeOwned, HalfEdgeTreeNode};

mod node;
pub use self::node::{DepthFirstDescendantsIter, InnerNode, LeafNode, Node, NodeValue};

mod path;
pub use self::path::{PathSegment, RootPath, SegmentedPath};

mod tree;
pub use self::tree::{
    AncestorTreeNodeIter, InsertOrUpdateNodeValueError, MatchNodePath, NewNodeId,
    NodeInsertedOrUpdated, NodePathMatched, NodePathResolved, ParentNodeUpdated, PathTree,
    PathTreeTypes, SubtreeInsertedOrReplaced, SubtreeRemoved, TreeNode,
    TreeNodeParentChildPathConflict, UpdateNodeValueError,
};

#[cfg(feature = "im")]
type HashMap<K, V> = im::HashMap<K, V>;

#[cfg(not(feature = "im"))]
type HashMap<K, V> = std::collections::HashMap<K, V>;

#[cfg(test)]
mod tests;
