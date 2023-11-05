// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

//! Immutable, path-addressable tree data structure.

#![warn(rust_2018_idioms)]
#![warn(rust_2021_compatibility)]
#![warn(missing_debug_implementations)]
#![warn(unreachable_pub)]
#![warn(unsafe_code)]
#![warn(rustdoc::broken_intra_doc_links)]
#![warn(clippy::pedantic)]
// Additional restrictions
#![warn(clippy::clone_on_ref_ptr)]
#![warn(clippy::missing_const_for_fn)]
#![warn(clippy::self_named_module_files)]
// Repetitions of module/type names occur frequently when using many
// modules for keeping the size of the source files handy. Often
// types have the same name as their parent module.
#![allow(clippy::module_name_repetitions)]
// Repeating the type name in `Default::default()` expressions is not needed
// as long as the context is obvious.
#![allow(clippy::default_trait_access)]
// TODO: Add missing docs
#![allow(clippy::missing_errors_doc)]

mod edge;
pub use self::edge::{HalfEdge, HalfEdgeRef};

mod node;
pub use self::node::{InnerNode, LeafNode, Node, NodeValue};

mod node_id;
pub use self::node_id::NodeId;

mod path;
pub use self::path::{PathSegment, PathSegmentRef, RootPath, SegmentedPath};

mod tree;
pub use self::tree::{
    AncestorTreeNodeIter, InsertOrUpdateNodeValueError, MatchNodePath, MatchedNodePath,
    ParentChildTreeNode, PathTree, PathTreeTypes, RemovedSubTree, ResolvedNodePath, TreeNode,
};

#[cfg(feature = "im")]
type HashMap<K, V> = im::HashMap<K, V>;

#[cfg(not(feature = "im"))]
type HashMap<K, V> = std::collections::HashMap<K, V>;

#[cfg(test)]
mod tests;
