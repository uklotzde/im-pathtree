// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::{borrow::Borrow, fmt, hash::Hash, marker::PhantomData, num::NonZeroUsize, sync::Arc};

use thiserror::Error;

use crate::{
    HalfEdge, HalfEdgeRef, HalfEdgeTreeNodeRef, HashMap, InnerNode, LeafNode, Node, NodeValue,
    PathSegment, PathSegmentRef, RootPath, SegmentedPath as _,
};

pub trait NewNodeId<T> {
    fn new_node_id(&mut self) -> T;
}

/// Type system for [`PathTree`].
pub trait PathTreeTypes: Clone + Default + fmt::Debug {
    type NodeId: Clone + Copy + PartialEq + Eq + Hash + fmt::Debug + fmt::Display;
    type NewNodeId: NewNodeId<Self::NodeId> + Clone + fmt::Debug;
    type InnerValue: Clone + fmt::Debug;
    type LeafValue: Clone + fmt::Debug;
    type PathSegment: PathSegment + Borrow<Self::PathSegmentRef>;
    type PathSegmentRef: PathSegmentRef<Self::PathSegment> + ?Sized;
    type RootPath: RootPath<Self::PathSegment, Self::PathSegmentRef>;
}

/// A conflicting path from a parent to a child node.
#[derive(Debug)]
pub struct TreeNodeParentChildPathConflict<T>
where
    T: PathTreeTypes,
{
    pub parent_node: Arc<TreeNode<T>>,
    pub child_path_segment: <T as PathTreeTypes>::PathSegment,
}

#[derive(Debug, Error)]
pub enum InsertOrUpdateNodeValueError<T>
where
    T: PathTreeTypes,
{
    #[error("path conflict")]
    PathConflict {
        conflict: TreeNodeParentChildPathConflict<T>,
        value: NodeValue<T>,
    },
    #[error("value type mismatch")]
    ValueTypeMismatch { value: NodeValue<T> },
}

#[derive(Debug, Error)]
pub enum UpdateNodeValueError<T>
where
    T: PathTreeTypes,
{
    #[error("value type mismatch")]
    ValueTypeMismatch { value: NodeValue<T> },
}

impl<T> From<UpdateNodeValueError<T>> for InsertOrUpdateNodeValueError<T>
where
    T: PathTreeTypes,
{
    fn from(from: UpdateNodeValueError<T>) -> Self {
        let UpdateNodeValueError::ValueTypeMismatch { value } = from;
        Self::ValueTypeMismatch { value }
    }
}

/// Return type of mutating tree operations.
///
/// Updating an immutable node in the tree requires to update its parent node.
#[derive(Debug, Clone)]
pub struct ParentChildTreeNode<T>
where
    T: PathTreeTypes,
{
    pub parent_node: Option<Arc<TreeNode<T>>>,
    pub child_node: Arc<TreeNode<T>>,
    pub replaced_child_node: Option<Arc<TreeNode<T>>>,
}

/// Return type when removing a node from the tree.
#[derive(Debug, Clone)]
pub struct RemovedSubtree<T>
where
    T: PathTreeTypes,
{
    /// Root node of the removed subtree.
    pub node: Arc<TreeNode<T>>,

    /// Updated parent node of the removed node.
    pub parent_node: Arc<TreeNode<T>>,

    /// Descendant node IDs that have been removed recursively from the tree.
    ///
    /// The total number of removed nodes is `1 + descendant_node_ids.len()`.
    pub descendant_node_ids: Vec<T::NodeId>,
}

impl<T> InsertOrUpdateNodeValueError<T>
where
    T: PathTreeTypes,
{
    pub fn into_value(self) -> NodeValue<T> {
        match self {
            Self::PathConflict { value, .. } | Self::ValueTypeMismatch { value } => value,
        }
    }
}

/// Cheaply clonable path tree structure.
///
/// Could be shared safely between multiple threads.
#[derive(Debug, Clone)]
pub struct PathTree<T>
where
    T: PathTreeTypes,
{
    root_node_id: T::NodeId,
    nodes: HashMap<T::NodeId, Arc<TreeNode<T>>>,
    new_node_id: T::NewNodeId,
    _types: PhantomData<T>,
}

#[derive(Debug, Default)]
struct TreeNodeParentChildContext<'a, T>
where
    T: PathTreeTypes,
{
    parent_node: Option<Arc<TreeNode<T>>>,
    child_path_segment: Option<&'a T::PathSegmentRef>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatchNodePath {
    Full,
    PartialOrFull,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatchedNodePath {
    Full {
        /// Number of path segments.
        ///
        /// Both the total and matched number of path segments are equals.
        number_of_segments: usize,
    },
    Partial {
        /// Number of matched path segments.
        ///
        /// Strictly less than the total number of path segments.
        number_of_matched_segments: NonZeroUsize,
    },
}

#[derive(Debug, Clone)]
pub struct ResolvedNodePath<'a, T>
where
    T: PathTreeTypes,
{
    pub node: &'a Arc<TreeNode<T>>,
    pub matched_path: MatchedNodePath,
}

impl<T: PathTreeTypes> PathTree<T> {
    /// Create a new path tree with the given root node.
    #[must_use]
    pub fn new(mut new_node_id: T::NewNodeId, root_node_value: NodeValue<T>) -> Self {
        let root_node_id = new_node_id.new_node_id();
        let root_node = TreeNode {
            id: root_node_id,
            parent: None,
            node: Node::from_value(root_node_value),
        };
        let mut nodes = HashMap::new();
        nodes.insert(root_node_id, Arc::new(root_node));
        Self {
            root_node_id,
            new_node_id,
            nodes,
            _types: PhantomData,
        }
    }

    fn new_node_id(&mut self) -> T::NodeId {
        self.new_node_id.new_node_id()
    }

    #[must_use]
    pub const fn root_node_id(&self) -> T::NodeId {
        self.root_node_id
    }

    #[must_use]
    pub fn root_node(&self) -> &Arc<TreeNode<T>> {
        self.get_node(self.root_node_id)
    }

    #[must_use]
    pub fn lookup_node(&self, id: T::NodeId) -> Option<&Arc<TreeNode<T>>> {
        self.nodes.get(&id)
    }

    /// Get an existing node by its id.
    ///
    /// Only used internally for node ids that must exist. If the node does not exist
    /// the tree is probably in an inconsistent state!
    ///
    /// # Panics
    ///
    /// Panics if the node does not exist.
    #[must_use]
    fn get_node(&self, id: T::NodeId) -> &Arc<TreeNode<T>> {
        self.nodes.get(&id).expect("node exists")
    }

    /// Find a node by its path.
    #[must_use]
    #[cfg_attr(debug_assertions, allow(clippy::missing_panics_doc))] // Never panics
    pub fn find_node(&self, path: &T::RootPath) -> Option<&Arc<TreeNode<T>>> {
        self.resolve_node_path(path, MatchNodePath::Full).map(
            |ResolvedNodePath { node, matched_path }| {
                debug_assert_eq!(
                    matched_path,
                    MatchedNodePath::Full {
                        number_of_segments: path.segments().count()
                    }
                );
                node
            },
        )
    }

    #[must_use]
    pub fn contains_node(&self, node: &Arc<TreeNode<T>>) -> bool {
        self.lookup_node(node.id)
            .map_or(false, |tree_node| Arc::ptr_eq(tree_node, node))
    }

    /// Find a node by its path.
    ///
    /// Returns the found node and the number of resolved path segments.
    #[must_use]
    #[cfg_attr(debug_assertions, allow(clippy::missing_panics_doc))] // Never panics
    pub fn resolve_node_path(
        &self,
        path: &T::RootPath,
        match_path: MatchNodePath,
    ) -> Option<ResolvedNodePath<'_, T>> {
        // TODO: Use a trie data structure and Aho-Corasick algo for faster lookup?
        let root_node = self.get_node(self.root_node_id);
        let mut last_visited_node = root_node;
        let mut number_of_matched_path_segments = 0;
        let mut partial_path_match = false;
        for path_segment in path.segments() {
            debug_assert!(!path_segment.is_empty());
            match &last_visited_node.node {
                Node::Leaf(_) => {
                    // Path is too long, i.e. the remaining path segments could not be resolved.
                    match match_path {
                        MatchNodePath::Full => {
                            return None;
                        }
                        MatchNodePath::PartialOrFull => {
                            partial_path_match = true;
                            break;
                        }
                    }
                }
                Node::Inner(inner_node) => {
                    let child_node = inner_node
                        .children
                        .get(path_segment)
                        .map(|node_id| self.get_node(*node_id));
                    if let Some(child_node) = child_node {
                        last_visited_node = child_node;
                        number_of_matched_path_segments += 1;
                    } else {
                        // Path segment mismatch.
                        match match_path {
                            MatchNodePath::Full => {
                                return None;
                            }
                            MatchNodePath::PartialOrFull => {
                                partial_path_match = true;
                                break;
                            }
                        }
                    }
                }
            }
            debug_assert_eq!(
                path_segment,
                last_visited_node
                    .parent
                    .as_ref()
                    .expect("has parent")
                    .path_segment
                    .borrow()
            );
        }
        let matched_path = if partial_path_match {
            // At least 1 segment must match for a partial match.
            let number_of_matched_segments = NonZeroUsize::new(number_of_matched_path_segments)?;
            debug_assert!(number_of_matched_segments.get() < path.segments().count());
            MatchedNodePath::Partial {
                number_of_matched_segments,
            }
        } else {
            debug_assert_eq!(number_of_matched_path_segments, path.segments().count());
            MatchedNodePath::Full {
                number_of_segments: number_of_matched_path_segments,
            }
        };
        Some(ResolvedNodePath {
            node: last_visited_node,
            matched_path,
        })
    }

    #[allow(clippy::too_many_lines)] // TODO
    fn create_missing_ancestor_nodes<'a>(
        &mut self,
        child_path: &'a T::RootPath,
        mut new_inner_value: impl FnMut() -> T::InnerValue,
        try_clone_leaf_into_inner_value: impl FnOnce(&T::LeafValue) -> Option<T::InnerValue>,
    ) -> Result<TreeNodeParentChildContext<'a, T>, TreeNodeParentChildPathConflict<T>> {
        if child_path.is_root() {
            return Ok(TreeNodeParentChildContext {
                parent_node: None,
                child_path_segment: None,
            });
        }
        let mut try_clone_leaf_into_inner_value = Some(try_clone_leaf_into_inner_value);
        let mut next_parent_node = Arc::clone(self.root_node());
        let (parent_path_segments, child_path_segment) = child_path.parent_child_segments();
        debug_assert!(child_path_segment.is_some());
        for path_segment in parent_path_segments {
            next_parent_node = match try_replace_leaf_with_inner_node(
                &mut self.nodes,
                next_parent_node,
                &mut try_clone_leaf_into_inner_value,
            ) {
                Ok(next_parent_node) => next_parent_node,
                Err(parent_node) => {
                    return Err(TreeNodeParentChildPathConflict {
                        parent_node,
                        child_path_segment: path_segment.to_owned(),
                    });
                }
            };
            let Node::Inner(inner_node) = &next_parent_node.node else {
                break;
            };
            let child_node = inner_node
                .children
                .get(path_segment)
                .map(|node_id| self.get_node(*node_id));
            if let Some(child_node) = child_node {
                log::debug!("Found child node {child_node:?} for path segment {path_segment:?}");
                next_parent_node = Arc::clone(child_node);
            } else {
                // Add new, empty inner node
                let child_node_id = self.new_node_id();
                debug_assert_ne!(child_node_id, next_parent_node.id);
                let child_node = TreeNode {
                    id: child_node_id,
                    parent: Some(HalfEdge {
                        path_segment: path_segment.to_owned(),
                        node_id: next_parent_node.id,
                    }),
                    node: Node::Inner(InnerNode::new(new_inner_value())),
                };
                log::debug!(
                    "Inserting new child node {child_node:?} for path segment {path_segment:?}"
                );
                let child_node = Arc::new(child_node);
                let new_next_parent_node = Arc::clone(&child_node);
                let old_child_node = self.nodes.insert(child_node.id, child_node);
                debug_assert!(old_child_node.is_none());
                let mut inner_node = inner_node.clone();
                let old_child_node_id = inner_node
                    .children
                    .insert(path_segment.to_owned(), child_node_id);
                debug_assert!(old_child_node_id.is_none());
                // Replace the parent node with the modified one
                let parent_node = TreeNode {
                    id: next_parent_node.id,
                    parent: next_parent_node.parent.clone(),
                    node: inner_node.into(),
                };
                let parent_node_id = parent_node.id;
                let old_parent_node = self.nodes.insert(parent_node_id, Arc::new(parent_node));
                log::debug!(
                    "Updated parent node {old_parent_node:?} to {new_parent_node:?}",
                    old_parent_node = old_parent_node.expect("old parent exists"),
                    new_parent_node = self.nodes.get(&parent_node_id).expect("new parent exists"),
                );
                next_parent_node = new_next_parent_node;
            }
            debug_assert_eq!(
                path_segment,
                next_parent_node
                    .parent
                    .as_ref()
                    .expect("has parent")
                    .path_segment
                    .borrow()
            );
        }
        let next_parent_node = match try_replace_leaf_with_inner_node(
            &mut self.nodes,
            next_parent_node,
            &mut try_clone_leaf_into_inner_value,
        ) {
            Ok(next_parent_node) => next_parent_node,
            Err(parent_node) => {
                return Err(TreeNodeParentChildPathConflict {
                    parent_node,
                    child_path_segment: child_path_segment
                        .expect("child path segment should exist")
                        .to_owned(),
                });
            }
        };
        let parent_node = match next_parent_node.node {
            Node::Inner(_) => Some(next_parent_node),
            Node::Leaf(_) => None,
        };
        Ok(TreeNodeParentChildContext {
            parent_node,
            child_path_segment,
        })
    }

    /// Insert or update a node in the tree.
    ///
    /// All missing parent nodes are created recursively and initialized
    /// with the value returned by `new_inner_value`.
    ///
    /// If the parent node exists and is a leaf node then it is replaced
    /// with an inner node by calling `try_clone_leaf_into_inner_value`.
    ///
    /// Returns the updated parent node and the inserted/updated child node.
    /// The parent node is `None` if the root node has been updated.
    ///
    /// In case of an error, the new value is returned back to the caller.
    #[allow(clippy::missing_panics_doc)] // Never panics
    pub fn insert_or_update_node_value(
        &mut self,
        path: &T::RootPath,
        new_value: NodeValue<T>,
        new_inner_value: &mut impl FnMut() -> T::InnerValue,
        try_clone_leaf_into_inner_value: impl FnOnce(&T::LeafValue) -> Option<T::InnerValue>,
    ) -> Result<ParentChildTreeNode<T>, InsertOrUpdateNodeValueError<T>> {
        let TreeNodeParentChildContext {
            parent_node,
            child_path_segment,
        } = match self.create_missing_ancestor_nodes(
            path,
            new_inner_value,
            try_clone_leaf_into_inner_value,
        ) {
            Ok(context) => context,
            Err(conflict) => {
                return Err(InsertOrUpdateNodeValueError::PathConflict {
                    conflict,
                    value: new_value,
                });
            }
        };
        let Some(parent_node) = parent_node else {
            // Update the root node.
            let old_root_node = Arc::clone(self.root_node());
            let new_root_node = self.update_node_value(&old_root_node, new_value)?;
            return Ok(ParentChildTreeNode {
                parent_node: None,
                child_node: new_root_node,
                replaced_child_node: Some(old_root_node),
            });
        };
        debug_assert!(matches!(parent_node.node, Node::Inner(_)));
        let child_path_segment = child_path_segment.expect("should never be empty");
        self.insert_or_update_child_node_value(&parent_node, child_path_segment, new_value)
    }

    /// Insert or update a child node in the tree.
    ///
    /// The parent node must exist and it must be an inner node.
    ///
    /// Returns the updated parent node and the inserted/updated child node.
    ///
    /// In case of an error, the new value is returned back to the caller.
    #[allow(clippy::missing_panics_doc)] // Never panics
    pub fn insert_or_update_child_node_value(
        &mut self,
        parent_node: &Arc<TreeNode<T>>,
        child_path_segment: &<T as PathTreeTypes>::PathSegmentRef,
        new_value: NodeValue<T>,
    ) -> Result<ParentChildTreeNode<T>, InsertOrUpdateNodeValueError<T>> {
        debug_assert!(self.contains_node(parent_node));
        debug_assert!(matches!(parent_node.node, Node::Inner(_)));
        let Node::Inner(inner_node) = &parent_node.node else {
            return Err(InsertOrUpdateNodeValueError::PathConflict {
                conflict: TreeNodeParentChildPathConflict {
                    parent_node: Arc::clone(parent_node),
                    child_path_segment: child_path_segment.to_owned(),
                },
                value: new_value,
            });
        };
        let path_segment = child_path_segment;
        if let Some(child_node) = inner_node
            .children
            .get(path_segment)
            .map(|node_id| self.get_node(*node_id))
        {
            log::debug!(
                "Updating value of existing child node {child_node_id}",
                child_node_id = child_node.id
            );
            let old_child_node = Arc::clone(child_node);
            let new_child_node = self.update_node_value(&old_child_node, new_value)?;
            return Ok(ParentChildTreeNode {
                parent_node: Some(Arc::clone(parent_node)),
                child_node: new_child_node,
                replaced_child_node: Some(old_child_node),
            });
        }
        let child_node_id = self.new_node_id();
        log::debug!("Adding new child node {child_node_id}");
        debug_assert!(!self.nodes.contains_key(&child_node_id));
        let new_child_node = TreeNode {
            id: child_node_id,
            parent: Some(HalfEdge {
                path_segment: path_segment.to_owned(),
                node_id: parent_node.id,
            }),
            node: Node::from_value(new_value),
        };
        let child_node_id = new_child_node.id;
        let new_child_node = Arc::new(new_child_node);
        let old_child_node = self
            .nodes
            .insert(child_node_id, Arc::clone(&new_child_node));
        debug_assert!(old_child_node.is_none());
        log::debug!(
            "Inserted new child node {new_child_node:?}",
            new_child_node = *new_child_node,
        );
        let mut inner_node = inner_node.clone();
        if let Some(child_node_id_mut) = inner_node.children.get_mut(path_segment) {
            *child_node_id_mut = child_node_id;
        } else {
            inner_node
                .children
                .insert(path_segment.to_owned(), child_node_id);
        }
        let parent_node = TreeNode {
            id: parent_node.id,
            parent: parent_node.parent.clone(),
            node: Node::Inner(inner_node),
        };
        let parent_node_id = parent_node.id;
        let new_parent_node = Arc::new(parent_node);
        let old_parent_node = self
            .nodes
            .insert(parent_node_id, Arc::clone(&new_parent_node));
        debug_assert!(old_parent_node.is_some());
        log::debug!(
            "Updated parent node {old_parent_node:?} to {new_parent_node:?}",
            old_parent_node = old_parent_node.as_deref(),
            new_parent_node = *new_parent_node,
        );
        Ok(ParentChildTreeNode {
            parent_node: Some(new_parent_node),
            child_node: new_child_node,
            replaced_child_node: None,
        })
    }

    /// Update a node value in the tree.
    ///
    /// Inner nodes with children could only be updated with an inner value.
    ///
    /// Returns the updated node with the new value.
    ///
    /// In case of an error, the new value is returned back to the caller.
    ///
    /// Undefined behavior if the given node does not belong to the tree.
    /// This precondition is only checked by debug assertions.
    #[allow(clippy::missing_panics_doc)] // Never panics
    pub fn update_node_value(
        &mut self,
        node: &Arc<TreeNode<T>>,
        new_value: NodeValue<T>,
    ) -> Result<Arc<TreeNode<T>>, UpdateNodeValueError<T>> {
        debug_assert!(self.contains_node(node));
        let new_node = Arc::new(node.try_clone_with_value(new_value)?);
        let old_node = self.nodes.insert(node.id, Arc::clone(&new_node));
        debug_assert!(old_node.is_some());
        debug_assert!(old_node.map_or(false, |old_node| Arc::ptr_eq(&old_node, node)));
        log::debug!("Updated node value: {node:?} -> {new_node:?}");
        Ok(new_node)
    }

    /// Remove a node and its children from the tree.
    ///
    /// Removes the entire subtree rooted at the given node.
    ///
    /// The root node cannot be removed.
    ///
    /// Returns the ID of the parent node and the IDs of the removed nodes.
    #[allow(clippy::missing_panics_doc)] // Never panics
    #[allow(clippy::result_unit_err)] // Cannot remove root node
    pub fn remove_subtree(&mut self, node: &Arc<TreeNode<T>>) -> Result<RemovedSubtree<T>, ()> {
        // Collect the IDs of all nodes that will be removed before starting to mutate the tree!
        // Otherwise invariants might be violated.
        let node_id = node.id;
        let descendant_node_ids = self
            .descendant_nodes(node)
            .map(
                |HalfEdgeRef {
                     path_segment: _,
                     node_id,
                 }| node_id,
            )
            .collect::<Vec<_>>();
        let nodes_count_before = self.nodes_count();
        // Disconnect the subtree from the parent node.
        let new_parent_node = {
            let child_node = node;
            debug_assert_eq!(child_node.id, node_id);
            let Some((path_segment_to_parent, parent_node)) = child_node.parent.as_ref().map(
                |HalfEdge {
                     path_segment: path_segment_to_parent,
                     node_id,
                 }| (path_segment_to_parent.borrow(), self.get_node(*node_id)),
            ) else {
                // Cannot remove the root node.
                debug_assert_eq!(node_id, self.root_node_id());
                return Err(());
            };
            debug_assert!(matches!(parent_node.node, Node::Inner(_)));
            let Node::Inner(inner_node) = &parent_node.node else {
                unreachable!();
            };
            let mut inner_node = inner_node.clone();
            let removed_id = inner_node.children.remove(path_segment_to_parent);
            debug_assert_eq!(removed_id, Some(node_id));
            TreeNode {
                id: parent_node.id,
                parent: parent_node.parent.clone(),
                node: Node::Inner(inner_node),
            }
        };
        let parent_node_id = new_parent_node.id;
        let new_parent_node = Arc::new(new_parent_node);
        let old_parent_node = self
            .nodes
            .insert(parent_node_id, Arc::clone(&new_parent_node));
        debug_assert!(old_parent_node.is_some());
        log::debug!(
            "Updated parent node {old_parent_node:?} to {new_parent_node:?}",
            new_parent_node = self.get_node(parent_node_id)
        );
        let node = self.nodes.remove(&node_id).expect("node exists");
        for node_id in &descendant_node_ids {
            self.nodes.remove(node_id);
        }
        // The tree is now in a consistent state again.
        let nodes_count_after = self.nodes_count();
        debug_assert!(nodes_count_before >= nodes_count_after);
        let removed_nodes_count = nodes_count_before - nodes_count_after;
        debug_assert_eq!(removed_nodes_count, 1 + descendant_node_ids.len());
        debug_assert!(removed_nodes_count > 0);
        Ok(RemovedSubtree {
            node,
            parent_node: new_parent_node,
            descendant_node_ids,
        })
    }

    /// Retain only the nodes that match the given predicate.
    ///
    /// The root node is always retained and cannot be removed.
    ///
    /// Returns the number of nodes that have been removed.
    #[allow(clippy::missing_panics_doc)] // Never panics
    pub fn retain_nodes(&mut self, mut predicate: impl FnMut(&TreeNode<T>) -> bool) {
        // TODO: Optimize by traversing the tree structure instead of iterating over
        // all nodes in no particular order. If a subtree is removed then all its
        // children don't need to be visited.
        let mut node_ids_to_remove = Vec::new();
        for node in self.nodes() {
            if !predicate(node) && node.id != self.root_node_id() {
                node_ids_to_remove.push(node.id);
            }
        }
        // Remove the subtrees in reverse order of the depth of their root node.
        node_ids_to_remove.sort_by(|lhs_id, rhs_id| {
            let lhs_node = self.get_node(*lhs_id);
            let rhs_node = self.get_node(*rhs_id);
            let lhs_depth = self.ancestor_nodes_count(lhs_node);
            let rhs_depth = self.ancestor_nodes_count(rhs_node);
            lhs_depth.cmp(&rhs_depth)
        });
        for node_id in node_ids_to_remove {
            let Some(node) = self.lookup_node(node_id) else {
                // Already removed.
                continue;
            };
            self.remove_subtree(&Arc::clone(node))
                .expect("removing the subtree should never fail");
        }
    }

    /// All nodes in no particular order.
    pub fn nodes(&self) -> impl Iterator<Item = &Arc<TreeNode<T>>> {
        self.nodes.values()
    }

    /// Total number of nodes in the tree.
    ///
    /// In constant time, i.e. O(1).
    #[must_use]
    pub fn nodes_count(&self) -> usize {
        let node_count = self.nodes.len();
        // Verify invariants
        debug_assert_eq!(
            node_count,
            1 + self.root_node().node.descendants_count(self)
        );
        debug_assert_eq!(node_count, self.nodes().count());
        node_count
    }

    /// Iterator over all ancestor nodes of the given node.
    ///
    /// Returns the parent node and the respective path segment from the child node
    /// in bottom-up order.
    pub fn ancestor_nodes<'a>(
        &'a self,
        node: &'a Arc<TreeNode<T>>,
    ) -> impl Iterator<Item = HalfEdgeTreeNodeRef<'_, T>> + Clone {
        AncestorTreeNodeIter::new(self, node)
    }

    /// The number of parent nodes of the given node up to the root node.
    #[must_use]
    pub fn ancestor_nodes_count(&self, node: &Arc<TreeNode<T>>) -> usize {
        self.ancestor_nodes(node).count()
    }

    /// Returns an iterator over all descendants of this node
    ///
    /// Recursively traverses the subtree.
    ///
    /// The ordering of nodes is undefined and an implementation detail. Only parent
    /// nodes are guaranteed to be visited before their children.
    pub fn descendant_nodes<'a>(
        &'a self,
        node: &'a Arc<TreeNode<T>>,
    ) -> impl Iterator<Item = HalfEdgeRef<'a, T>> {
        debug_assert!(self.contains_node(node));
        node.node.descendants(self)
    }

    /// Number of child nodes of the given node (recursively).
    #[must_use]
    pub fn descendant_nodes_count(&self, node: &Arc<TreeNode<T>>) -> usize {
        debug_assert!(self.contains_node(node));
        node.node.descendants_count(self)
    }
}

/// Immutable node in the tree.
#[derive(Debug, Clone)]
pub struct TreeNode<T: PathTreeTypes> {
    /// Identifier for direct lookup.
    pub id: T::NodeId,

    /// Link to the parent node.
    ///
    /// Must be `None` for the root node and `Some` for all other nodes.
    pub parent: Option<HalfEdge<T>>,

    /// The actual content of this node.
    pub node: Node<T>,
}

impl<T: PathTreeTypes> TreeNode<T> {
    /// Clone the node with a new value.
    ///
    /// Leaf values could be replaced by both leaf and inner values.
    /// An inner value could only be replaced by a leaf value, if the
    /// node does not have any children.
    ///
    /// Fails if the type of the new value is incompatible with the
    /// current value type of the node, depending on its children.
    fn try_clone_with_value(
        &self,
        new_value: NodeValue<T>,
    ) -> Result<Self, UpdateNodeValueError<T>> {
        let new_node = match &self.node {
            Node::Inner(InnerNode { children, .. }) => {
                match new_value {
                    NodeValue::Inner(new_value) => {
                        // Remains an inner node with the current children and the new value.
                        Self {
                            id: self.id,
                            parent: self.parent.clone(),
                            node: Node::Inner(InnerNode {
                                children: children.clone(),
                                value: new_value,
                            }),
                        }
                    }
                    new_value @ NodeValue::Leaf(_) => {
                        if !children.is_empty() {
                            return Err(UpdateNodeValueError::ValueTypeMismatch {
                                value: new_value,
                            });
                        }
                        Self {
                            id: self.id,
                            parent: self.parent.clone(),
                            node: Node::from_value(new_value),
                        }
                    }
                }
            }
            Node::Leaf(_) => {
                // Leaf node values could be replaced by both leaf and inner node values.
                Self {
                    id: self.id,
                    parent: self.parent.clone(),
                    node: Node::from_value(new_value),
                }
            }
        };
        Ok(new_node)
    }
}

fn try_replace_leaf_with_inner_node<T: PathTreeTypes>(
    nodes: &mut HashMap<T::NodeId, Arc<TreeNode<T>>>,
    node: Arc<TreeNode<T>>,
    try_clone_leaf_into_inner_value: &mut Option<
        impl FnOnce(&T::LeafValue) -> Option<T::InnerValue>,
    >,
) -> Result<Arc<TreeNode<T>>, Arc<TreeNode<T>>> {
    let TreeNode {
        id,
        parent,
        node: Node::Leaf(LeafNode { value: leaf_value }),
    } = &*node
    else {
        return Ok(node);
    };
    let try_clone_leaf_into_inner_value = try_clone_leaf_into_inner_value
        .take()
        .expect("consumed at most once");
    let Some(inner_value) = try_clone_leaf_into_inner_value(leaf_value) else {
        // Keep this leaf node
        return Err(node);
    };
    // Replace leaf node with empty inner node
    let inner_node = TreeNode {
        id: *id,
        parent: parent.clone(),
        node: InnerNode::new(inner_value).into(),
    };
    log::debug!(
        "Replacing leaf node {leaf_node:?} with inner node {inner_node:?}",
        leaf_node = *node
    );
    let inner_node = Arc::new(inner_node);
    let replaced_leaf_node = nodes.insert(inner_node.id, Arc::clone(&inner_node));
    debug_assert!(replaced_leaf_node.is_some());
    Ok(inner_node)
}

/// Iterator over all ancestor nodes of the given node.
///
/// Returns the node and the respective path segment from the child node.
#[derive(Debug, Clone)]
pub struct AncestorTreeNodeIter<'a, T: PathTreeTypes> {
    tree: &'a PathTree<T>,
    next_node: Option<&'a Arc<TreeNode<T>>>,
}

impl<'a, T: PathTreeTypes> AncestorTreeNodeIter<'a, T> {
    /// Create a new iterator over all ancestor nodes of the given node.
    ///
    /// The given node must exist in the tree. This is only checked in
    /// debug builds. Otherwise the iterator will be empty.
    #[must_use]
    pub fn new(tree: &'a PathTree<T>, node: &'a Arc<TreeNode<T>>) -> Self {
        debug_assert!(tree.contains_node(node));
        Self {
            tree,
            next_node: Some(node),
        }
    }
}

impl<'a, T: PathTreeTypes> Iterator for AncestorTreeNodeIter<'a, T> {
    type Item = HalfEdgeTreeNodeRef<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let parent = self.next_node.as_ref()?.parent.as_ref()?;
        self.next_node = self.tree.lookup_node(parent.node_id);
        self.next_node.map(|node| HalfEdgeTreeNodeRef {
            path_segment: parent.path_segment.borrow(),
            node,
        })
    }
}
