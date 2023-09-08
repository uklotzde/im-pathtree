// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::{borrow::Borrow, fmt, marker::PhantomData, sync::Arc};

use thiserror::Error;

use crate::{
    HashMap, InnerNode, LeafNode, Node, NodeId, NodeValue, PathSegment, PathSegmentRef, RootPath,
    SegmentedPath as _,
};

/// Type system for [`PathTree`].
pub trait PathTreeTypes: Clone + Default + fmt::Debug {
    type InnerValue: Clone + fmt::Debug;
    type LeafValue: Clone + fmt::Debug;
    type PathSegment: PathSegment + Borrow<Self::PathSegmentRef>;
    type PathSegmentRef: PathSegmentRef<Self::PathSegment> + ?Sized;
    type RootPath: RootPath<Self::PathSegment, Self::PathSegmentRef>;
}

#[derive(Debug, Error)]
pub enum InsertOrUpdateNodeValueError<T>
where
    T: PathTreeTypes,
{
    #[error("invalid path")]
    InvalidPath(NodeValue<T>),
    #[error("value type mismatch")]
    ValueTypeMismatch(NodeValue<T>),
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
}

/// Return type when removing a node from the tree.
#[derive(Debug, Clone)]
pub struct RemovedSubTree<T>
where
    T: PathTreeTypes,
{
    pub node: Arc<TreeNode<T>>,
    pub parent_node: Arc<TreeNode<T>>,
    pub removed_child_node_ids: Vec<NodeId>,
}

impl<T> InsertOrUpdateNodeValueError<T>
where
    T: PathTreeTypes,
{
    pub fn into_value(self) -> NodeValue<T> {
        match self {
            Self::InvalidPath(value) | Self::ValueTypeMismatch(value) => value,
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
    root_node_id: NodeId,
    nodes: HashMap<NodeId, Arc<TreeNode<T>>>,
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

impl<T: PathTreeTypes> PathTree<T> {
    /// Create a new path tree with the given root node.
    #[must_use]
    pub fn new(value: NodeValue<T>) -> Self {
        let root_node_id = NodeId::new();
        let root_node = Node::from_value(value);
        let root_node = TreeNode {
            id: root_node_id,
            parent: None,
            node: root_node,
        };
        let mut nodes = HashMap::new();
        nodes.insert(root_node_id, Arc::new(root_node));
        Self {
            root_node_id,
            nodes,
            _types: PhantomData,
        }
    }

    #[must_use]
    pub const fn root_node_id(&self) -> NodeId {
        self.root_node_id
    }

    #[must_use]
    pub fn root_node(&self) -> &Arc<TreeNode<T>> {
        self.resolve_node(self.root_node_id)
    }

    #[must_use]
    pub fn contains_node(&self, id: NodeId) -> bool {
        self.nodes.contains_key(&id)
    }

    #[must_use]
    pub fn lookup_node(&self, id: NodeId) -> Option<&Arc<TreeNode<T>>> {
        self.nodes.get(&id)
    }

    /// Resolve an existing node by its id.
    ///
    /// Only used internally for node ids that must exist. If the node does not exist
    /// the tree is probably in an inconsistent state!
    ///
    /// # Panics
    ///
    /// Panics if the node does not exist.
    #[must_use]
    fn resolve_node(&self, id: NodeId) -> &Arc<TreeNode<T>> {
        self.nodes.get(&id).expect("node exists")
    }

    #[must_use]
    #[cfg_attr(debug_assertions, allow(clippy::missing_panics_doc))] // Never panics
    pub fn find_node(&self, path: &T::RootPath) -> Option<&Arc<TreeNode<T>>> {
        // TODO: Use a trie data structure and Aho-Corasick algo for faster lookup?
        let root_node = self.resolve_node(self.root_node_id);
        if path.is_root() {
            return Some(root_node);
        }
        let mut last_visited_node = root_node;
        for path_segment in path.segments() {
            match &last_visited_node.node {
                Node::Leaf(_) => {
                    // path is too long
                    return None;
                }
                Node::Inner(inner_node) => {
                    let child_node = inner_node
                        .children
                        .get(path_segment)
                        .map(|node_id| self.resolve_node(*node_id));
                    if let Some(child_node) = child_node {
                        last_visited_node = child_node;
                    } else {
                        return None;
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
        Some(last_visited_node)
    }

    #[must_use]
    pub fn find_node_id(&self, path: &T::RootPath) -> Option<NodeId> {
        self.find_node(path).map(|node| node.id)
    }

    fn create_missing_parent_nodes_recursively<'a>(
        &mut self,
        child_path: &'a T::RootPath,
        mut new_inner_value: impl FnMut() -> T::InnerValue,
        try_clone_leaf_into_inner_value: impl FnOnce(&T::LeafValue) -> Option<T::InnerValue>,
    ) -> Result<TreeNodeParentChildContext<'a, T>, ()> {
        if child_path.is_root() {
            return Ok(TreeNodeParentChildContext {
                parent_node: None,
                child_path_segment: None,
            });
        }
        let mut try_clone_leaf_into_inner_value = Some(try_clone_leaf_into_inner_value);
        let mut next_parent_node = Arc::clone(self.root_node());
        let (parent_path_segments, child_path_segment) = child_path.parent_child_segments();
        for path_segment in parent_path_segments {
            next_parent_node = try_replace_leaf_with_inner_node(
                &mut self.nodes,
                next_parent_node,
                &mut try_clone_leaf_into_inner_value,
            )?;
            let Node::Inner(inner_node) = &next_parent_node.node else {
                break;
            };
            let child_node = inner_node
                .children
                .get(path_segment)
                .map(|node_id| self.resolve_node(*node_id));
            if let Some(child_node) = child_node {
                log::debug!("Found child node {child_node:?} for path segment {path_segment:?}");
                next_parent_node = Arc::clone(child_node);
            } else {
                // Add new, empty inner node
                let parent_node_id = next_parent_node.id;
                let child_node_id = NodeId::new();
                debug_assert_ne!(parent_node_id, child_node_id);
                let child_node = TreeNode {
                    id: child_node_id,
                    parent: Some(TreeNodeParent {
                        id: parent_node_id,
                        path_segment: path_segment.to_owned(),
                    }),
                    node: Node::Inner(InnerNode::new(new_inner_value())),
                };
                log::debug!(
                    "Inserting new child node {child_node:?} for path segment {path_segment:?}"
                );
                let child_node = Arc::new(child_node);
                let new_parent_node = Arc::clone(&child_node);
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
                let old_parent_node = self.nodes.insert(parent_node_id, Arc::new(parent_node));
                log::debug!(
                    "Updated parent node {old_parent_node:?} to {new_parent_node:?}",
                    old_parent_node = old_parent_node.expect("old parent exists")
                );
                next_parent_node = new_parent_node;
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
        let next_parent_node = try_replace_leaf_with_inner_node(
            &mut self.nodes,
            next_parent_node,
            &mut try_clone_leaf_into_inner_value,
        )?;
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
        new_inner_value: impl FnMut() -> T::InnerValue,
        try_clone_leaf_into_inner_value: impl FnOnce(&T::LeafValue) -> Option<T::InnerValue>,
    ) -> Result<ParentChildTreeNode<T>, InsertOrUpdateNodeValueError<T>> {
        let Ok(TreeNodeParentChildContext {
            parent_node,
            child_path_segment,
        }) = self.create_missing_parent_nodes_recursively(
            path,
            new_inner_value,
            try_clone_leaf_into_inner_value,
        )
        else {
            return Err(InsertOrUpdateNodeValueError::InvalidPath(new_value));
        };
        let Some(parent_node) = parent_node else {
            // Update the root node
            let new_root_node = self
                .root_node()
                .try_clone_update_value(new_value)
                .map_err(InsertOrUpdateNodeValueError::ValueTypeMismatch)?;
            let new_root_node = Arc::new(new_root_node);
            let old_root_node = self
                .nodes
                .insert(new_root_node.id, Arc::clone(&new_root_node));
            log::debug!(
                "Updated root node {old_root_node:?} to {new_root_node:?}",
                old_root_node = old_root_node.as_deref(),
                new_root_node = *new_root_node,
            );
            return Ok(ParentChildTreeNode {
                parent_node: None,
                child_node: new_root_node,
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
        parent_node: &TreeNode<T>,
        child_path_segment: &<T as PathTreeTypes>::PathSegmentRef,
        new_value: NodeValue<T>,
    ) -> Result<ParentChildTreeNode<T>, InsertOrUpdateNodeValueError<T>> {
        debug_assert!(matches!(parent_node.node, Node::Inner(_)));
        let Node::Inner(inner_node) = &parent_node.node else {
            return Err(InsertOrUpdateNodeValueError::InvalidPath(new_value));
        };
        // Wrap into an option as a workaround for the limitations of the borrow checker.
        // The value is consumed at most once in every code path.
        let mut new_value = Some(new_value);
        let path_segment = child_path_segment;
        let new_child_node = if let Some(child_node) = inner_node
            .children
            .get(path_segment)
            .map(|node_id| self.resolve_node(*node_id))
        {
            log::debug!(
                "Updating value of existing child node {child_node_id}",
                child_node_id = child_node.id
            );
            let new_value = new_value.take().expect("not consumed yet");
            child_node
                .try_clone_update_value(new_value)
                .map_err(InsertOrUpdateNodeValueError::ValueTypeMismatch)?
        } else {
            let value = new_value.take().expect("not consumed yet");
            let child_node_id = NodeId::new();
            log::debug!("Adding new child node {child_node_id}");
            debug_assert!(!self.contains_node(child_node_id));
            TreeNode {
                id: child_node_id,
                parent: Some(TreeNodeParent {
                    id: parent_node.id,
                    path_segment: path_segment.to_owned(),
                }),
                node: Node::from_value(value),
            }
        };
        let child_node_id = new_child_node.id;
        let new_child_node = Arc::new(new_child_node);
        let old_child_node = self
            .nodes
            .insert(child_node_id, Arc::clone(&new_child_node));
        log::debug!(
            "Updated child node {old_child_node:?} to {new_child_node:?}",
            old_child_node = old_child_node.as_deref(),
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
        })
    }

    /// Remove a node and its children from the tree.
    ///
    /// Removes the entire subtree rooted at the given node.
    ///
    /// The root node cannot be removed.
    ///
    /// Returns the ID of the parent node and the IDs of the removed nodes.
    #[allow(clippy::missing_panics_doc)] // Never panics
    pub fn remove_subtree(&mut self, node_id: NodeId) -> Option<RemovedSubTree<T>> {
        let (parent_node, child_node) = {
            let child_node = self.lookup_node(node_id)?;
            let parent_node = child_node
                .parent
                .as_ref()
                .map(|parent| self.resolve_node(parent.id))?;
            debug_assert!(matches!(parent_node.node, Node::Inner(_)));
            let Node::Inner(inner_node) = &parent_node.node else {
                unreachable!();
            };
            let mut inner_node = inner_node.clone();
            inner_node.children.remove(
                child_node
                    .parent
                    .as_ref()
                    .expect("has parent")
                    .path_segment
                    .borrow(),
            );
            let parent_node = TreeNode {
                id: parent_node.id,
                parent: parent_node.parent.clone(),
                node: Node::Inner(inner_node),
            };
            (parent_node, Arc::clone(child_node))
        };
        let parent_node_id = parent_node.id;
        let new_parent_node = Arc::new(parent_node);
        let old_parent_node = self
            .nodes
            .insert(parent_node_id, Arc::clone(&new_parent_node));
        debug_assert!(old_parent_node.is_some());
        log::debug!(
            "Updated parent node {old_parent_node:?} to {new_parent_node:?}",
            new_parent_node = self.resolve_node(parent_node_id)
        );
        let removed_child_node_ids = std::iter::once(child_node.id)
            .chain(child_node.node.children_recursively(self))
            .collect::<Vec<_>>();
        let node_count_before = self.node_count();
        for node_id in &removed_child_node_ids {
            self.nodes.remove(node_id);
        }
        let node_count_after = self.node_count();
        debug_assert!(node_count_before >= node_count_after);
        let number_of_nodes_removed = node_count_before - node_count_after;
        debug_assert_eq!(number_of_nodes_removed, removed_child_node_ids.len());
        debug_assert!(number_of_nodes_removed > 0);
        Some(RemovedSubTree {
            node: child_node,
            parent_node: new_parent_node,
            removed_child_node_ids,
        })
    }

    /// Retain only the nodes that match the given predicate.
    ///
    /// Returns the number of nodes that have been removed.
    #[allow(clippy::missing_panics_doc)] // Never panics
    pub fn retain_nodes(&mut self, mut predicate: impl FnMut(&TreeNode<T>) -> bool) {
        // TODO: Optimize by traversing the tree structure instead of iterating over
        // all nodes in no particular order. If a subtree is removed then all its
        // children don't need to be visited.
        let mut node_ids_to_remove = Vec::new();
        for node in self.nodes() {
            if !predicate(node) {
                node_ids_to_remove.push(node.id);
            }
        }
        // Remove the subtrees in reverse order of the depth of their root node.
        node_ids_to_remove.sort_by(|lhs, rhs| {
            let lhs_depth = self.count_parent_nodes(*lhs).expect("node exists");
            let rhs_depth = self.count_parent_nodes(*rhs).expect("node exists");
            lhs_depth.cmp(&rhs_depth)
        });
        for node_id in node_ids_to_remove {
            self.remove_subtree(node_id);
        }
    }

    /// All nodes in no particular order.
    pub fn nodes(&self) -> impl Iterator<Item = &Arc<TreeNode<T>>> {
        self.nodes.values()
    }

    /// Total number of nodes in the tree.
    #[must_use]
    pub fn node_count(&self) -> usize {
        let node_count = self.nodes.len();
        // Verify invariants
        debug_assert_eq!(
            node_count,
            1 + self.root_node().node.count_children_recursively(self)
        );
        debug_assert_eq!(node_count, self.nodes().count());
        node_count
    }

    /// All parent nodes of the given node up to the root node.
    ///
    /// Returns `None` if the given node is not found.
    #[must_use]
    pub fn parent_nodes(
        &self,
        node_id: NodeId,
    ) -> Option<impl Iterator<Item = &Arc<TreeNode<T>>> + '_> {
        let Some(mut next_node) = self.lookup_node(node_id) else {
            return None;
        };
        Some(std::iter::from_fn(move || {
            let Some(parent_node) = next_node
                .parent
                .as_ref()
                .map(|parent| self.resolve_node(parent.id))
            else {
                return None;
            };
            next_node = parent_node;
            Some(parent_node)
        }))
    }

    /// The number of parent nodes of the given node up to the root node.
    ///
    /// Returns `None` if the given node is not found.
    #[must_use]
    pub fn count_parent_nodes(&self, node_id: NodeId) -> Option<usize> {
        self.parent_nodes(node_id).map(std::iter::Iterator::count)
    }

    /// Number of child nodes of the given node (recursively).
    #[must_use]
    pub fn count_child_nodes_recursively(&self, node_id: NodeId) -> Option<usize> {
        self.lookup_node(node_id)
            .map(|tree_node| tree_node.node.count_children_recursively(self))
    }
}

/// Link of non-root node in the tree.
#[derive(Debug, Clone)]
pub struct TreeNodeParent<T: PathTreeTypes> {
    /// The id of the parent node.
    pub id: NodeId,

    /// Path segment for addressing the child from the parent.
    pub path_segment: <T as PathTreeTypes>::PathSegment,
}

/// Immutable node in the tree.
#[derive(Debug, Clone)]
pub struct TreeNode<T: PathTreeTypes> {
    /// Identifier for direct lookup.
    pub id: NodeId,

    /// Link to the parent node.
    ///
    /// Must be `None` for the root node and `Some` for all other nodes.
    pub parent: Option<TreeNodeParent<T>>,

    /// The actual content of this node.
    pub node: Node<T>,
}

impl<T: PathTreeTypes> TreeNode<T> {
    /// Clone the node and update its value.
    ///
    /// Fails if the type of the new value doesn't match the value type
    /// of the node.
    fn try_clone_update_value(&self, new_value: NodeValue<T>) -> Result<Self, NodeValue<T>>
    where
        T: PathTreeTypes,
    {
        let new_tree_node = match &self.node {
            Node::Leaf(LeafNode { .. }) => match new_value {
                NodeValue::Leaf(value) => Self {
                    id: self.id,
                    parent: self.parent.clone(),
                    node: Node::Leaf(LeafNode::new(value)),
                },
                new_value @ NodeValue::Inner(..) => {
                    return Err(new_value);
                }
            },
            Node::Inner(InnerNode { children, .. }) => match new_value {
                NodeValue::Inner(value) => {
                    let children = children.clone();
                    TreeNode {
                        id: self.id,
                        parent: self.parent.clone(),
                        node: Node::Inner(InnerNode { children, value }),
                    }
                }
                new_value @ NodeValue::Leaf(..) => {
                    return Err(new_value);
                }
            },
        };
        Ok(new_tree_node)
    }
}

fn try_replace_leaf_with_inner_node<T: PathTreeTypes>(
    nodes: &mut HashMap<NodeId, Arc<TreeNode<T>>>,
    node: Arc<TreeNode<T>>,
    try_clone_leaf_into_inner_value: &mut Option<
        impl FnOnce(&T::LeafValue) -> Option<T::InnerValue>,
    >,
) -> Result<Arc<TreeNode<T>>, ()> {
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
        return Err(());
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
