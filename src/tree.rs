// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::{fmt, marker::PhantomData, sync::Arc};

use im::HashMap;
use thiserror::Error;

use crate::{
    InnerNode, LeafNode, Node, NodeId, NodeValue, PathSegment, PathSegmentRef, RootPath,
    SegmentedPath as _,
};

/// Type system for [`PathTree`].
pub trait PathTreeTypes: Clone + Default + fmt::Debug {
    type InnerValue: Clone + fmt::Debug;
    type LeafValue: Clone + fmt::Debug;
    type PathSegment: PathSegment;
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
    pub fn root_node_id(&self) -> NodeId {
        self.root_node_id
    }

    #[must_use]
    pub fn root_node(&self) -> &Arc<TreeNode<T>> {
        self.lookup_node(self.root_node_id)
            .expect("root node exists")
    }

    #[must_use]
    pub fn contains_node(&self, id: NodeId) -> bool {
        self.nodes.contains_key(&id)
    }

    #[must_use]
    pub fn lookup_node(&self, id: NodeId) -> Option<&Arc<TreeNode<T>>> {
        self.nodes.get(&id)
    }

    #[must_use]
    pub fn find_node(&self, path: &T::RootPath) -> Option<&Arc<TreeNode<T>>> {
        // TODO: Use a trie data structure and Aho-Corasick algo for faster lookup?
        let root_node = self
            .lookup_node(self.root_node_id)
            .expect("root node exists");
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
                    let mut found = false;
                    for child_id in &inner_node.children {
                        let child_node = self.lookup_node(*child_id).expect("child node exists");
                        if path_segment
                            .equals(&child_node.parent.as_ref().expect("has parent").path_segment)
                        {
                            last_visited_node = child_node;
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return None;
                    }
                }
            }
            debug_assert!(path_segment.equals(
                &last_visited_node
                    .parent
                    .as_ref()
                    .expect("has parent")
                    .path_segment
            ));
        }
        Some(last_visited_node)
    }

    fn create_missing_parent_nodes_recursively<'a>(
        &mut self,
        child_path: &'a T::RootPath,
        mut new_inner_value: impl FnMut() -> T::InnerValue,
    ) -> Result<TreeNodeParentChildContext<'a, T>, ()> {
        if child_path.is_root() {
            return Ok(TreeNodeParentChildContext {
                parent_node: None,
                child_path_segment: None,
            });
        }
        let root_node = Arc::clone(self.root_node());
        let mut parent_node = root_node;
        let (parent_path_segments, child_path_segment) = child_path.parent_child_segments();
        for path_segment in parent_path_segments {
            // TODO: Avoid to use an optional here
            let mut new_parent_node = None;
            match &parent_node.node {
                Node::Leaf(_) => {
                    // path is too long
                    return Err(());
                }
                Node::Inner(inner_node) => {
                    for child_id in &inner_node.children {
                        let child_node = self.lookup_node(*child_id).expect("child node exists");
                        if path_segment
                            .equals(&child_node.parent.as_ref().expect("has parent").path_segment)
                        {
                            log::debug!(
                                "Found child node {child_node:?} for path segment {path_segment:?}"
                            );
                            new_parent_node = Some(Arc::clone(child_node));
                            break;
                        }
                    }
                    if new_parent_node.is_none() {
                        // Add new, empty inner node
                        let parent_node_id = parent_node.id;
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
                        log::debug!("Inserting new child node {child_node:?} for path segment {path_segment:?}");
                        let child_node = Arc::new(child_node);
                        new_parent_node = Some(Arc::clone(&child_node));
                        let old_child_node = self.nodes.insert(child_node.id, child_node);
                        debug_assert!(old_child_node.is_none());
                        let mut inner_node = inner_node.clone();
                        inner_node.children.push(child_node_id);
                        // Replace the parent node with the modified one
                        let parent_node = TreeNode {
                            node: inner_node.into(),
                            ..(*parent_node).clone()
                        };
                        let old_parent_node =
                            self.nodes.insert(parent_node_id, Arc::new(parent_node));
                        debug_assert!(old_parent_node.is_some());
                        log::debug!(
                            "Updated parent node {old_parent_node:?} to {new_parent_node:?}",
                            new_parent_node = self.lookup_node(parent_node_id)
                        );
                    }
                }
            }
            parent_node = new_parent_node.expect("new parent node has been assigned");
            debug_assert!(path_segment.equals(
                &parent_node
                    .parent
                    .as_ref()
                    .expect("has parent")
                    .path_segment
            ));
        }
        let parent_node = match parent_node.node {
            Node::Inner(_) => Some(parent_node),
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
    /// with the inner default value.
    ///
    /// Returns the parent node and the inserted/updated child node. Both require updating
    /// the parent node as well.
    ///
    /// In case of an error, the new value is returned back to the caller.
    pub fn insert_or_update_node_value(
        &mut self,
        path: &T::RootPath,
        new_value: NodeValue<T>,
        new_inner_value: impl FnMut() -> T::InnerValue,
    ) -> Result<ParentChildTreeNode<T>, InsertOrUpdateNodeValueError<T>> {
        let Ok(TreeNodeParentChildContext { parent_node, child_path_segment}) = self.create_missing_parent_nodes_recursively(path, new_inner_value) else {
            return Err(InsertOrUpdateNodeValueError::InvalidPath(new_value));
        };
        let Some(parent_node) = parent_node else {
            // Update the root node
            let new_root_node = self.root_node().try_clone_with_new_value(new_value).map_err(InsertOrUpdateNodeValueError::ValueTypeMismatch)?;
            let new_root_node = Arc::new(new_root_node);
            let old_root_node = self.nodes.insert(new_root_node.id, Arc::clone(&new_root_node));
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
        let Node::Inner(inner_node) = &parent_node.node else {
            unreachable!();
        };
        // Wrap into an option as a workaround for the limitations of the borrow checker.
        // The value is consumed at most once in every code path.
        let mut new_value = Some(new_value);
        let path_segment = child_path_segment.expect("should never be empty");
        let mut child_node_to_update = None;
        for (child_index, child_node_id) in inner_node.children().enumerate() {
            let child_node = self.lookup_node(child_node_id).expect("child node exists");
            if path_segment.equals(&child_node.parent.as_ref().expect("has parent").path_segment) {
                let new_value = new_value.take().expect("not consumed yet");
                let new_child_node = child_node
                    .try_clone_with_new_value(new_value)
                    .map_err(InsertOrUpdateNodeValueError::ValueTypeMismatch)?;
                child_node_to_update = Some((child_index, new_child_node));
                break;
            }
        }
        let (child_index, child_node) = if let Some(child_node_to_update) = child_node_to_update {
            log::debug!("Updating value of existing node: {path:?}");
            child_node_to_update
        } else {
            log::debug!("Adding new node: {path:?}");
            let value = new_value.take().expect("not consumed yet");
            let child_node_id = NodeId::new();
            let child_node = TreeNode {
                id: child_node_id,
                parent: Some(TreeNodeParent {
                    id: parent_node.id,
                    path_segment: path_segment.to_owned(),
                }),
                node: Node::from_value(value),
            };
            debug_assert!(!self.contains_node(child_node_id));
            (inner_node.children.len(), child_node)
        };
        let child_node_id = child_node.id;
        let new_child_node = Arc::new(child_node);
        let old_child_node = self
            .nodes
            .insert(child_node_id, Arc::clone(&new_child_node));
        log::debug!(
            "Updated child node {old_child_node:?} to {new_child_node:?}",
            old_child_node = old_child_node.as_deref(),
            new_child_node = *new_child_node,
        );
        let mut inner_node = inner_node.clone();
        inner_node.children.insert(child_index, child_node_id);
        let parent_node = TreeNode {
            node: Node::Inner(inner_node),
            ..(*parent_node).clone()
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

    /// Remove a node from the tree.
    ///
    /// Removes the entire subtree rooted at the given node.
    ///
    /// The root node cannot be removed.
    ///
    /// Returns the ID of the parent node and the IDs of the removed nodes.
    pub fn remove_sub_tree(&mut self, node_id: NodeId) -> Option<RemovedSubTree<T>> {
        let (parent_node, child_node) = {
            let child_node = self.lookup_node(node_id)?;
            let parent_node = child_node
                .parent
                .as_ref()
                .and_then(|parent| self.lookup_node(parent.id))?;
            debug_assert!(matches!(parent_node.node, Node::Inner(_)));
            let Node::Inner(inner_node) = &parent_node.node else {
                unreachable!();
            };
            let mut inner_node = inner_node.clone();
            inner_node
                .children
                .retain(|child_node_id| *child_node_id != node_id);
            let parent_node = TreeNode {
                node: Node::Inner(inner_node),
                ..(**parent_node).clone()
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
            new_parent_node = self.lookup_node(parent_node_id)
        );
        let removed_child_node_ids = std::iter::once(child_node.id)
            .chain(child_node.node.children_recursively(self))
            .collect::<Vec<_>>();
        let num_nodes_before = self.number_of_nodes();
        for node_id in &removed_child_node_ids {
            self.nodes.remove(node_id);
        }
        let num_nodes_after = self.number_of_nodes();
        debug_assert!(num_nodes_before >= num_nodes_after);
        let number_of_nodes_removed = num_nodes_before - num_nodes_after;
        debug_assert_eq!(number_of_nodes_removed, removed_child_node_ids.len());
        debug_assert!(number_of_nodes_removed > 0);
        Some(RemovedSubTree {
            parent_node: new_parent_node,
            removed_child_node_ids,
        })
    }

    #[must_use]
    pub fn number_of_nodes(&self) -> usize {
        let num_nodes = self.nodes.len();
        // Verify invariant
        debug_assert_eq!(num_nodes, self.count_nodes_recursively());
        num_nodes
    }

    #[must_use]
    fn count_nodes_recursively(&self) -> usize {
        1 + self.root_node().node.count_children_recursively(self)
    }

    #[must_use]
    pub fn count_child_nodes_recursively(&self, parent_node_id: NodeId) -> Option<usize> {
        self.lookup_node(parent_node_id)
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
    /// Clone the node with a new value.
    ///
    /// Fails if the type of the new value doesn't match the value type
    /// of the node.
    fn try_clone_with_new_value(&self, new_value: NodeValue<T>) -> Result<Self, NodeValue<T>>
    where
        T: PathTreeTypes,
    {
        let new_tree_node = match &self.node {
            Node::Leaf(LeafNode { .. }) => match new_value {
                NodeValue::Leaf(value) => Self {
                    id: self.id,
                    parent: self.parent.clone(),
                    node: Node::Leaf(LeafNode { value }),
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
