// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::{borrow::Borrow, fmt, hash::Hash, marker::PhantomData, num::NonZeroUsize, sync::Arc};

use derive_more::{Display, Error};

use crate::{
    HalfEdge, HalfEdgeOwned, HalfEdgeTreeNode, HashMap, InnerNode, LeafNode, Node, NodeValue,
    PathSegment, RootPath, SegmentedPath as _,
};

pub trait NewNodeId<T> {
    fn new_node_id(&mut self) -> T;
}

/// Type system for [`PathTree`].
pub trait PathTreeTypes: Clone + Default + fmt::Debug {
    type NodeId: Clone + Copy + Eq + Hash + fmt::Debug + fmt::Display;
    type NewNodeId: NewNodeId<Self::NodeId> + Clone + fmt::Debug;
    type InnerValue: Clone + fmt::Debug;
    type LeafValue: Clone + fmt::Debug;
    type PathSegmentOwned: Clone + Eq + Hash + fmt::Debug + Borrow<Self::PathSegment>;
    type PathSegment: PathSegment + ?Sized;
    type RootPath: RootPath<Self::PathSegment> + ?Sized;

    fn path_segment_to_owned(path_segment: &Self::PathSegment) -> Self::PathSegmentOwned;
}

/// A conflicting path from a parent to a child node.
#[derive(Debug)]
pub struct TreeNodeParentChildPathConflict<T>
where
    T: PathTreeTypes,
{
    pub parent_node: Arc<TreeNode<T>>,
    pub child_path_segment: T::PathSegmentOwned,
}

#[derive(Debug, Display, Error)]
pub enum InsertOrUpdateNodeValueError<T>
where
    T: PathTreeTypes,
{
    #[display("path conflict")]
    PathConflict {
        conflict: TreeNodeParentChildPathConflict<T>,
        value: NodeValue<T>,
    },
    #[display("value type mismatch")]
    ValueTypeMismatch { value: NodeValue<T> },
}

#[derive(Debug, Display, Error)]
pub enum UpdateNodeValueError<T>
where
    T: PathTreeTypes,
{
    #[display("value type mismatch")]
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

#[derive(Debug, Clone)]
pub struct NodeInsertedOrUpdated<T>
where
    T: PathTreeTypes,
{
    /// The new child node.
    ///
    /// The inserted or updated child node.
    pub node: Arc<TreeNode<T>>,

    /// The changes of the parent node.
    ///
    /// `None` if the node has no parent (i.e. is the root node of the tree)
    /// or if the parent node has not been updated.
    pub parent: Option<ParentNodeUpdated<T>>,
}

#[derive(Debug, Clone)]
pub struct ParentNodeUpdated<T>
where
    T: PathTreeTypes,
{
    /// The new parent node.
    pub node: Arc<TreeNode<T>>,

    /// The removed subtree.
    pub removed_subtree: Option<PathTree<T>>,
}

/// Return type when removing a node from the tree.
#[derive(Debug, Clone)]
pub struct SubtreeRemoved<T>
where
    T: PathTreeTypes,
{
    /// New parent node.
    ///
    /// Updated parent node of the removed node that remains in the tree.
    pub parent_node: Arc<TreeNode<T>>,

    /// Child path segment.
    ///
    /// Path segment between the parent node and its former child node,
    /// which has become the root node of the removed subtree.
    pub child_path_segment: T::PathSegmentOwned,

    /// Removed subtree.
    ///
    /// A new tree built from the removed node and all its descendants.
    pub removed_subtree: PathTree<T>,
}

/// Return type when inserting or replacing a subtree.
#[derive(Debug, Clone)]
pub struct SubtreeInsertedOrReplaced<T>
where
    T: PathTreeTypes,
{
    /// The root node of the inserted subtree.
    pub child_node_id: T::NodeId,

    /// New parent node.
    ///
    /// Updated parent node that contains the subtree as child.
    pub parent: ParentNodeUpdated<T>,
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
    child_path_segment: Option<&'a T::PathSegment>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatchNodePath {
    Full,
    PartialOrFull,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodePathMatched {
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
pub struct NodePathResolved<'a, T>
where
    T: PathTreeTypes,
{
    pub node: &'a Arc<TreeNode<T>>,
    pub matched_path: NodePathMatched,
}

impl<T: PathTreeTypes> PathTree<T> {
    /// Create a new path tree with the given root node.
    #[must_use]
    pub fn new(mut new_node_id: T::NewNodeId, root_node_value: NodeValue<T>) -> Self {
        let root_node_id = new_node_id.new_node_id();
        let root_node = TreeNode {
            id: root_node_id,
            parent: None,
            node: Node::from_value_without_children(root_node_value),
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
    pub fn find_node(&self, path: &T::RootPath) -> Option<&Arc<TreeNode<T>>> {
        self.resolve_node_path(path, MatchNodePath::Full).map(
            |NodePathResolved { node, matched_path }| {
                debug_assert_eq!(
                    matched_path,
                    NodePathMatched::Full {
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
    pub fn resolve_node_path<'a>(
        &'a self,
        path: &T::RootPath,
        match_path: MatchNodePath,
    ) -> Option<NodePathResolved<'a, T>> {
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
            NodePathMatched::Partial {
                number_of_matched_segments,
            }
        } else {
            debug_assert_eq!(number_of_matched_path_segments, path.segments().count());
            NodePathMatched::Full {
                number_of_segments: number_of_matched_path_segments,
            }
        };
        Some(NodePathResolved {
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
                        child_path_segment: T::path_segment_to_owned(path_segment),
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
                    parent: Some(HalfEdgeOwned {
                        path_segment: T::path_segment_to_owned(path_segment),
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
                    .insert(T::path_segment_to_owned(path_segment), child_node_id);
                debug_assert!(old_child_node_id.is_none());
                // Replace the parent node with the modified one.
                update_parent_node(
                    &mut self.nodes,
                    TreeNode {
                        id: next_parent_node.id,
                        parent: next_parent_node.parent.clone(),
                        node: inner_node.into(),
                    },
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
                        .map(T::path_segment_to_owned)
                        .expect("child path segment should exist"),
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
    ) -> Result<NodeInsertedOrUpdated<T>, InsertOrUpdateNodeValueError<T>> {
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
            return Ok(NodeInsertedOrUpdated {
                node: new_root_node,
                parent: None,
            });
        };
        debug_assert!(matches!(parent_node.node, Node::Inner(_)));
        let child_path_segment = child_path_segment.expect("should never be empty");
        self.insert_or_update_child_node_value(&parent_node, child_path_segment, None, new_value)
    }

    /// Insert or update a child node in the tree.
    ///
    /// The parent node must exist and it must be an inner node.
    ///
    /// By providing `old_child_path_segment` an existing node could
    /// be renamed and updated. This will retain its `NodeId`.
    ///
    /// Returns the updated parent node and the inserted/updated child node.
    ///
    /// In case of an error, the new value is returned back to the caller.
    #[allow(clippy::missing_panics_doc)] // Never panics
    #[allow(clippy::too_many_lines)] // TODO
    pub fn insert_or_update_child_node_value(
        &mut self,
        parent_node: &Arc<TreeNode<T>>,
        child_path_segment: &T::PathSegment,
        old_child_path_segment: Option<&T::PathSegment>,
        new_value: NodeValue<T>,
    ) -> Result<NodeInsertedOrUpdated<T>, InsertOrUpdateNodeValueError<T>> {
        debug_assert!(self.contains_node(parent_node));
        debug_assert!(matches!(parent_node.node, Node::Inner(_)));
        let Node::Inner(inner_node) = &parent_node.node else {
            return Err(InsertOrUpdateNodeValueError::PathConflict {
                conflict: TreeNodeParentChildPathConflict {
                    parent_node: Arc::clone(parent_node),
                    child_path_segment: T::path_segment_to_owned(child_path_segment),
                },
                value: new_value,
            });
        };
        let old_child_path_segment = old_child_path_segment.unwrap_or(child_path_segment);
        let (child_node, inner_node_and_removed_subtree) = if let Some(child_node) = inner_node
            .children
            .get(old_child_path_segment)
            .map(|node_id| self.get_node(*node_id))
        {
            let child_node_id = child_node.id;
            log::debug!("Updating value of existing child node {child_node_id}");
            let old_child_node = Arc::clone(child_node);
            if old_child_path_segment == child_path_segment {
                // No renaming.
                let new_child_node = self.update_node_value(&old_child_node, new_value)?;
                (new_child_node, None)
            } else {
                let new_parent = HalfEdgeOwned {
                    path_segment: T::path_segment_to_owned(child_path_segment),
                    node_id: parent_node.id,
                };
                let updated_child_node =
                    old_child_node.try_clone_with_parent_and_value(Some(new_parent), new_value)?;
                let (mut inner_node, removed_subtree) = if let Some(subtree_root_node_id) =
                    parent_node.node.find_child(child_path_segment)
                {
                    log::debug!("Removing child node {child_node_id} with subtree from {child_path_segment:?}");
                    let removed_subtree = self.remove_subtree_by_id(subtree_root_node_id);
                    debug_assert!(removed_subtree.is_some());
                    let SubtreeRemoved {
                        parent_node,
                        child_path_segment: removed_child_path_segment,
                        removed_subtree,
                    } = removed_subtree.expect("subtree has been removed");
                    debug_assert_eq!(removed_child_path_segment.borrow(), child_path_segment);
                    let Node::Inner(inner_node) = &parent_node.node else {
                        unreachable!();
                    };
                    (inner_node.clone(), Some(removed_subtree))
                } else {
                    // The (new) child path segment is not occupied by a node/subtree.
                    (inner_node.clone(), None)
                };
                // Move the updated node to the new, empty location.
                log::debug!("Moving child node {child_node_id} from {old_child_path_segment:?} to {child_path_segment:?}");
                let removed_child_node_id = inner_node.children.remove(old_child_path_segment);
                debug_assert_eq!(removed_child_node_id, Some(child_node_id));
                debug_assert!(self.nodes.contains_key(&child_node_id));
                let child_node_id = updated_child_node.id;
                let new_child_node = Arc::new(updated_child_node);
                let replaced_child_node = self
                    .nodes
                    .insert(child_node_id, Arc::clone(&new_child_node));
                debug_assert!(replaced_child_node.is_some());
                debug_assert!(Arc::ptr_eq(
                    replaced_child_node.as_ref().unwrap(),
                    &old_child_node
                ));
                debug_assert!(!inner_node.children.contains_key(child_path_segment));
                inner_node
                    .children
                    .insert(T::path_segment_to_owned(child_path_segment), child_node_id);
                (new_child_node, Some((inner_node, removed_subtree)))
            }
        } else {
            let child_node_id = self.new_node_id();
            log::debug!("Adding new child node {child_node_id}");
            debug_assert!(!self.nodes.contains_key(&child_node_id));
            let new_child_node = TreeNode {
                id: child_node_id,
                parent: Some(HalfEdgeOwned {
                    path_segment: T::path_segment_to_owned(child_path_segment),
                    node_id: parent_node.id,
                }),
                node: Node::from_value_without_children(new_value),
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
            if let Some(child_node_id_mut) = inner_node.children.get_mut(child_path_segment) {
                *child_node_id_mut = child_node_id;
            } else {
                inner_node
                    .children
                    .insert(T::path_segment_to_owned(child_path_segment), child_node_id);
            }
            (new_child_node, Some((inner_node, None)))
        };
        let parent = inner_node_and_removed_subtree.map(|(inner_node, removed_subtree)| {
            let new_parent_node = update_parent_node(
                &mut self.nodes,
                TreeNode {
                    id: parent_node.id,
                    parent: parent_node.parent.clone(),
                    node: Node::Inner(inner_node),
                },
            );
            ParentNodeUpdated {
                node: new_parent_node,
                removed_subtree,
            }
        });
        Ok(NodeInsertedOrUpdated {
            node: child_node,
            parent,
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
    /// Removes and returns the entire subtree rooted at the given node.
    ///
    /// The root node cannot be removed and the tree remains unchanged.
    ///
    /// Returns the removed subtree or `None` if unchanged.
    /// The node ids in the removed subtree remain unchanged.
    #[allow(clippy::missing_panics_doc)] // Never panics
    pub fn remove_subtree_by_id(&mut self, node_id: T::NodeId) -> Option<SubtreeRemoved<T>> {
        if node_id == self.root_node_id {
            // Cannot remove the root node.
            return None;
        }
        let nodes_count_before = self.nodes_count();
        let node = self.nodes.remove(&node_id)?;
        // The descendants of the removed node could still be collected,
        // even though the tree is already incomplete.
        let descendant_node_ids = node
            .node
            .descendants(self)
            .map(
                |HalfEdge {
                     path_segment: _,
                     node_id,
                 }| node_id,
            )
            .collect::<Vec<_>>();
        // Split off the nodes of the subtree from the remaining nodes.
        #[cfg(feature = "im")]
        let mut subtree_nodes: HashMap<_, _> = descendant_node_ids
            .into_iter()
            .filter_map(|node_id| self.nodes.remove_with_key(&node_id))
            .collect();
        #[cfg(not(feature = "im"))]
        let mut subtree_nodes: HashMap<_, _> = descendant_node_ids
            .into_iter()
            .filter_map(|node_id| self.nodes.remove_entry(&node_id))
            .collect();
        // Disconnect the subtree from the parent node. The old parent node
        // still references the root node of the removed subtree as a child.
        let new_parent_node = {
            debug_assert!(node.parent.is_some());
            let HalfEdgeOwned {
                path_segment: parent_path_segment,
                node_id: parent_node_id,
            } = node.parent.as_ref().expect("has parent");
            let parent_node = self.nodes.get(parent_node_id).expect("has a parent");
            debug_assert!(matches!(parent_node.node, Node::Inner(_)));
            let Node::Inner(inner_node) = &parent_node.node else {
                unreachable!();
            };
            let mut inner_node = inner_node.clone();
            let removed_id = inner_node.children.remove(parent_path_segment.borrow());
            debug_assert_eq!(removed_id, Some(node_id));
            TreeNode {
                id: parent_node.id,
                parent: parent_node.parent.clone(),
                node: Node::Inner(inner_node),
            }
        };
        let new_parent_node = update_parent_node(&mut self.nodes, new_parent_node);
        // The tree is now back in a consistent state and we can use the public API again.
        let nodes_count_after = self.nodes_count();
        debug_assert!(nodes_count_before >= nodes_count_after);
        let removed_nodes_count = nodes_count_before.get() - nodes_count_after.get();
        let TreeNode { id, parent, node } = Arc::unwrap_or_clone(node);
        let parent = parent.expect("has a parent");
        debug_assert_eq!(parent.node_id, new_parent_node.id);
        let child_path_segment = parent.path_segment;
        let subtree_root_node = Arc::new(TreeNode {
            id,
            parent: None,
            node,
        });
        subtree_nodes.insert(node_id, subtree_root_node);
        let removed_subtree = Self {
            root_node_id: node_id,
            nodes: subtree_nodes,
            new_node_id: self.new_node_id.clone(),
            _types: PhantomData,
        };
        debug_assert_eq!(removed_nodes_count, removed_subtree.nodes_count().get());
        Some(SubtreeRemoved {
            parent_node: new_parent_node,
            child_path_segment,
            removed_subtree,
        })
    }

    /// Insert a subtree.
    ///
    /// The root node of the subtree will replace an existing node.
    /// The existing node must node have any children, otherwise the
    /// insertion will fail.
    ///
    /// The inserted nodes from the subtree will be assigned new ids
    /// that are generated by this tree.
    ///
    /// By providing `old_child_path_segment` an existing node could
    /// be renamed and replaced by the subtree. This will retain its
    /// `NodeId`.
    #[allow(clippy::missing_panics_doc)] // Never panics
    pub fn insert_or_replace_subtree(
        &mut self,
        parent_node: &Arc<TreeNode<T>>,
        child_path_segment: &T::PathSegment,
        old_child_path_segment: Option<&T::PathSegment>,
        mut subtree: Self,
    ) -> Result<SubtreeInsertedOrReplaced<T>, InsertOrUpdateNodeValueError<T>> {
        debug_assert!(self.contains_node(parent_node));
        // Initialized with the old node id, which will be replaced with the new node id
        // after the root node of the subtree has been inserted/replaced.
        let mut subtree_root_node_id = subtree.root_node_id();
        let mut subtree_root_parent_updated = None;
        {
            let subtree_node_ids = std::iter::once(subtree.root_node_id())
                .chain(subtree.root_node().node.descendants(&subtree).map(
                    |HalfEdge {
                         path_segment: _,
                         node_id,
                     }| node_id,
                ))
                .collect::<Vec<_>>();
            let mut old_to_new_node_id =
                std::collections::HashMap::<T::NodeId, T::NodeId>::with_capacity(
                    subtree_node_ids.len(),
                );
            for old_node_id in subtree_node_ids {
                let old_node = subtree.nodes.remove(&old_node_id).expect("node exists");
                // Ideally, the nodes in the subtree are not referenced in the outer
                // context to avoid cloning them. For most use cases this assumption
                // should be valid.
                let TreeNode {
                    id: _,
                    parent,
                    node,
                } = Arc::unwrap_or_clone(old_node);
                // TODO: This could be optimized when not reusing insert_or_update_child_node_value()
                // and instead inserting or replacing the node directly.
                let (parent_node, child_path_segment, old_child_path_segment) =
                    if let Some(parent) = parent {
                        debug_assert!(old_to_new_node_id.contains_key(&parent.node_id));
                        let parent_node_id = old_to_new_node_id
                            .get(&parent.node_id)
                            .copied()
                            .expect("parent node has already been inserted");
                        let parent_node = self
                            .nodes
                            .get(&parent_node_id)
                            .expect("parent node has already been inserted");
                        (parent_node, parent.path_segment, None)
                    } else {
                        // Root node.
                        debug_assert_eq!(old_node_id, subtree.root_node_id());
                        (
                            parent_node,
                            T::path_segment_to_owned(child_path_segment),
                            old_child_path_segment,
                        )
                    };
                let node_value = match node {
                    Node::Inner(inner) => NodeValue::Inner(inner.value),
                    Node::Leaf(leaf) => NodeValue::Leaf(leaf.value),
                };
                let NodeInsertedOrUpdated {
                    node: child_node,
                    parent,
                } = self
                    .insert_or_update_child_node_value(
                        &Arc::clone(parent_node),
                        child_path_segment.borrow(),
                        old_child_path_segment,
                        node_value,
                    )
                    .inspect_err(|_| {
                        // Insertion could only fail for the first node,
                        // which is the root node of the subtree. This ensures
                        // that `self` remains unchanged on error.
                        debug_assert_eq!(old_node_id, subtree.root_node_id());
                    })?;
                let child_node_id = child_node.id;
                if old_node_id == subtree.root_node_id() {
                    // Subtree root node inserted/updated.
                    subtree_root_node_id = child_node_id;
                    subtree_root_parent_updated = parent;
                }
                debug_assert!(!old_to_new_node_id.contains_key(&old_node_id));
                old_to_new_node_id.insert(old_node_id, child_node_id);
            }
        }
        Ok(SubtreeInsertedOrReplaced {
            child_node_id: subtree_root_node_id,
            parent: subtree_root_parent_updated.expect("parent node has been updated"),
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
            self.remove_subtree_by_id(node_id);
        }
    }

    /// All nodes in no particular order.
    pub fn nodes(&self) -> impl ExactSizeIterator<Item = &Arc<TreeNode<T>>> {
        self.nodes.values()
    }

    /// Total number of nodes in the tree.
    ///
    /// Executed in constant time, i.e. O(1). But only if not both
    /// debug assertions and the feature "expensive-debug-assertions"
    /// are enabled.
    #[must_use]
    pub fn nodes_count(&self) -> NonZeroUsize {
        debug_assert!(!self.nodes.is_empty());
        let nodes_count = self.nodes.len();
        #[cfg(feature = "expensive-debug-assertions")]
        {
            // Verify invariants
            debug_assert_eq!(
                nodes_count,
                1 + self.root_node().node.descendants_count(self)
            );
            debug_assert_eq!(nodes_count, self.nodes().count());
        }
        // SAFETY: A tree always contains at least a root node.
        debug_assert!(nodes_count > 0);
        #[allow(unsafe_code)]
        unsafe {
            NonZeroUsize::new_unchecked(nodes_count)
        }
    }

    /// Iterator over all ancestor nodes of the given node.
    ///
    /// Returns the parent node and the respective path segment from the child node
    /// in bottom-up order.
    pub fn ancestor_nodes<'a>(
        &'a self,
        node: &'a Arc<TreeNode<T>>,
    ) -> impl Iterator<Item = HalfEdgeTreeNode<'_, T>> + Clone {
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
    ) -> impl Iterator<Item = HalfEdge<'a, T>> {
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
    pub parent: Option<HalfEdgeOwned<T>>,

    /// The actual content of this node.
    pub node: Node<T>,
}

impl<T: PathTreeTypes> TreeNode<T> {
    fn try_clone_with_value(
        &self,
        new_value: NodeValue<T>,
    ) -> Result<Self, UpdateNodeValueError<T>> {
        self.try_clone_with_parent_and_value(None, new_value)
    }

    /// Clones the node with a new parent and value.
    ///
    /// Leaf values could be replaced by both leaf and inner values.
    /// An inner value could only be replaced by a leaf value, if the
    /// node does not have any children.
    ///
    /// Fails if the type of the new value is incompatible with the
    /// current value type of the node, depending on its children.
    fn try_clone_with_parent_and_value(
        &self,
        new_parent: Option<HalfEdgeOwned<T>>,
        new_value: NodeValue<T>,
    ) -> Result<Self, UpdateNodeValueError<T>> {
        let new_node = match &self.node {
            Node::Inner(InnerNode { children, .. }) => {
                match new_value {
                    NodeValue::Inner(new_value) => {
                        // Remains an inner node with the current children and the new value.
                        Self {
                            id: self.id,
                            parent: new_parent.or_else(|| self.parent.clone()),
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
                            parent: new_parent.or_else(|| self.parent.clone()),
                            node: Node::from_value_without_children(new_value),
                        }
                    }
                }
            }
            Node::Leaf(_) => {
                // Leaf node values could be replaced by both leaf and inner node values.
                Self {
                    id: self.id,
                    parent: new_parent.or_else(|| self.parent.clone()),
                    node: Node::from_value_without_children(new_value),
                }
            }
        };
        debug_assert_eq!(self.id, new_node.id);
        debug_assert_eq!(self.node.children_count(), new_node.node.children_count());
        debug_assert!(self
            .node
            .children()
            .zip(new_node.node.children())
            .all(|(old, new)| old == new));
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
    type Item = HalfEdgeTreeNode<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let parent = self.next_node.as_ref()?.parent.as_ref()?;
        self.next_node = self.tree.lookup_node(parent.node_id);
        self.next_node.map(|node| HalfEdgeTreeNode {
            path_segment: parent.path_segment.borrow(),
            node,
        })
    }
}

fn update_parent_node<T: PathTreeTypes>(
    nodes: &mut HashMap<T::NodeId, Arc<TreeNode<T>>>,
    parent_node: TreeNode<T>,
) -> Arc<TreeNode<T>> {
    debug_assert!(matches!(parent_node.node, Node::Inner(_)));
    let parent_node_id = parent_node.id;
    let new_parent_node = Arc::new(parent_node);
    debug_assert!(nodes.contains_key(&parent_node_id));
    let old_parent_node = nodes.insert(parent_node_id, Arc::clone(&new_parent_node));
    debug_assert!(old_parent_node.is_some());
    log::debug!(
        "Updated parent node {old_parent_node:?} to {new_parent_node:?}",
        old_parent_node = old_parent_node.expect("old parent exists"),
        new_parent_node = *new_parent_node,
    );
    new_parent_node
}
