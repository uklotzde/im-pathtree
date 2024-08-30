// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::borrow::Borrow as _;

use crate::{HalfEdgeRef, HashMap, PathTree, PathTreeTypes};

const DESCENDANTS_ITER_STACK_CAPACITY: usize = 1024;

#[derive(Debug, Clone)]
pub enum NodeValue<T: PathTreeTypes> {
    Inner(T::InnerValue),
    Leaf(T::LeafValue),
}

#[derive(Debug, Clone)]
pub enum Node<T>
where
    T: PathTreeTypes,
{
    Inner(InnerNode<T>),
    Leaf(LeafNode<T::LeafValue>),
}

impl<T> Node<T>
where
    T: PathTreeTypes,
{
    pub(crate) fn from_value_without_children(value: NodeValue<T>) -> Self {
        let node = match value {
            NodeValue::Inner(value) => Self::Inner(InnerNode::new(value)),
            NodeValue::Leaf(value) => Self::Leaf(LeafNode::new(value)),
        };
        debug_assert_eq!(node.children_count(), 0);
        node
    }

    pub const fn inner_value(&self) -> Option<&T::InnerValue> {
        match self {
            Self::Inner(InnerNode { value, .. }) => Some(value),
            Self::Leaf(LeafNode { .. }) => None,
        }
    }

    pub const fn leaf_value(&self) -> Option<&T::LeafValue> {
        match self {
            Self::Leaf(LeafNode { value, .. }) => Some(value),
            Self::Inner(InnerNode { .. }) => None,
        }
    }
}

impl<T> From<InnerNode<T>> for Node<T>
where
    T: PathTreeTypes,
{
    fn from(inner: InnerNode<T>) -> Self {
        Self::Inner(inner)
    }
}

impl<T> From<LeafNode<T::LeafValue>> for Node<T>
where
    T: PathTreeTypes,
{
    fn from(leaf: LeafNode<T::LeafValue>) -> Self {
        Self::Leaf(leaf)
    }
}

impl<T> Node<T>
where
    T: PathTreeTypes,
{
    /// Returns an iterator over all children of this node
    ///
    /// Only includes direct children, not grandchildren or other descendants.
    pub fn children(&self) -> impl ExactSizeIterator<Item = HalfEdgeRef<'_, T>> + '_ {
        match self {
            Self::Inner(inner) => itertools::Either::Left(inner.children()),
            Self::Leaf(_) => itertools::Either::Right(std::iter::empty()),
        }
    }

    /// Returns the number of children.
    ///
    /// Only includes direct children, not grandchildren or other descendants.
    ///
    /// In constant time, i.e. O(1).
    pub fn children_count(&self) -> usize {
        match self {
            Self::Inner(inner) => inner.children_count(),
            Self::Leaf(_) => 0,
        }
    }

    /// Find a child node by its path segment.
    ///
    /// Returns the id of the child node or `None` if not found.
    pub fn find_child(&self, child_path_segment: &T::PathSegmentRef) -> Option<T::NodeId> {
        match self {
            Self::Inner(inner) => inner.find_child(child_path_segment),
            Self::Leaf(_) => None,
        }
    }

    pub(crate) fn descendants<'a>(
        &'a self,
        tree: &'a PathTree<T>,
    ) -> DepthFirstDescendantsIter<'a, T> {
        match self {
            Self::Inner(inner) => inner.descendants(tree),
            Self::Leaf(_) => DepthFirstDescendantsIter::empty(tree),
        }
    }

    pub(crate) fn descendants_count<'a>(&'a self, tree: &'a PathTree<T>) -> usize {
        match self {
            Self::Inner(inner) => inner.descendants_count(tree),
            Self::Leaf(_) => 0,
        }
    }
}

/// Intrinsic data of an inner node.
#[derive(Debug, Clone)]
pub struct InnerNode<T>
where
    T: PathTreeTypes,
{
    pub(crate) children: HashMap<T::PathSegment, T::NodeId>,
    pub value: T::InnerValue,
}

impl<T> InnerNode<T>
where
    T: PathTreeTypes,
{
    /// Create an empty inner node with no children
    pub(crate) fn new(value: T::InnerValue) -> Self {
        Self {
            children: HashMap::new(),
            value,
        }
    }

    /// Edges to children of this node
    ///
    /// In arbitrary but stable ordering.
    pub fn children(&self) -> impl ExactSizeIterator<Item = HalfEdgeRef<'_, T>> + '_ {
        self.children
            .iter()
            .map(|(path_segment, node_id)| HalfEdgeRef {
                path_segment: path_segment.borrow(),
                node_id: *node_id,
            })
    }

    /// Returns the number of children.
    ///
    /// Only includes direct children, not grandchildren or other descendants.
    ///
    /// In constant time, i.e. O(1).
    pub fn children_count(&self) -> usize {
        self.children.len()
    }

    /// Find a child node by its path segment.
    ///
    /// Returns the id of the child node or `None` if not found.
    pub fn find_child(&self, child_path_segment: &T::PathSegmentRef) -> Option<T::NodeId> {
        self.children.get(child_path_segment).copied()
    }

    fn descendants<'a>(&'a self, tree: &'a PathTree<T>) -> DepthFirstDescendantsIter<'a, T> {
        let mut iter = DepthFirstDescendantsIter::new(tree, DESCENDANTS_ITER_STACK_CAPACITY);
        iter.push_parent(self);
        iter
    }

    /// Number of descendants of this node
    ///
    /// Recursively counts all descendants of this node.
    ///
    /// More efficient than `descendants().count()`.
    pub fn descendants_count<'a>(&'a self, tree: &'a PathTree<T>) -> usize {
        // This recursive implementation is probably faster than `descendants().count()`.
        // TODO: Replace by a non-recursive version.
        self.children().fold(
            0,
            |count,
             HalfEdgeRef {
                 path_segment: _,
                 node_id,
             }| {
                count
                    + 1
                    + tree
                        .lookup_node(node_id)
                        .map_or(0, |node| node.node.descendants_count(tree))
            },
        )
    }
}

/// Iterator over descendants of a node
///
/// Returned by [`PathTree::descendant_nodes()`].
#[derive(Debug)]
pub struct DepthFirstDescendantsIter<'a, T>
where
    T: PathTreeTypes,
{
    tree: &'a PathTree<T>,
    children_stack: Vec<HalfEdgeRef<'a, T>>,
}

impl<'a, T> DepthFirstDescendantsIter<'a, T>
where
    T: PathTreeTypes,
{
    fn new(tree: &'a PathTree<T>, stack_capacity: usize) -> Self {
        let children_stack = Vec::with_capacity(stack_capacity);
        Self {
            tree,
            children_stack,
        }
    }

    fn empty(tree: &'a PathTree<T>) -> Self {
        Self::new(tree, 0)
    }

    fn push_parent(&mut self, parent: &'a InnerNode<T>) {
        let len_before = self.children_stack.len();
        self.children_stack.extend(parent.children());
        debug_assert!(self.children_stack.len() >= len_before);
        // Reverse the order of children so that the first child ends up at the top of the stack.
        self.children_stack[len_before..].reverse();
    }
}

impl<'a, T> Iterator for DepthFirstDescendantsIter<'a, T>
where
    T: PathTreeTypes,
{
    type Item = HalfEdgeRef<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let child = self.children_stack.pop()?;
        let Some(node) = self.tree.lookup_node(child.node_id) else {
            unreachable!("child node not found: {node_id}", node_id = child.node_id);
        };
        match &node.node {
            Node::Inner(inner) => {
                self.push_parent(inner);
            }
            Node::Leaf(_) => (),
        }
        Some(child)
    }
}

/// Intrinsic data of a leaf node.
#[derive(Debug, Clone)]
pub struct LeafNode<V> {
    pub value: V,
}

impl<V> LeafNode<V> {
    /// Create a leaf node
    pub(crate) const fn new(value: V) -> Self {
        Self { value }
    }
}
