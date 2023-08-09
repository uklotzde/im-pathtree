// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use crate::{NodeId, PathTree, PathTreeTypes};

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
    Leaf(LeafNode<<T as PathTreeTypes>::LeafValue>),
}

impl<T> Node<T>
where
    T: PathTreeTypes,
{
    pub(crate) fn from_value(value: NodeValue<T>) -> Self {
        match value {
            NodeValue::Inner(value) => Self::Inner(InnerNode::new(value)),
            NodeValue::Leaf(value) => Self::Leaf(LeafNode { value }),
        }
    }

    pub fn inner_value(&self) -> Option<&T::InnerValue> {
        match self {
            Self::Inner(InnerNode { value, .. }) => Some(value),
            Self::Leaf(LeafNode { .. }) => None,
        }
    }

    pub fn leaf_value(&self) -> Option<&T::LeafValue> {
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

impl<T> From<LeafNode<<T as PathTreeTypes>::LeafValue>> for Node<T>
where
    T: PathTreeTypes,
{
    fn from(leaf: LeafNode<<T as PathTreeTypes>::LeafValue>) -> Self {
        Self::Leaf(leaf)
    }
}

impl<T> Node<T>
where
    T: PathTreeTypes,
{
    pub fn children(&self) -> impl Iterator<Item = NodeId> + '_ {
        match self {
            Self::Inner(inner) => Some(inner.children()),
            Self::Leaf(_) => None,
        }
        .into_iter()
        .flatten()
    }

    pub fn children_recursively<'a>(
        &'a self,
        tree: &'a PathTree<T>,
    ) -> Box<dyn Iterator<Item = NodeId> + 'a> {
        Box::new(
            match self {
                Self::Inner(inner) => Some(inner.children_recursively(tree)),
                Self::Leaf(_) => None,
            }
            .into_iter()
            .flatten(),
        )
    }

    pub fn count_children_recursively<'a>(&'a self, tree: &'a PathTree<T>) -> usize {
        match self {
            Self::Inner(inner) => inner.count_children_recursively(tree),
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
    pub(crate) children: Vec<NodeId>,
    pub value: <T as PathTreeTypes>::InnerValue,
}

impl<T> InnerNode<T>
where
    T: PathTreeTypes,
{
    /// Construct an empty inner node with no children
    pub const fn new(value: <T as PathTreeTypes>::InnerValue) -> Self {
        Self {
            children: Vec::new(),
            value,
        }
    }

    pub fn children(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.children.iter().copied()
    }

    fn children_recursively<'a>(
        &'a self,
        tree: &'a PathTree<T>,
    ) -> Box<dyn Iterator<Item = NodeId> + 'a> {
        Box::new(self.children().flat_map(|node_id| {
            // Traversal in depth-first order
            let grandchildren = tree
                .lookup_node(node_id)
                .into_iter()
                .flat_map(|node| node.node.children_recursively(tree));
            std::iter::once(node_id).chain(grandchildren)
        }))
    }

    pub fn count_children_recursively<'a>(&'a self, tree: &'a PathTree<T>) -> usize {
        self.children().fold(0, |count, node_id| {
            count
                + 1
                + tree
                    .lookup_node(node_id)
                    .map_or(0, |node| node.node.count_children_recursively(tree))
        })
    }
}

/// Intrinsic data of a leaf node.
#[derive(Debug, Clone)]
pub struct LeafNode<V> {
    pub value: V,
}
