// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::borrow::Cow;

use crate::{RootPath, SegmentedPath};

/// A lazy path implementation for testing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SlashPath<'a>(Cow<'a, str>);

impl<'a> SlashPath<'a> {
    const PATH_SEPARATOR_STR: &str = "/";

    const fn new(inner: Cow<'a, str>) -> Self {
        Self(inner)
    }

    fn as_str(&self) -> &str {
        self.0.as_ref()
    }

    fn segments(&self) -> impl Iterator<Item = &str> + '_ {
        self.as_str()
            .split_terminator(Self::PATH_SEPARATOR_STR)
            .filter(|segment| !segment.is_empty())
    }
}

impl RootPath<Cow<'static, str>, str> for SlashPath<'_> {
    fn root() -> Self {
        Self::new(Cow::Borrowed(Self::PATH_SEPARATOR_STR))
    }

    fn is_root(&self) -> bool {
        *self == Self::root()
    }
}

impl SegmentedPath<Cow<'static, str>, str> for SlashPath<'_> {
    fn segments(&self) -> Box<dyn Iterator<Item = &str> + '_> {
        Box::new(self.segments())
    }

    fn parent_segments(&self) -> Box<dyn Iterator<Item = &str> + '_> {
        let num_segments = self.segments().count();
        Box::new(self.segments().take(num_segments.max(1) - 1))
    }

    fn last_segment(&self) -> Option<&str> {
        self.segments().last()
    }
}

#[test]
fn slash_path() {
    assert_eq!(0, SlashPath::root().segments().count());
    assert_eq!(0, SlashPath::new(Cow::Borrowed("//")).segments().count());
    assert_eq!(
        vec![" ", "\t", "\n"],
        SlashPath::new(Cow::Borrowed(" /\t/\n"))
            .segments()
            .collect::<Vec<_>>()
    );
    assert_eq!(
        vec!["foo", "bar"],
        SlashPath::new(Cow::Borrowed("foo/bar"))
            .segments()
            .collect::<Vec<_>>()
    );
    assert_eq!(
        vec!["foo", "bar"],
        SlashPath::new(Cow::Borrowed("/foo/bar"))
            .segments()
            .collect::<Vec<_>>()
    );
    assert_eq!(
        vec!["foo", "bar"],
        SlashPath::new(Cow::Borrowed("foo/bar/"))
            .segments()
            .collect::<Vec<_>>()
    );
    assert_eq!(
        vec!["foo", "bar"],
        SlashPath::new(Cow::Borrowed("//foo///bar"))
            .segments()
            .collect::<Vec<_>>()
    );
}

#[derive(Debug, Clone, Default)]
struct PathTreeTypes;

impl crate::PathTreeTypes for PathTreeTypes {
    type RootPath = SlashPath<'static>;
    type PathSegment = Cow<'static, str>;
    type PathSegmentRef = str;
    type InnerValue = isize;
    type LeafValue = usize;
}

type PathTree = crate::PathTree<PathTreeTypes>;
type NodeValue = crate::NodeValue<PathTreeTypes>;

// <https://github.com/rust-lang/api-guidelines/issues/223#issuecomment-683346783>
const _: () = {
    fn assert_send<T: Send>() {}
    let _ = assert_send::<PathTree>;
};

// <https://github.com/rust-lang/api-guidelines/issues/223#issuecomment-683346783>
const _: () = {
    fn assert_sync<T: Sync>() {}
    let _ = assert_sync::<PathTree>;
};

#[test]
fn single_leaf_node() {
    let mut path_tree = PathTree::new(NodeValue::Leaf(23));
    let root_node_id = path_tree.root_node_id();

    assert_eq!(1, path_tree.number_of_nodes());
    assert_eq!(
        Some(0),
        path_tree.count_child_nodes_recursively(root_node_id)
    );
    assert_eq!(Some(&23), path_tree.root_node().node.leaf_value());

    // Update the root node (leaf)
    assert!(path_tree
        .insert_or_update_node_value(&SlashPath::root(), NodeValue::Leaf(42), Default::default)
        .is_ok());
    assert!(path_tree
        .insert_or_update_node_value(&SlashPath::root(), NodeValue::Inner(-1), Default::default)
        .is_err());

    assert_eq!(1, path_tree.number_of_nodes());
    assert_eq!(
        Some(0),
        path_tree.count_child_nodes_recursively(root_node_id)
    );
    assert_eq!(Some(&42), path_tree.root_node().node.leaf_value());

    // Inserting a new leaf node with its parent should fail
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(1),
            || -2 // Creates the parent node "/foo" with value -2
        )
        .is_err());
}

#[test]
fn multiple_nodes() {
    let mut path_tree = PathTree::new(NodeValue::Inner(-23));
    let root_node_id = path_tree.root_node_id();

    assert_eq!(1, path_tree.number_of_nodes());
    assert_eq!(
        Some(0),
        path_tree.count_child_nodes_recursively(root_node_id)
    );
    assert_eq!(Some(&-23), path_tree.root_node().node.inner_value());

    // Insert a new leaf node with its parent
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(1),
            || -2 // Creates the parent node "/foo" with value -2
        )
        .is_ok());

    assert_eq!(3, path_tree.number_of_nodes());
    assert_eq!(
        Some(2),
        path_tree.count_child_nodes_recursively(root_node_id)
    );
    assert_eq!(Some(&-23), path_tree.root_node().node.inner_value());
    assert_eq!(
        Some(&-2),
        path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo")))
            .unwrap()
            .node
            .inner_value()
    );
    assert_eq!(
        Some(&1),
        path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar")))
            .unwrap()
            .node
            .leaf_value()
    );
    assert!(path_tree
        .find_node(&SlashPath::new(Cow::Borrowed("/bar")))
        .is_none());
    assert!(path_tree
        .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar/baz")))
        .is_none());

    // Update the root node (inner)
    assert!(path_tree
        .insert_or_update_node_value(&SlashPath::root(), NodeValue::Inner(-42), Default::default)
        .is_ok());
    assert!(path_tree
        .insert_or_update_node_value(&SlashPath::root(), NodeValue::Leaf(42), Default::default)
        .is_err());

    assert_eq!(3, path_tree.number_of_nodes());
    assert_eq!(
        Some(2),
        path_tree.count_child_nodes_recursively(root_node_id)
    );
    assert_eq!(Some(&-42), path_tree.root_node().node.inner_value());
    assert_eq!(
        Some(&-2),
        path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo")))
            .unwrap()
            .node
            .inner_value()
    );
    assert_eq!(
        Some(&1),
        path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar")))
            .unwrap()
            .node
            .leaf_value()
    );
}
