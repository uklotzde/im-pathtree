// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::borrow::Cow;

use crate::{RootPath, SegmentedPath};

/// A lazy path implementation for testing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SlashPath<'a>(Cow<'a, str>);

impl SlashPath<'_> {
    const PATH_SEPARATOR: char = '/';

    const PATH_SEPARATOR_STR: &str = "/";

    const ROOT: Self = Self(Cow::Borrowed(Self::PATH_SEPARATOR_STR));

    fn as_str(&self) -> &str {
        self.0.as_ref()
    }

    fn segments(&self) -> impl Iterator<Item = &str> + '_ {
        self.as_str()
            .split_terminator(Self::PATH_SEPARATOR)
            .filter(|segment| !segment.is_empty())
    }

    fn parent_child_segments(&self) -> (impl Iterator<Item = &str> + '_, Option<&str>) {
        let (num_segments, child_segment) = self
            .segments()
            .fold((0, None), |(count, _), next| (count + 1, Some(next)));
        (
            Box::new(self.segments().take(num_segments.max(1) - 1)),
            child_segment,
        )
    }
}

impl<'a> SlashPath<'a> {
    const fn new(inner: Cow<'a, str>) -> Self {
        Self(inner)
    }
}

impl RootPath<Cow<'static, str>, str> for SlashPath<'_> {
    fn is_root(&self) -> bool {
        *self == Self::ROOT
    }
}

impl SegmentedPath<Cow<'static, str>, str> for SlashPath<'_> {
    fn segments(&self) -> Box<dyn Iterator<Item = &str> + '_> {
        Box::new(self.segments())
    }

    fn parent_child_segments(&self) -> (Box<dyn Iterator<Item = &str> + '_>, Option<&str>) {
        let (parent_segments, child_segment) = self.parent_child_segments();
        (Box::new(parent_segments), child_segment)
    }
}

#[test]
fn slash_path() {
    assert_eq!(0, SlashPath::ROOT.segments().count());
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
    const fn assert_send<T: Send>() {}
    let _ = assert_send::<PathTree>;
};

// <https://github.com/rust-lang/api-guidelines/issues/223#issuecomment-683346783>
const _: () = {
    const fn assert_sync<T: Sync>() {}
    let _ = assert_sync::<PathTree>;
};

#[test]
fn single_leaf_node() {
    let mut path_tree = PathTree::new(NodeValue::Leaf(23));
    let root_node_id = path_tree.root_node_id();

    assert_eq!(1, path_tree.node_count());
    assert_eq!(Some(0), path_tree.count_descendant_nodes(root_node_id));
    assert_eq!(Some(&23), path_tree.root_node().node.leaf_value());

    // Update the root node (leaf)
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::ROOT,
            NodeValue::Leaf(42),
            Default::default,
            |_| None
        )
        .is_ok());
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::ROOT,
            NodeValue::Inner(-1),
            Default::default,
            |_| None
        )
        .is_err());

    assert_eq!(1, path_tree.node_count());
    assert_eq!(Some(0), path_tree.count_descendant_nodes(root_node_id));
    assert_eq!(Some(&42), path_tree.root_node().node.leaf_value());

    // Inserting a new leaf node with its parent should fail
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(1),
            || -2, // Creates the parent node "/foo" with value -2
            |_| None
        )
        .is_err());
    // Replacing the leaf node with a new inner node should succeed
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(1),
            || -2, // Creates the parent node "/foo" with value -2
            |&leaf_value| leaf_value.try_into().ok()
        )
        .is_ok());

    assert_eq!(3, path_tree.node_count());
    assert_eq!(Some(2), path_tree.count_descendant_nodes(root_node_id));
    assert_eq!(Some(&42), path_tree.root_node().node.inner_value());
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

#[test]
#[allow(clippy::too_many_lines)]
fn multiple_nodes() {
    let mut path_tree = PathTree::new(NodeValue::Inner(-23));
    let root_node_id = path_tree.root_node_id();

    assert_eq!(1, path_tree.node_count());
    assert_eq!(Some(0), path_tree.count_descendant_nodes(root_node_id));
    assert_eq!(Some(&-23), path_tree.root_node().node.inner_value());

    // Insert a new leaf node with its parent
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(1),
            || -2, // Creates the parent node "/foo" with value -2
            |_| None
        )
        .is_ok());

    assert_eq!(3, path_tree.node_count());
    assert_eq!(Some(2), path_tree.count_descendant_nodes(root_node_id));
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
        .insert_or_update_node_value(
            &SlashPath::ROOT,
            NodeValue::Inner(-42),
            Default::default,
            |_| None
        )
        .is_ok());
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::ROOT,
            NodeValue::Leaf(42),
            Default::default,
            |_| None
        )
        .is_err());

    assert_eq!(3, path_tree.node_count());
    assert_eq!(Some(2), path_tree.count_descendant_nodes(root_node_id));
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

    // Inserting a new leaf node below a leaf node should fail
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar/baz")),
            NodeValue::Leaf(3),
            || 0,
            |_| None
        )
        .is_err());
    // Replacing the leaf node with a new inner node should succeed
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar/baz")),
            NodeValue::Leaf(3),
            || 0,
            |&leaf_value| leaf_value.try_into().ok().map(|v: isize| -v)
        )
        .is_ok());

    assert_eq!(4, path_tree.node_count());
    assert_eq!(Some(3), path_tree.count_descendant_nodes(root_node_id));
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
        Some(&-1),
        path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar")))
            .unwrap()
            .node
            .inner_value()
    );
    assert_eq!(
        Some(&3),
        path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar/baz")))
            .unwrap()
            .node
            .leaf_value()
    );

    {
        // Remove subtree "/foo/bar".
        let mut path_tree = path_tree.clone();
        assert_eq!(4, path_tree.node_count());
        let bar_node = path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar")))
            .unwrap();
        let bar_id = bar_node.id;
        let bar_descendant_count = path_tree.count_descendant_nodes(bar_id).unwrap();
        assert_eq!(1, bar_descendant_count);
        let removed_subtree = path_tree.remove_subtree(bar_id).unwrap();
        debug_assert_eq!(
            1 + bar_descendant_count,
            removed_subtree.removed_node_ids.len()
        );
        assert_eq!(2, path_tree.node_count());
    }

    {
        // Remove subtree "/foo".
        let mut path_tree = path_tree.clone();
        assert_eq!(4, path_tree.node_count());
        let foo_node = path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo")))
            .unwrap();
        let foo_id = foo_node.id;
        let foo_descendant_count = path_tree.count_descendant_nodes(foo_id).unwrap();
        assert_eq!(2, foo_descendant_count);
        let removed_subtree = path_tree.remove_subtree(foo_id).unwrap();
        debug_assert_eq!(
            1 + foo_descendant_count,
            removed_subtree.removed_node_ids.len()
        );
        // Only the root node remains.
        assert_eq!(1, path_tree.node_count());
    }

    {
        // The root node cannot be removed.
        let mut path_tree = path_tree.clone();
        assert_eq!(4, path_tree.node_count());
        assert!(path_tree.remove_subtree(path_tree.root_node_id()).is_none());
        assert_eq!(4, path_tree.node_count());
    }
}
