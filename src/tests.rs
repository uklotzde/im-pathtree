// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::{borrow::Cow, sync::Arc};

use crate::{
    ChildNodeChangeset, MatchNodePath, MatchedNodePath, RemovedSubtree, RootPath, SegmentedPath,
};

/// A lazy path implementation for testing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SlashPath<'a>(Cow<'a, str>);

impl SlashPath<'_> {
    const PATH_SEPARATOR: char = '/';

    const PATH_SEPARATOR_STR: &'static str = "/";

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
struct NewNodeId {
    next_node_id: usize,
}

impl crate::NewNodeId<usize> for NewNodeId {
    fn new_node_id(&mut self) -> usize {
        let next_node_id = self.next_node_id;
        self.next_node_id = self.next_node_id.checked_add(1).unwrap();
        next_node_id
    }
}

#[derive(Debug, Clone, Default, PartialEq)]
struct PathTreeTypes;

impl crate::PathTreeTypes for PathTreeTypes {
    type NodeId = usize;
    type NewNodeId = NewNodeId;
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
    let mut path_tree = PathTree::new(Default::default(), NodeValue::Leaf(23));

    assert_eq!(1, path_tree.nodes_count());
    assert_eq!(0, path_tree.descendant_nodes_count(path_tree.root_node()));
    assert_eq!(Some(&23), path_tree.root_node().node.leaf_value());

    // Update the root (leaf) node.
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::ROOT,
            NodeValue::Leaf(42),
            &mut Default::default,
            |_| None
        )
        .is_ok());
    // Replacing a leaf node with an inner node should succeed.
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::ROOT,
            NodeValue::Inner(-1),
            &mut Default::default,
            |_| None
        )
        .is_ok());
    // Restore the root (leaf) node.
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::ROOT,
            NodeValue::Leaf(42),
            &mut Default::default,
            |_| None
        )
        .is_ok());

    assert_eq!(1, path_tree.nodes_count());
    assert_eq!(0, path_tree.descendant_nodes_count(path_tree.root_node()));
    assert_eq!(Some(&42), path_tree.root_node().node.leaf_value());

    // Inserting a new leaf node with its parent should fail
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(1),
            &mut || -2, // Creates the parent node "/foo" with value -2
            |_| None
        )
        .is_err());
    // Replacing the leaf node with a new inner node should succeed
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(1),
            &mut || -2, // Creates the parent node "/foo" with value -2
            |&leaf_value| leaf_value.try_into().ok()
        )
        .is_ok());

    assert_eq!(3, path_tree.nodes_count());
    assert_eq!(2, path_tree.descendant_nodes_count(path_tree.root_node()));
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
    let mut path_tree = PathTree::new(Default::default(), NodeValue::Inner(-23));

    assert_eq!(1, path_tree.nodes_count());
    assert_eq!(0, path_tree.descendant_nodes_count(path_tree.root_node()));
    assert_eq!(Some(&-23), path_tree.root_node().node.inner_value());

    // Insert a new leaf node with its parent
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(1),
            &mut || -2, // Creates the parent node "/foo" with value -2
            |_| None
        )
        .is_ok());

    assert_eq!(3, path_tree.nodes_count());
    assert_eq!(2, path_tree.descendant_nodes_count(path_tree.root_node()));
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

    // Update the root (inner) node.
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::ROOT,
            NodeValue::Inner(-42),
            &mut Default::default,
            |_| None
        )
        .is_ok());

    assert_eq!(3, path_tree.nodes_count());
    assert_eq!(2, path_tree.descendant_nodes_count(path_tree.root_node()));
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

    // Inserting a new leaf node below a leaf node should fail.
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar/baz")),
            NodeValue::Leaf(3),
            &mut || 0,
            |_| None
        )
        .is_err());
    // Replacing the leaf node with a new inner node should succeed.
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar/baz")),
            NodeValue::Leaf(3),
            &mut || 0,
            |&leaf_value| leaf_value.try_into().ok().map(|v: isize| -v)
        )
        .is_ok());

    assert_eq!(4, path_tree.nodes_count());
    assert_eq!(3, path_tree.descendant_nodes_count(path_tree.root_node()));
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
        // Remove subtree "/foo/bar/baz".
        let mut path_tree = path_tree.clone();
        assert_eq!(4, path_tree.nodes_count());
        let node = path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar/baz")))
            .unwrap();
        let descendant_nodes_count = path_tree.descendant_nodes_count(node);
        assert_eq!(0, descendant_nodes_count);
        let RemovedSubtree {
            parent_node: _,
            child_path_segment,
            removed_subtree,
        } = path_tree.remove_subtree_by_id(node.id).unwrap();
        debug_assert_eq!(child_path_segment.as_ref(), "baz");
        debug_assert_eq!(1 + descendant_nodes_count, removed_subtree.nodes_count());
        assert_eq!(3, path_tree.nodes_count());
    }

    {
        // Remove subtree "/foo/bar".
        let mut path_tree = path_tree.clone();
        assert_eq!(4, path_tree.nodes_count());
        let node = path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar")))
            .unwrap();
        let descendant_nodes_count = path_tree.descendant_nodes_count(node);
        assert_eq!(1, descendant_nodes_count);
        let RemovedSubtree {
            parent_node: _,
            child_path_segment,
            removed_subtree,
        } = path_tree.remove_subtree_by_id(node.id).unwrap();
        debug_assert_eq!(child_path_segment.as_ref(), "bar");
        debug_assert_eq!(1 + descendant_nodes_count, removed_subtree.nodes_count());
        assert_eq!(2, path_tree.nodes_count());
    }

    {
        // Remove subtree "/foo".
        let mut path_tree = path_tree.clone();
        assert_eq!(4, path_tree.nodes_count());
        let node = path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo")))
            .unwrap();
        let descendant_nodes_count = path_tree.descendant_nodes_count(node);
        assert_eq!(2, descendant_nodes_count);
        let RemovedSubtree {
            parent_node: _,
            child_path_segment,
            removed_subtree,
        } = path_tree.remove_subtree_by_id(node.id).unwrap();
        debug_assert_eq!(child_path_segment.as_ref(), "foo");
        debug_assert_eq!(1 + descendant_nodes_count, removed_subtree.nodes_count());
        // Only the root node remains.
        assert_eq!(1, path_tree.nodes_count());
    }

    {
        // The root node cannot be removed.
        let mut path_tree = path_tree.clone();
        assert_eq!(4, path_tree.nodes_count());
        assert!(path_tree
            .remove_subtree_by_id(path_tree.root_node_id())
            .is_none());
        assert_eq!(4, path_tree.nodes_count());
    }

    // Transforming an inner node with children into a leaf node should fail.
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::ROOT,
            NodeValue::Leaf(11),
            &mut Default::default,
            |_| None
        )
        .is_err());
    let root_node_id = path_tree.root_node_id();
    path_tree.retain_nodes(|node| node.id == root_node_id);
    assert_eq!(1, path_tree.nodes_count());
    assert_eq!(0, path_tree.descendant_nodes_count(path_tree.root_node()));
    // Transforming an inner node without children into a leaf node should succeed.
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::ROOT,
            NodeValue::Leaf(11),
            &mut Default::default,
            |_| None
        )
        .is_ok());
    assert_eq!(Some(&11), path_tree.root_node().node.leaf_value());
}

#[test]
#[allow(clippy::too_many_lines)]
fn resolve_node_path() {
    let mut path_tree = PathTree::new(Default::default(), NodeValue::Inner(0));
    let mut new_inner_value = {
        let mut inner_value = 0;
        move || {
            inner_value -= 1;
            inner_value
        }
    };

    path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/one/two/three/four/five")),
            NodeValue::Leaf(55),
            &mut new_inner_value,
            |_| None,
        )
        .unwrap();
    path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/one/two/3/4/5")),
            NodeValue::Leaf(5),
            &mut new_inner_value,
            |_| None,
        )
        .unwrap();
    path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/one/two/3/4/6")),
            NodeValue::Leaf(6),
            &mut new_inner_value,
            |_| None,
        )
        .unwrap();

    for match_node_path in [MatchNodePath::Full, MatchNodePath::PartialOrFull] {
        assert_eq!(
            MatchedNodePath::Full {
                number_of_segments: 0
            },
            path_tree
                .resolve_node_path(&SlashPath::new(Cow::Borrowed("/")), match_node_path)
                .unwrap()
                .matched_path
        );
        assert_eq!(
            MatchedNodePath::Full {
                number_of_segments: 1
            },
            path_tree
                .resolve_node_path(&SlashPath::new(Cow::Borrowed("/one")), match_node_path)
                .unwrap()
                .matched_path
        );
        assert_eq!(
            MatchedNodePath::Full {
                number_of_segments: 2
            },
            path_tree
                .resolve_node_path(&SlashPath::new(Cow::Borrowed("/one/two")), match_node_path)
                .unwrap()
                .matched_path
        );
        assert_eq!(
            MatchedNodePath::Full {
                number_of_segments: 3
            },
            path_tree
                .resolve_node_path(
                    &SlashPath::new(Cow::Borrowed("/one/two/three")),
                    match_node_path
                )
                .unwrap()
                .matched_path
        );
        assert_eq!(
            MatchedNodePath::Full {
                number_of_segments: 3
            },
            path_tree
                .resolve_node_path(
                    &SlashPath::new(Cow::Borrowed("/one/two/3")),
                    match_node_path
                )
                .unwrap()
                .matched_path
        );
        assert_eq!(
            MatchedNodePath::Full {
                number_of_segments: 4
            },
            path_tree
                .resolve_node_path(
                    &SlashPath::new(Cow::Borrowed("/one/two/three/four")),
                    match_node_path
                )
                .unwrap()
                .matched_path
        );
        assert_eq!(
            MatchedNodePath::Full {
                number_of_segments: 4
            },
            path_tree
                .resolve_node_path(
                    &SlashPath::new(Cow::Borrowed("/one/two/3/4")),
                    match_node_path
                )
                .unwrap()
                .matched_path
        );
        assert_eq!(
            MatchedNodePath::Full {
                number_of_segments: 5
            },
            path_tree
                .resolve_node_path(
                    &SlashPath::new(Cow::Borrowed("/one/two/three/four/five")),
                    match_node_path
                )
                .unwrap()
                .matched_path
        );
        assert_eq!(
            MatchedNodePath::Full {
                number_of_segments: 5
            },
            path_tree
                .resolve_node_path(
                    &SlashPath::new(Cow::Borrowed("/one/two/3/4/5")),
                    match_node_path
                )
                .unwrap()
                .matched_path
        );
    }

    assert!(path_tree
        .resolve_node_path(
            &SlashPath::new(Cow::Borrowed("/one/two/foo")),
            MatchNodePath::Full
        )
        .is_none());
    assert_eq!(
        MatchedNodePath::Partial {
            number_of_matched_segments: 2.try_into().unwrap()
        },
        path_tree
            .resolve_node_path(
                &SlashPath::new(Cow::Borrowed("/one/two/foo")),
                MatchNodePath::PartialOrFull
            )
            .unwrap()
            .matched_path
    );

    assert!(path_tree
        .resolve_node_path(
            &SlashPath::new(Cow::Borrowed("/one/two/foo/four")),
            MatchNodePath::Full
        )
        .is_none());
    assert_eq!(
        MatchedNodePath::Partial {
            number_of_matched_segments: 2.try_into().unwrap()
        },
        path_tree
            .resolve_node_path(
                &SlashPath::new(Cow::Borrowed("/one/two/foo/four")),
                MatchNodePath::PartialOrFull
            )
            .unwrap()
            .matched_path
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn update_node_value() {
    let mut path_tree = PathTree::new(Default::default(), NodeValue::Inner(-23));

    assert_eq!(1, path_tree.nodes_count());
    assert_eq!(0, path_tree.descendant_nodes_count(path_tree.root_node()));
    assert_eq!(Some(&-23), path_tree.root_node().node.inner_value());

    // Insert a new leaf node with its parent
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(1),
            &mut || -2, // Creates the parent node "/foo" with value -2
            |_| None
        )
        .is_ok());

    assert_eq!(3, path_tree.nodes_count());
    assert_eq!(2, path_tree.descendant_nodes_count(path_tree.root_node()));
    assert!(path_tree
        .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar/baz")))
        .is_none());

    let inner_node_id = path_tree
        .find_node(&SlashPath::new(Cow::Borrowed("/foo")))
        .unwrap()
        .id;
    let leaf_node_id = path_tree
        .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar")))
        .unwrap()
        .id;

    // Update the leaf node value.
    assert_eq!(
        Some(&1),
        path_tree
            .lookup_node(leaf_node_id)
            .unwrap()
            .node
            .leaf_value()
    );
    assert!(path_tree
        .update_node_value(
            &Arc::clone(path_tree.lookup_node(leaf_node_id).unwrap()),
            NodeValue::Leaf(2),
        )
        .is_ok());
    assert_eq!(
        Some(&2),
        path_tree
            .lookup_node(leaf_node_id)
            .unwrap()
            .node
            .leaf_value()
    );

    // Update the inner node value.
    assert_eq!(
        Some(&-2),
        path_tree
            .lookup_node(inner_node_id)
            .unwrap()
            .node
            .inner_value()
    );
    assert!(path_tree
        .update_node_value(
            &Arc::clone(path_tree.lookup_node(inner_node_id).unwrap()),
            NodeValue::Inner(-3),
        )
        .is_ok());
    assert_eq!(
        Some(&-3),
        path_tree
            .lookup_node(inner_node_id)
            .unwrap()
            .node
            .inner_value()
    );

    // Transform the leaf node into an inner node by updating its value.
    assert_eq!(
        Some(&2),
        path_tree
            .lookup_node(leaf_node_id)
            .unwrap()
            .node
            .leaf_value()
    );
    assert!(path_tree
        .update_node_value(
            &Arc::clone(path_tree.lookup_node(leaf_node_id).unwrap()),
            NodeValue::Inner(-4),
        )
        .is_ok());
    assert_eq!(
        Some(&-4),
        path_tree
            .lookup_node(leaf_node_id)
            .unwrap()
            .node
            .inner_value()
    );

    // Transforming an inner node with children into a leaf node should fail.
    assert!(path_tree
        .update_node_value(
            &Arc::clone(path_tree.lookup_node(inner_node_id).unwrap()),
            NodeValue::Leaf(4),
        )
        .is_err());

    // Delete child of inner node.
    path_tree.remove_subtree_by_id(leaf_node_id).unwrap();

    // Transforming an inner node without children into a leaf node should succeed.
    assert_ne!(
        Some(&-4),
        path_tree
            .lookup_node(inner_node_id)
            .unwrap()
            .node
            .inner_value()
    );
    assert!(path_tree
        .update_node_value(
            &Arc::clone(path_tree.lookup_node(inner_node_id).unwrap()),
            NodeValue::Leaf(4),
        )
        .is_ok());
    assert_eq!(
        Some(&4),
        path_tree
            .lookup_node(inner_node_id)
            .unwrap()
            .node
            .leaf_value()
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn insert_or_update_child_node_value_leaf() {
    let mut path_tree = PathTree::new(Default::default(), NodeValue::Inner(-23));

    assert_eq!(1, path_tree.nodes_count());
    assert_eq!(0, path_tree.descendant_nodes_count(path_tree.root_node()));
    assert_eq!(Some(&-23), path_tree.root_node().node.inner_value());

    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(2),
            &mut || -1, // Creates the parent node "/foo" with value -1
            |_| None
        )
        .is_ok());
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/baz")),
            NodeValue::Leaf(3),
            &mut || unreachable!(),
            |_| None
        )
        .is_ok());

    assert_eq!(4, path_tree.nodes_count());

    let leaf_node_id = path_tree
        .find_node(&SlashPath::new(Cow::Borrowed("/foo/bar")))
        .unwrap()
        .id;
    assert_eq!(
        Some(&2),
        path_tree
            .lookup_node(leaf_node_id)
            .unwrap()
            .node
            .leaf_value()
    );

    // Update the value and rename the leaf node.
    let parent_node = Arc::clone(
        path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo")))
            .unwrap(),
    );
    let ChildNodeChangeset {
        new_child_node,
        new_parent_node: _,
        old_child_node,
        removed_subtree,
    } = path_tree
        .insert_or_update_child_node_value(&parent_node, "bar2", Some("bar"), NodeValue::Leaf(4))
        .unwrap();
    assert_eq!(4, path_tree.nodes_count());
    assert_eq!(
        Some(&4),
        path_tree
            .lookup_node(leaf_node_id)
            .unwrap()
            .node
            .leaf_value()
    );
    // Id and children of the updated node have not changed.
    assert_eq!(old_child_node.as_ref().unwrap().id, new_child_node.id);
    assert_eq!(
        old_child_node
            .unwrap()
            .as_ref()
            .node
            .children()
            .collect::<Vec<_>>(),
        new_child_node.node.children().collect::<Vec<_>>()
    );
    // No subtree has been removed.
    assert!(removed_subtree.is_none());

    // Update the value and rename the leaf node again, replacing the node "/foo/baz".
    let replaced_node_path = SlashPath::new(Cow::Borrowed("/foo/baz"));
    let replaced_node_id = path_tree.find_node(&replaced_node_path).unwrap().id;
    let parent_node = Arc::clone(
        path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo")))
            .unwrap(),
    );
    let ChildNodeChangeset {
        new_child_node,
        new_parent_node: _,
        old_child_node,
        removed_subtree,
    } = path_tree
        .insert_or_update_child_node_value(&parent_node, "baz", Some("bar2"), NodeValue::Leaf(5))
        .unwrap();
    assert_eq!(3, path_tree.nodes_count());
    assert_eq!(
        Some(&5),
        path_tree
            .lookup_node(leaf_node_id)
            .unwrap()
            .node
            .leaf_value()
    );
    assert_eq!(
        leaf_node_id,
        path_tree.find_node(&replaced_node_path).unwrap().id
    );
    // Id and children of the updated node have not changed.
    assert_eq!(old_child_node.as_ref().unwrap().id, new_child_node.id);
    assert_eq!(
        old_child_node
            .unwrap()
            .as_ref()
            .node
            .children()
            .collect::<Vec<_>>(),
        new_child_node.node.children().collect::<Vec<_>>()
    );
    // The replaced node becomes the root node of the removed subtree.
    assert!(path_tree.lookup_node(replaced_node_id).is_none());
    assert_eq!(1, removed_subtree.as_ref().unwrap().nodes_count());
    assert_eq!(
        replaced_node_id,
        removed_subtree.as_ref().unwrap().root_node_id()
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn insert_or_update_child_node_value_inner() {
    let mut path_tree = PathTree::new(Default::default(), NodeValue::Inner(-23));

    assert_eq!(1, path_tree.nodes_count());
    assert_eq!(0, path_tree.descendant_nodes_count(path_tree.root_node()));
    assert_eq!(Some(&-23), path_tree.root_node().node.inner_value());

    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/inner")),
            NodeValue::Leaf(2),
            &mut || -1, // Creates the parent node "/foo" with value -1
            |_| None
        )
        .is_ok());
    //
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/inner/leaf")),
            NodeValue::Leaf(42),
            &mut || unreachable!(),
            |value| {
                // Transform the former leaf node into an inner node.
                assert_eq!(2, *value);
                Some(-2)
            }
        )
        .is_ok());
    assert!(path_tree
        .insert_or_update_node_value(
            &SlashPath::new(Cow::Borrowed("/foo/bar")),
            NodeValue::Leaf(3),
            &mut || unreachable!(),
            |_| None
        )
        .is_ok());

    assert_eq!(5, path_tree.nodes_count());

    let inner_node_id = path_tree
        .find_node(&SlashPath::new(Cow::Borrowed("/foo/inner")))
        .unwrap()
        .id;
    assert_eq!(
        Some(&-2),
        path_tree
            .lookup_node(inner_node_id)
            .unwrap()
            .node
            .inner_value()
    );

    // Update the value and rename the inner node.
    let parent_node = Arc::clone(
        path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo")))
            .unwrap(),
    );
    let ChildNodeChangeset {
        new_child_node,
        new_parent_node: _,
        old_child_node,
        removed_subtree,
    } = path_tree
        .insert_or_update_child_node_value(
            &parent_node,
            "inner2",
            Some("inner"),
            NodeValue::Inner(-4),
        )
        .unwrap();
    assert_eq!(5, path_tree.nodes_count());
    assert_eq!(
        Some(&-4),
        path_tree
            .lookup_node(inner_node_id)
            .unwrap()
            .node
            .inner_value()
    );
    // Id and children of the updated node have not changed.
    assert_eq!(old_child_node.as_ref().unwrap().id, new_child_node.id);
    assert_eq!(
        old_child_node
            .unwrap()
            .as_ref()
            .node
            .children()
            .collect::<Vec<_>>(),
        new_child_node.node.children().collect::<Vec<_>>()
    );
    // No subtree has been removed.
    assert!(removed_subtree.is_none());

    // Update the value and rename the inner node again, replacing the node "/foo/bar".
    let replaced_node_path = SlashPath::new(Cow::Borrowed("/foo/bar"));
    let replaced_node_id = path_tree.find_node(&replaced_node_path).unwrap().id;
    let parent_node = Arc::clone(
        path_tree
            .find_node(&SlashPath::new(Cow::Borrowed("/foo")))
            .unwrap(),
    );
    let ChildNodeChangeset {
        new_child_node,
        new_parent_node: _,
        old_child_node,
        removed_subtree,
    } = path_tree
        .insert_or_update_child_node_value(
            &parent_node,
            "bar",
            Some("inner2"),
            NodeValue::Inner(-5),
        )
        .unwrap();
    assert_eq!(4, path_tree.nodes_count());
    assert_eq!(
        Some(&-5),
        path_tree
            .lookup_node(inner_node_id)
            .unwrap()
            .node
            .inner_value()
    );
    assert_eq!(
        inner_node_id,
        path_tree.find_node(&replaced_node_path).unwrap().id
    );
    // Id and children of the updated node have not changed.
    assert_eq!(old_child_node.as_ref().unwrap().id, new_child_node.id);
    assert_eq!(
        old_child_node
            .unwrap()
            .as_ref()
            .node
            .children()
            .collect::<Vec<_>>(),
        new_child_node.node.children().collect::<Vec<_>>()
    );
    // The replaced node becomes the root node of the removed subtree.
    assert!(path_tree.lookup_node(replaced_node_id).is_none());
    assert_eq!(1, removed_subtree.as_ref().unwrap().nodes_count());
    assert_eq!(
        replaced_node_id,
        removed_subtree.as_ref().unwrap().root_node_id()
    );
}
