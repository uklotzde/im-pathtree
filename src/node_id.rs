// SPDX-FileCopyrightText: The im-pathtree authors
// SPDX-License-Identifier: MPL-2.0

use std::{
    num::NonZeroUsize,
    sync::atomic::{AtomicUsize, Ordering},
};

const ZERO_NODE_ID_VALUE: usize = 0;

static LAST_NODE_ID_VALUE: AtomicUsize = AtomicUsize::new(ZERO_NODE_ID_VALUE);

/// Fast, ephemeral node identifier.
///
/// Unique across all in-memory nodes within a single process. Identifiers
/// are re-generated and assigned when the process is restarted and must
/// not be stored permanently!
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, derive_more::Display)]
pub struct NodeId(NonZeroUsize);

impl NodeId {
    /// Generate a new, unique identifier.
    ///
    /// Only the first [`usize::MAX`] identifiers are guaranteed to be unique.
    /// All following identifiers will be duplicates of previous ones.
    ///
    /// The node IDs are unique within a single process, even across multiple trees.
    /// Different nodes always have different IDs, no matter if they are in the same
    /// tree or not.
    ///
    /// ```
    /// # use im_pathtree::NodeId;
    /// let foo_id = NodeId::new();
    /// let bar_id = NodeId::new();
    /// assert_ne!(foo_id, bar_id);
    /// ```
    #[allow(clippy::new_without_default)] // Prevent unintended generation of new identifiers
    pub fn new() -> Self {
        loop {
            // No memory ordering guarantees when invoking this function.
            // We only need to ensure that the next value is unique.
            let last_value = LAST_NODE_ID_VALUE.fetch_add(1, Ordering::Relaxed);
            // fetch_add() performs a wrapping add, so we need to do the same
            let next_value = last_value.wrapping_add(1);
            if let Some(next_value) = NonZeroUsize::new(next_value) {
                return Self(next_value);
            }
            // Looping happens only on overflow and at most once during each call.
            // It is almost impossible that multiple overflows occur in a row during
            // a single call.
        }
    }
}
