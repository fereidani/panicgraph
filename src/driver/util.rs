//! Shared container aliases.

/// Hash map used throughout the crate.
pub type Map<K, V> = hashbrown::HashMap<K, V>;

/// Hash set used throughout the crate.
pub type Set<T> = hashbrown::HashSet<T>;
