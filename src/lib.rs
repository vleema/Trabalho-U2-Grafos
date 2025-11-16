//! A Rust crate for representing and manipulating graphs using various data structures.

#![feature(impl_trait_in_assoc_type)]

mod adjacency_list;
mod eulerian_cycle;
mod graph;
mod minimum_spanning_tree;
mod shortest_path;
mod traversal;

pub use graph::Graph;
pub use graph::Node;
pub use graph::UndirectedGraph;
pub use graph::WeightedGraph;

pub mod graphs {
    pub use crate::adjacency_list::AdjacencyList;
    pub use crate::shortest_path::DijkstraResult;
    pub use crate::traversal::BfsEvent;
    pub use crate::traversal::BfsIter;
    pub use crate::traversal::BiconnectedComponentsIter;
    pub use crate::traversal::DfsEdgesIter;
    pub use crate::traversal::DfsEvent;
    pub use crate::traversal::DfsIter;
    pub use crate::traversal::Edge;
}
