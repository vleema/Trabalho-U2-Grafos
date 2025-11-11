//! A Rust crate for representing and manipulating graphs using various data structures.
mod adjacency_matrix;
mod eulerian_cycle;
mod graph;
mod minimum_spanning_tree;
mod shortest_path;
mod traversal;

pub use graph::Graph;
pub use graph::Node;
pub use graph::UndirectedGraph;

pub mod graphs {
    pub use crate::adjacency_matrix::AdjacencyMatrix;
    pub use crate::shortest_path::DijkstraIter;
    pub use crate::traversal::BfsEvent;
    pub use crate::traversal::BfsIter;
    pub use crate::traversal::BiconnectedComponentsIter;
    pub use crate::traversal::DfsEdgesIter;
    pub use crate::traversal::DfsEvent;
    pub use crate::traversal::DfsIter;
    pub use crate::traversal::Edge;
}
