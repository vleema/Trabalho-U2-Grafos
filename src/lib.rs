//! A Rust crate for representing and manipulating graphs using various data structures.
//!
//! This crate provides traits and implementations for directed and undirected graphs,
//! supporting adjacency lists, adjacency matrices, and incidence matrices. It also
//! includes I/O traits for importing and exporting graphs, as well as utility functions
//! for printing and inspecting graph structures.
//!
//! # Modules
//! - `graph`: Core graph traits and BFS/DFS events.
//! - `adjacency_matrix`: Implementation of graphs using adjacency matrices.
mod adjacency_matrix;
mod graph;

pub use graph::BfsEvent;
pub use graph::DfsEvent;
pub use graph::Edge;
pub use graph::Graph;
pub use graph::UndirectedGraph;

pub mod graphs {
    pub use crate::adjacency_matrix::AdjacencyMatrix;
}
