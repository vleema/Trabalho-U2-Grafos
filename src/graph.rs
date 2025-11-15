use num_traits::{Bounded, CheckedAdd, One, Zero};

use crate::{
    graphs::{BfsIter, BiconnectedComponentsIter, DfsEdgesIter, DfsIter, DijkstraIter, Edge},
    shortest_path::FloydWarshallResult,
};
use std::hash::Hash;

pub trait Node: Eq + Hash + Copy {}

impl<T> Node for T where T: Eq + Hash + Copy {}

/// Defines a generic interface for a graph data structure.
///
/// The [`Graph`] trait represents a **directed graph**, where each node can have
/// zero or more outgoing edges to other nodes.
/// It defines the essential operations for graph construction, traversal, and analysis.
///
/// Types implementing this trait can represent any kind of graph structure, such as
/// adjacency lists, adjacency matrices, ...
///
/// # Type Parameters
/// - `Node`: The type used to represent graph nodes.
///   Must implement [`Eq`], [`Hash`], and [`Copy`] to ensure efficient lookups.
pub trait Graph<N: Node> {
    /// Returns the number of nodes (vertices) in the graph.
    fn order(&self) -> usize;

    /// Returns the number of edges in the graph.
    ///
    /// This includes all directed edges, so in a directed graph,
    /// an edge `(u, v)` counts as a single edge.
    fn size(&self) -> usize;

    /// Returns the **in-degree** and **out-degree** of a given node.
    ///
    /// # Arguments
    /// * `n` — The node whose degrees are being queried.
    ///
    /// # Returns
    /// A tuple `(usize, usize)` where:
    /// - The first element is the number of **incoming** edges.
    /// - The second element is the number of **outgoing** edges.
    fn node_degrees(&self, n: N) -> (usize, usize);

    /// Returns an iterator over all nodes in the graph.
    ///
    /// The iterator yields each node exactly once.
    fn nodes(&self) -> impl Iterator<Item = N>;

    /// Adds a new node to the graph.
    ///
    /// If the node already exists, this operation has no effect.
    fn add_node(&mut self, n: N);

    /// Removes a node and all edges connected to it.
    ///
    /// If the node does not exist, this operation has no effect.
    fn remove_node(&mut self, n: N);

    /// Adds a **directed edge** from node `n` to node `m`.
    ///
    /// If either node does not exist, this operation has no effect.
    fn add_edge(&mut self, n: N, m: N);

    /// Removes a **directed edge** from node `n` to node `m`, if it exists.
    ///
    /// If either node does not exist, this operation has no effect.
    fn remove_edge(&mut self, n: N, m: N);

    type Neighbors<'a>: Iterator<Item = N>
    where
        Self: 'a;

    /// Returns an iterator over all **neighbors** (adjacent nodes) of a given node.
    ///
    /// # Arguments
    /// * `n` — The node whose outgoing neighbors are to be listed.
    fn neighbors(&self, n: N) -> Self::Neighbors<'_>;

    /// Checks whether the graph is **bipartite** and returns `true` or `false`
    fn bipartite(&self) -> bool;

    /// Returns the **underlying graph** of the current structure.
    ///
    /// This removes edge directionality, making each edge bidirectional.
    fn underlying_graph(&self) -> Self;

    /// Returns `true` if there is a directed edge from node `n` to node `m`.
    fn has_edge(&self, n: N, m: N) -> bool {
        self.neighbors(n).any(|neighbor| neighbor == m)
    }

    /// Returns an iterator that performs a **depth-first search (DFS)** starting from `start`.
    ///
    /// The iterator yields [`DfsEvent`] values that represent the traversal steps.
    fn dfs(&self, start: N) -> DfsIter<'_, N, Self> {
        DfsIter::new(self, start)
    }

    /// Returns an iterator that performs a **breadth-first search (BFS)** starting from `start`.
    ///
    /// The iterator yields [`BfsEvent`] values for each level of the search.
    fn bfs(&self, start: N) -> BfsIter<'_, N, Self> {
        BfsIter::new(self, start)
    }

    /// Returns an iterator that classifies all edges encountered during a DFS traversal.
    ///
    /// The classification follows standard DFS rules, producing edges of type ['Edge']
    fn classify_edges(&self, start: N) -> DfsEdgesIter<'_, N, Self> {
        DfsEdgesIter::new(self, start)
    }
}

/// Trait defining operations for **undirected graphs**.
///
/// Extends [`Graph`], treating each edge as a bidirectional connection `(n <-> m)`.
/// Provides utility methods for manipulation and analysis of undirected graphs,
/// including connectivity checks, biconnected components, and edge classification.
pub trait UndirectedGraph<N: Node>: Graph<N> {
    /// Returns the total number of **undirected edges** in the graph.
    fn undirected_size(&self) -> usize;

    /// Checks whether the graph is **connected**.
    ///
    /// Returns `true` if there exists a path between every pair of nodes.
    fn connected(&self) -> bool;

    /// Returns an iterator over the **biconnected components** of the graph.
    ///
    /// The traversal starts from the given `start` node.
    fn biconnected_components(&self, start: N) -> BiconnectedComponentsIter<'_, N, Self> {
        BiconnectedComponentsIter::new(self, start)
    }

    /// Adds an **undirected edge** `(n <-> m)` to the graph.
    ///
    /// Internally, this adds both directed edges `(n -> m)` and `(m -> n)`.
    fn add_undirected_edge(&mut self, n: N, m: N) {
        self.add_edge(n, m);
        self.add_edge(m, n);
    }

    /// Removes an **undirected edge** `(n <-> m)` from the graph.
    ///
    /// Internally, this removes both directed edges `(n <-> m)` and `(m <-> n)`.
    fn remove_undirected_edge(&mut self, n: N, m: N) {
        self.remove_edge(n, m);
        self.remove_edge(m, n);
    }

    /// Returns the **degree** of the given node,
    /// considering all undirected connections.
    fn undirected_node_degree(&self, n: N) -> usize {
        self.neighbors(n).count()
    }

    /// Returns an iterator classifying the **undirected edges** of the graph.
    ///
    /// Only edges of types [`Edge::Tree`] and [`Edge::Back`] are considered,
    /// as these represent meaningful relations in undirected graphs.
    fn classify_undirected_edges<'a>(&'a self, start: N) -> impl Iterator<Item = Edge<N>>
    where
        N: 'a,
    {
        DfsEdgesIter::new(self, start)
            .filter(|edge| matches!(edge, Edge::Tree(_, _) | Edge::Back(_, _)))
    }

    fn minimum_spanning_tree_kruskal(
        &self,
    ) -> crate::minimum_spanning_tree::KruskalIter<'_, N, Self>
    where
        N: Ord,
        Self: WeightedGraph<N, i32>,
    {
        crate::minimum_spanning_tree::KruskalIter::new(self)
    }

    fn minimum_spanning_tree_prim(&self) -> crate::minimum_spanning_tree::PrimIter<'_, N, Self>
    where
        N: Ord,
        Self: WeightedGraph<N, i32>,
    {
        crate::minimum_spanning_tree::PrimIter::new(self)
    }
}

pub trait Weight: CheckedAdd + Ord + Bounded + Zero + One + Copy {}

impl<T> Weight for T where T: CheckedAdd + Ord + Bounded + One + Zero + Copy {}

pub trait WeightedGraph<N: Node, W: Weight>: Graph<N> {
    type WeightedNeighbors<'a>: Iterator<Item = (N, W)>
    where
        Self: 'a;
    fn weighted_neighbors(&self, n: N) -> Self::WeightedNeighbors<'_>;

    fn add_weighted_edge(&mut self, n: N, m: N, w: W);

    fn djikstra(&self, start: N) -> DijkstraIter<'_, N, W, Self> {
        DijkstraIter::new(self, start)
    }

    fn floyd_warshall(&self) -> FloydWarshallResult<N, W> {
        FloydWarshallResult::new(self)
    }
}
