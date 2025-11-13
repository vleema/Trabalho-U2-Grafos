use crate::graphs::{
    BfsIter, BiconnectedComponentsIter, DfsEdgesIter, DfsIter, DijkstraIter, Edge,
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
pub trait Graph<T>
where
    T: Node,
{
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
    fn node_degrees(&self, n: T) -> (usize, usize);

    /// Returns an iterator over all nodes in the graph.
    ///
    /// The iterator yields each node exactly once.
    fn nodes(&self) -> impl Iterator<Item = T>;

    /// Adds a new node to the graph.
    ///
    /// If the node already exists, this operation has no effect.
    fn add_node(&mut self, n: T);

    /// Removes a node and all edges connected to it.
    ///
    /// If the node does not exist, this operation has no effect.
    fn remove_node(&mut self, n: T);

    /// Adds a **directed edge** from node `n` to node `m`.
    ///
    /// If either node does not exist, this operation has no effect.
    fn add_edge(&mut self, n: T, m: T, w: i32);

    /// Removes a **directed edge** from node `n` to node `m`, if it exists.
    ///
    /// If either node does not exist, this operation has no effect.
    fn remove_edge(&mut self, n: T, m: T, w: Option<i32>);

    type Neighbors<'a>: Iterator<Item = (T, i32)>
    where
        Self: 'a,
        T: 'a;

    /// Returns an iterator over all **neighbors** (adjacent nodes) of a given node.
    ///
    /// # Arguments
    /// * `n` — The node whose outgoing neighbors are to be listed.
    fn neighbors<'a>(&'a self, n: T) -> Option<Self::Neighbors<'a>>;

    /// Checks whether the graph is **bipartite** and returns `true` or `false`
    fn bipartite(&self) -> bool;

    /// Returns the **underlying graph** of the current structure.
    ///
    /// This removes edge directionality, making each edge bidirectional.
    fn underlying_graph(&self) -> Self;

    /// Returns `true` if there is a directed edge from node `n` to node `m`.
    fn has_edge(&self, n: T, m: T) -> bool {
        if let Some(mut neighbors) = self.neighbors(n) {
            neighbors.any(|neighbor| neighbor.0 == m)
        } else {
            false
        }
    }

    /// Returns an iterator that performs a **depth-first search (DFS)** starting from `start`.
    ///
    /// The iterator yields [`DfsEvent`] values that represent the traversal steps.
    fn dfs(&self, start: T) -> DfsIter<'_, T, Self>
    where
        Self: Sized,
    {
        DfsIter::new(self, start)
    }

    /// Returns an iterator that performs a **breadth-first search (BFS)** starting from `start`.
    ///
    /// The iterator yields [`BfsEvent`] values for each level of the search.
    fn bfs(&self, start: T) -> BfsIter<'_, T, Self>
    where
        Self: Sized,
    {
        BfsIter::new(self, start)
    }

    /// Returns an iterator that classifies all edges encountered during a DFS traversal.
    ///
    /// The classification follows standard DFS rules, producing edges of type ['Edge']
    fn classify_edges(&self, start: T) -> DfsEdgesIter<'_, T, Self>
    where
        Self: Sized,
    {
        DfsEdgesIter::new(self, start)
    }

    fn shortest_path_dijkstra(&self, start: T) -> DijkstraIter<'_, T, Self>
    where
        Self: Sized,
    {
        DijkstraIter::new(self, start)
    }
}

/// Trait defining operations for **undirected graphs**.
///
/// Extends [`Graph`], treating each edge as a bidirectional connection `(n <-> m)`.
/// Provides utility methods for manipulation and analysis of undirected graphs,
/// including connectivity checks, biconnected components, and edge classification.
pub trait UndirectedGraph<T>: Graph<T>
where
    T: Node,
{
    /// Returns the total number of **undirected edges** in the graph.
    fn undirected_size(&self) -> usize;

    /// Checks whether the graph is **connected**.
    ///
    /// Returns `true` if there exists a path between every pair of nodes.
    fn connected(&self) -> bool;

    /// Returns an iterator over the **biconnected components** of the graph.
    ///
    /// The traversal starts from the given `start` node.
    fn biconnected_components(&self, start: T) -> BiconnectedComponentsIter<'_, T, Self>
    where
        Self: Sized,
    {
        BiconnectedComponentsIter::new(self, start)
    }

    /// Adds an **undirected edge** `(n <-> m)` to the graph.
    ///
    /// Internally, this adds both directed edges `(n -> m)` and `(m -> n)`.
    fn add_undirected_edge(&mut self, n: T, m: T, w: i32) {
        self.add_edge(n, m, w);
        self.add_edge(m, n, w);
    }

    /// Removes an **undirected edge** `(n <-> m)` from the graph.
    ///
    /// Internally, this removes both directed edges `(n <-> m)` and `(m <-> n)`.
    fn remove_undirected_edge(&mut self, n: T, m: T, w: Option<i32>) {
        self.remove_edge(n, m, w);
        self.remove_edge(m, n, w);
    }

    /// Returns the **degree** of the given node,
    /// considering all undirected connections.
    fn undirected_node_degree(&self, n: T) -> usize {
        match self.neighbors(n) {
            None => 0,
            Some(neighbor) => neighbor.count(),
        }
    }

    /// Returns an iterator classifying the **undirected edges** of the graph.
    ///
    /// Only edges of types [`Edge::Tree`] and [`Edge::Back`] are considered,
    /// as these represent meaningful relations in undirected graphs.
    fn classify_undirected_edges<'a>(&'a self, start: T) -> impl Iterator<Item = Edge<T>>
    where
        Self: Sized,
        T: 'a,
    {
        DfsEdgesIter::new(self, start)
            .filter(|edge| matches!(edge, Edge::Tree(_, _) | Edge::Back(_, _)))
    }
}
