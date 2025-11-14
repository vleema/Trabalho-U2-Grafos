use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;

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
pub trait Node: Eq + Hash + Copy {}
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
    fn add_edge(&mut self, n: T, m: T);

    /// Removes a **directed edge** from node `n` to node `m`, if it exists.
    ///
    /// If either node does not exist, this operation has no effect.
    fn remove_edge(&mut self, n: T, m: T);

    type Neighbors<'a>: Iterator<Item = T>
    where
        Self: 'a,
        T: 'a;

    /// Returns an iterator over all **neighbors** (adjacent nodes) of a given node.
    ///
    /// # Arguments
    /// * `n` — The node whose outgoing neighbors are to be listed.
    fn neighbors<'a>(&'a self, n: T) -> Option<Self::Neighbors<'a>>;

    type WeightedNeighbors<'a>: Iterator<Item = (T, i32)>
    where
        Self: 'a,
        T: 'a;

    /// Returns an iterator over all **neighbors** (adjacent nodes) of a given node.
    ///
    /// # Arguments
    /// * `n` — The node whose outgoing neighbors are to be listed.
    fn weighted_neighbors<'a>(&'a self, n: T) -> Option<Self::WeightedNeighbors<'a>>;

    /// Checks whether the graph is **bipartite** and returns `true` or `false`
    fn bipartite(&self) -> bool;

    /// Returns the **underlying graph** of the current structure.
    ///
    /// This removes edge directionality, making each edge bidirectional.
    fn underlying_graph(&self) -> Self;

    /// Returns `true` if there is a directed edge from node `n` to node `m`.
    fn has_edge(&self, n: T, m: T) -> bool {
        if let Some(mut neighbors) = self.neighbors(n) {
            neighbors.any(|neighbor| neighbor == m)
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
    fn add_undirected_edge(&mut self, n: T, m: T) {
        self.add_edge(n, m);
        self.add_edge(m, n);
    }

    /// Removes an **undirected edge** `(n <-> m)` from the graph.
    ///
    /// Internally, this removes both directed edges `(n <-> m)` and `(m <-> n)`.
    fn remove_undirected_edge(&mut self, n: T, m: T) {
        self.remove_edge(n, m);
        self.remove_edge(m, n);
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

/// Represents an event that occurs during a depth-first search (DFS) traversal.
///
/// This enum is used to describe the different types of events that can be
/// encountered while performing DFS on a graph. It is generic over the `Node`
/// type, which represents the nodes in the graph.
///
/// # Variants
/// - `Discover(Node, Option<Node>)`: Indicates that a node has been discovered for the first time.
///   The `Option<Node>` represents the parent node in the DFS tree (`None` for the start node).
/// - `Finish(Node)`: Indicates that all descendants of a node have been visited and the node is finished.
/// - `NonTreeEdge(Node, Node)`: Indicates that a non-tree edge (back, forward, or cross edge) is found
///   from the first node to the second node.
#[derive(Debug)]
pub enum DfsEvent<T>
where
    T: Node,
{
    Discover(T, Option<T>),
    Finish(T),
    NonTreeEdge(T, T),
}

/// Represents a iterator over a depth-first-search (DFS) traversal.
///
/// The iteration yields a `DfsEvent<Node>` over each instance of `next`.
pub struct DfsIter<'a, T, G>
where
    G: Graph<T>,
    T: Node,
    Self: 'a,
{
    graph: &'a G,
    stack: Vec<(T, G::Neighbors<'a>)>,
    visited: HashSet<T>,
    start_node: Option<T>,
}

impl<'a, T, G> DfsIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
{
    /// Creates a new DFS iterator starting from the given node.
    fn new(graph: &'a G, start: T) -> Self {
        Self {
            graph,
            stack: vec![],
            visited: HashSet::with_capacity(graph.order()),
            start_node: Some(start),
        }
    }

    /// Sets the `start_node` field of a `DfsIter` manually.
    ///
    /// This enables starting another DFS while maintains the inner parts of the iterator
    /// initialized, like the `visited` dictionary.
    pub fn new_start(&mut self, start: T) {
        self.start_node = Some(start)
    }
}

impl<'a, T, G> Iterator for DfsIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
{
    type Item = DfsEvent<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(start_node) = self.start_node.take()
            && self.visited.insert(start_node)
        {
            self.stack
                .push((start_node, self.graph.neighbors(start_node).unwrap())); // TODO: remove
            // unwrap later

            return Some(DfsEvent::Discover(start_node, None));
        }

        if let Some((node, mut neighbors)) = self.stack.pop() {
            if let Some(neighbor) = neighbors.next() {
                self.stack.push((node, neighbors));

                if self.visited.insert(neighbor) {
                    self.stack
                        .push((neighbor, self.graph.neighbors(neighbor).unwrap()));
                    return Some(DfsEvent::Discover(neighbor, Some(node)));
                } else {
                    return Some(DfsEvent::NonTreeEdge(node, neighbor));
                }
            } else {
                return Some(DfsEvent::Finish(node));
            }
        }

        None
    }
}

/// Represents an event during a breadth-first search (BFS).
///
/// This enum is used to describe the different types of events that can be
/// encountered while performing DFS on a graph. It is generic over the `Node`
/// type, which represents the nodes in the graph.
///
/// # Variants
/// - `Discover(Node, Vec<Node>)`: Indicates that a node has been discovered for the first time.
///   The `Vec<Node>` represents the node's neighbors that will be explored on BFS tree.
/// - `CrossEdge(Node, Node)`: Indicates that a node has an edge to another and neither is an ancestor of the other.
#[derive(Debug)]
pub enum BfsEvent<T>
where
    T: Node,
{
    Discover(T, Vec<T>),
    CrossEdge(T, T),
}

/// Represents a iterator over a breadth-first-search (BFS) traversal.
///
/// The iteration yields a `BfsEvent<Node>` over each instance of `next`.
pub struct BfsIter<'a, T, G>
where
    T: Node,
{
    graph: &'a G,
    queue: VecDeque<T>,
    visited: HashSet<T>,
    parent: HashMap<T, Option<T>>,
}

impl<'a, T, G> BfsIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
{
    /// Creates a new BFS iterator starting from the given node.
    fn new(graph: &'a G, start: T) -> Self {
        let mut visited = HashSet::with_capacity(graph.order());
        visited.insert(start);

        let mut parent: HashMap<T, Option<T>> = HashMap::with_capacity(graph.order());
        parent.insert(start, None);

        Self {
            graph,
            queue: VecDeque::from(vec![start]),
            visited,
            parent,
        }
    }
}

impl<'a, T, G> Iterator for BfsIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
{
    type Item = Vec<BfsEvent<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.queue.pop_front()?;
        let mut children: Vec<T> = Vec::new();
        let mut events: Vec<BfsEvent<T>> = Vec::new();

        match self.graph.neighbors(node) {
            None => {}
            Some(neighbors) => {
                for n in neighbors {
                    if self.visited.insert(n) {
                        self.queue.push_back(n);
                        self.parent.insert(n, Some(node));
                        children.push(n);
                    } else if Some(node) != self.parent.get(&n).copied().flatten() {
                        events.push(BfsEvent::CrossEdge(node, n));
                    }
                }
            }
        }

        events.push(BfsEvent::Discover(node, children));
        Some(events)
    }
}

/// Represents the classification of an edge in a graph during a depth-first search (DFS).
///
/// This enum is used to categorize edges based on the DFS traversal. It is generic
/// over the `Node` type, which represents the nodes in the graph. The classification
/// is based on the relationship between the two nodes connected by the edge in the DFS tree.
///
/// # Variants
/// - `Tree(u, v)`: An edge from a parent `u` to a child `v` in the DFS tree.
/// - `Back(u, v)`: An edge from a node `u` to its ancestor `v` in the DFS tree. This indicates a cycle.
/// - `ParentBack(u, v)`: A special case of a back edge where `v` is the direct parent of `u`.
///   This is common in undirected graphs.
/// - `Forward(u, v)`: An edge from a node `u` to its descendant `v` that is not a tree edge.
/// - `Cross(u, v)`: An edge between two nodes `u` and `v` such that neither is an ancestor of the other.
#[derive(Debug)]
pub enum Edge<T>
where
    T: Node,
{
    Tree(T, T),
    Back(T, T),
    ParentBack(T, T),
    Forward(T, T),
    Cross(T, T),
}

/// An iterator that performs a depth-first search (DFS) and classifies the edges of the graph.
///
/// This iterator wraps a `DfsIter` and uses its events to classify each edge of the
/// graph into one of the categories defined by the `Edge` enum. It yields an `Edge<Node>`
/// for each edge encountered during the traversal.
pub struct DfsEdgesIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
    Self: 'a,
{
    iter: DfsIter<'a, T, G>,
    time: usize,
    discovery: HashMap<T, usize>,
    finish: HashMap<T, usize>,
    parent: HashMap<T, T>,
    stack_hash: HashSet<T>,
}

impl<'a, T, G> DfsEdgesIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
{
    /// Creates a new DFS-with-edges iterator starting from the given node.
    fn new(graph: &'a G, start: T) -> Self {
        Self {
            iter: DfsIter::new(graph, start),
            time: 0,
            discovery: HashMap::with_capacity(graph.order()),
            finish: HashMap::with_capacity(graph.order()),
            parent: HashMap::with_capacity(graph.order()),
            stack_hash: HashSet::with_capacity(graph.order()),
        }
    }

    /// Sets the `start_node` field of the inner `DfsIter` manually.
    ///
    /// This enables classifying edges from another components of a graph.
    pub fn new_start(&mut self, start: T) {
        self.iter.new_start(start);
    }
}

impl<'a, T, G> Iterator for DfsEdgesIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
{
    type Item = Edge<T>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(event) = self.iter.next() {
            match event {
                DfsEvent::Discover(node, maybe_parent) => {
                    self.stack_hash.insert(node);
                    self.discovery.insert(node, self.time);
                    self.time += 1;
                    if let Some(parent) = maybe_parent {
                        self.parent.insert(node, parent);
                        return Some(Edge::Tree(parent, node));
                    }
                }
                DfsEvent::Finish(node) => {
                    self.stack_hash.remove(&node);
                    self.finish.insert(node, self.time);
                    self.time += 1;
                }
                DfsEvent::NonTreeEdge(node, neighbor) => {
                    if self.stack_hash.contains(&neighbor) {
                        if self
                            .parent
                            .get(&node)
                            .is_some_and(|&parent| parent == neighbor)
                        {
                            return Some(Edge::ParentBack(node, neighbor));
                        } else {
                            return Some(Edge::Back(node, neighbor));
                        }
                    } else if self
                        .discovery
                        .get(&node)
                        .is_some_and(|t1| self.discovery.get(&neighbor).is_some_and(|t2| t1 < t2))
                    {
                        return Some(Edge::Forward(node, neighbor));
                    } else {
                        return Some(Edge::Cross(node, neighbor));
                    }
                }
            }
        }
        None
    }
}

/// An iterator that yields the biconnected components of a undirected graph (`UndirectedGraph`).
///
/// The iterator identifies the biconnected components during a depth-first-search (DFS) that's
/// made by a inner iterator, a `DfsIter`.
pub struct BiconnectedComponentsIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
    Self: 'a,
{
    iter: DfsIter<'a, T, G>,
    time: usize,
    discovery: HashMap<T, usize>,
    lowpt: HashMap<T, usize>,
    parents: HashMap<T, T>,
    edge_stack: Vec<(T, T)>,
}

impl<'a, T, G> BiconnectedComponentsIter<'a, T, G>
where
    T: Node,
    G: Graph<T> + 'a,
{
    /// Creates a new iterator over the biconnected components of an undirected graph
    fn new(graph: &'a G, start: T) -> Self {
        Self {
            iter: graph.dfs(start),
            time: 0,
            discovery: HashMap::with_capacity(graph.order()),
            lowpt: HashMap::with_capacity(graph.order()),
            parents: HashMap::with_capacity(graph.order()),
            edge_stack: Vec::with_capacity(graph.order()),
        }
    }

    /// Extracts a biconnected component from the edge stack.
    fn extract_component(&mut self, u: T, v: T) -> Option<Vec<(T, T)>> {
        let mut component = Vec::new();
        while let Some(edge) = self.edge_stack.pop() {
            component.push(edge);
            if edge == (u, v) || edge == (v, u) {
                break;
            }
        }
        Some(component)
    }
}

impl<'a, T, G> Iterator for BiconnectedComponentsIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
{
    type Item = Vec<(T, T)>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(event) = self.iter.next() {
            match event {
                DfsEvent::Discover(node, maybe_parent) => {
                    self.discovery.insert(node, self.time);
                    self.lowpt.insert(node, self.time);
                    self.time += 1;
                    if let Some(parent) = maybe_parent {
                        self.edge_stack.push((parent, node));
                        self.parents.insert(node, parent);
                    }
                }
                DfsEvent::Finish(node) => {
                    if let Some(&parent) = self.parents.get(&node) {
                        let &node_low = self.lowpt.get(&node).unwrap();
                        let parent_low = self.lowpt.get_mut(&parent).unwrap();

                        *parent_low = (*parent_low).min(node_low);

                        if self.discovery[&parent] <= self.lowpt[&node] {
                            return self.extract_component(parent, node);
                        }
                    } else if !self.edge_stack.is_empty() {
                        return Some(std::mem::take(&mut self.edge_stack));
                    }
                }
                DfsEvent::NonTreeEdge(u, v) => {
                    if Some(&v) != self.parents.get(&u) && self.discovery[&v] < self.discovery[&u] {
                        self.edge_stack.push((u, v));
                        self.lowpt
                            .entry(u)
                            .and_modify(|u_low| *u_low = (*u_low).min(self.discovery[&v]));
                    }
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod test {}
