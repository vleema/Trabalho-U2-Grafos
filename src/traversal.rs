use crate::graph::Graph;
use crate::graph::Node;
use std::collections::{HashMap, HashSet, VecDeque};

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
pub struct DfsIter<'a, N, G>
where
    N: Node,
    G: Graph<N>,
    Self: 'a,
{
    graph: &'a G,
    stack: Vec<(N, G::Neighbors<'a>)>,
    visited: HashSet<N>,
    start_node: Option<N>,
}

impl<'a, N, G> DfsIter<'a, N, G>
where
    N: Node,
    G: Graph<N>,
{
    /// Creates a new DFS iterator starting from the given node.
    pub fn new(graph: &'a G, start: N) -> Self {
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
    pub fn new_start(&mut self, start: N) {
        self.start_node = Some(start)
    }
}

impl<'a, N, G> Iterator for DfsIter<'a, N, G>
where
    N: Node,
    G: Graph<N>,
{
    type Item = DfsEvent<N>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(start_node) = self.start_node.take()
            && self.visited.insert(start_node)
        {
            self.stack
                .push((start_node, self.graph.neighbors(start_node)));

            return Some(DfsEvent::Discover(start_node, None));
        }

        if let Some((node, mut neighbors)) = self.stack.pop() {
            if let Some(neighbor) = neighbors.next() {
                self.stack.push((node, neighbors));

                if self.visited.insert(neighbor) {
                    self.stack.push((neighbor, self.graph.neighbors(neighbor)));
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
    pub fn new(graph: &'a G, start: T) -> Self {
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

        for n in self.graph.neighbors(node) {
            if self.visited.insert(n) {
                self.queue.push_back(n);
                self.parent.insert(n, Some(node));
                children.push(n);
            } else if Some(node) != self.parent.get(&n).copied().flatten() {
                events.push(BfsEvent::CrossEdge(node, n));
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
    pub fn new(graph: &'a G, start: T) -> Self {
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
    pub fn new(graph: &'a G, start: T) -> Self {
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
mod test {
    /* Uncomment when is implemented
    use super::*;
    use crate::UndirectedGraph;
    use crate::adjacency_matrix::AdjacencyMatrix;

    #[test]
    fn dfs_with_cycle() {
        let mut g = AdjacencyMatrix::default();
        g.add_node(0);
        g.add_node(1);
        g.add_node(2);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 0); // Cycle

        let mut dfs = g.dfs(0);

        assert!(matches!(dfs.next(), Some(DfsEvent::Discover(0, None))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Discover(1, Some(0)))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Discover(2, Some(1)))));
        assert!(matches!(dfs.next(), Some(DfsEvent::NonTreeEdge(2, 0))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Finish(2))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Finish(1))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Finish(0))));
        assert!(dfs.next().is_none());
    }

    #[test]
    fn dfs_simple_path() {
        let mut g = AdjacencyMatrix::default();
        g.add_node(0);
        g.add_node(1);
        g.add_node(2);
        g.add_edge(0, 1);
        g.add_edge(1, 2);

        let mut dfs = g.dfs(0);

        assert!(matches!(dfs.next(), Some(DfsEvent::Discover(0, None))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Discover(1, Some(0)))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Discover(2, Some(1)))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Finish(2))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Finish(1))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Finish(0))));
        assert!(dfs.next().is_none());
    }

    #[test]
    fn single_node_dfs() {
        let mut g = AdjacencyMatrix::default();
        g.add_node(0);

        let mut dfs = g.dfs(0);

        assert!(matches!(dfs.next(), Some(DfsEvent::Discover(0, None))));
        assert!(matches!(dfs.next(), Some(DfsEvent::Finish(0))));
        assert!(dfs.next().is_none());
    }

    #[test]
    fn test_biconnected_components() {
        // 0 -- 1 -- 4
        //    /  \
        //   3 -- 2
        let mut graph = AdjacencyMatrix::default();
        graph.add_node(0);
        graph.add_node(1);
        graph.add_node(2);
        graph.add_node(3);
        graph.add_node(4);
        graph.add_undirected_edge(1, 4);
        graph.add_undirected_edge(0, 1);
        graph.add_undirected_edge(1, 2);
        graph.add_undirected_edge(1, 3);
        graph.add_undirected_edge(2, 3);

        let components: Vec<Vec<(usize, usize)>> = graph.biconnected_components(0).collect();

        assert_eq!(components.len(), 3);
        assert!(components.contains(&vec![(1, 4)]));
        assert!(components.contains(&vec![(3, 1), (2, 3), (1, 2)]));
        assert!(components.contains(&vec![(0, 1)]));
    }
    */
}
