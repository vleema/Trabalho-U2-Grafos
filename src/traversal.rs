use crate::graph::Graph;
use crate::graph::Node;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Debug)]
pub enum DfsEvent<T>
where
    T: Node,
{
    Discover(T, Option<T>),
    Finish(T),
    NonTreeEdge(T, T),
}

pub struct DfsIter<'a, N, G>
where
    N: Node,
    G: Graph<N> + ?Sized,
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
    G: Graph<N> + ?Sized,
{
    pub fn new(graph: &'a G, start: N) -> Self {
        Self {
            graph,
            stack: vec![],
            visited: HashSet::with_capacity(graph.order()),
            start_node: Some(start),
        }
    }

    pub fn new_start(&mut self, start: N) {
        self.start_node = Some(start)
    }
}

impl<'a, N, G> Iterator for DfsIter<'a, N, G>
where
    N: Node,
    G: Graph<N> + ?Sized,
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

#[derive(Debug)]
pub enum BfsEvent<N>
where
    N: Node,
{
    Discover(N, Vec<N>),
    CrossEdge(N, N),
}

pub struct BfsIter<'a, N, G>
where
    N: Node,
    G: Graph<N> + ?Sized,
{
    graph: &'a G,
    queue: VecDeque<N>,
    visited: HashSet<N>,
    parent: HashMap<N, Option<N>>,
}

impl<'a, N, G> BfsIter<'a, N, G>
where
    N: Node,
    G: Graph<N> + ?Sized,
{
    pub fn new(graph: &'a G, start: N) -> Self {
        let mut visited = HashSet::with_capacity(graph.order());
        visited.insert(start);

        let mut parent: HashMap<N, Option<N>> = HashMap::with_capacity(graph.order());
        parent.insert(start, None);

        Self {
            graph,
            queue: VecDeque::from(vec![start]),
            visited,
            parent,
        }
    }
}

impl<'a, N, G> Iterator for BfsIter<'a, N, G>
where
    N: Node,
    G: Graph<N> + ?Sized,
{
    type Item = Vec<BfsEvent<N>>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.queue.pop_front()?;
        let mut children: Vec<N> = Vec::new();
        let mut events: Vec<BfsEvent<N>> = Vec::new();

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

#[derive(Debug)]
pub enum Edge<N>
where
    N: Node,
{
    Tree(N, N),
    Back(N, N),
    ParentBack(N, N),
    Forward(N, N),
    Cross(N, N),
}

pub struct DfsEdgesIter<'a, N, G>
where
    N: Node,
    G: Graph<N> + ?Sized,
    Self: 'a,
{
    iter: DfsIter<'a, N, G>,
    time: usize,
    discovery: HashMap<N, usize>,
    finish: HashMap<N, usize>,
    parent: HashMap<N, N>,
    stack_hash: HashSet<N>,
}

impl<'a, N, G> DfsEdgesIter<'a, N, G>
where
    N: Node,
    G: Graph<N> + ?Sized,
{
    pub fn new(graph: &'a G, start: N) -> Self {
        Self {
            iter: DfsIter::new(graph, start),
            time: 0,
            discovery: HashMap::with_capacity(graph.order()),
            finish: HashMap::with_capacity(graph.order()),
            parent: HashMap::with_capacity(graph.order()),
            stack_hash: HashSet::with_capacity(graph.order()),
        }
    }

    pub fn new_start(&mut self, start: N) {
        self.iter.new_start(start);
    }
}

impl<'a, N, G> Iterator for DfsEdgesIter<'a, N, G>
where
    N: Node,
    G: Graph<N> + ?Sized,
{
    type Item = Edge<N>;

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

pub struct BiconnectedComponentsIter<'a, T, G>
where
    T: Node,
    G: Graph<T> + ?Sized,
    Self: 'a,
{
    iter: DfsIter<'a, T, G>,
    time: usize,
    discovery: HashMap<T, usize>,
    lowpt: HashMap<T, usize>,
    parents: HashMap<T, T>,
    edge_stack: Vec<(T, T)>,
}

impl<'a, N, G> BiconnectedComponentsIter<'a, N, G>
where
    N: Node,
    G: Graph<N> + 'a + ?Sized,
{
    pub fn new(graph: &'a G, start: N) -> Self {
        Self {
            iter: graph.dfs(start),
            time: 0,
            discovery: HashMap::with_capacity(graph.order()),
            lowpt: HashMap::with_capacity(graph.order()),
            parents: HashMap::with_capacity(graph.order()),
            edge_stack: Vec::with_capacity(graph.order()),
        }
    }

    fn extract_component(&mut self, u: N, v: N) -> Option<Vec<(N, N)>> {
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

impl<'a, N, G> Iterator for BiconnectedComponentsIter<'a, N, G>
where
    N: Node,
    G: Graph<N> + ?Sized,
{
    type Item = Vec<(N, N)>;

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
