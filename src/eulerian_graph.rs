use crate::graph::Node;
use crate::graphs::AdjacencyList;
use std::collections::HashMap;

pub struct HierholzerResult<N: Node> {
    pub path: Vec<N>,
    pub has_eulerian_cycle: bool,
    pub has_eulerian_path: bool,
}

pub trait Graph<N: Node> {
    fn nodes(&self) -> impl Iterator<Item = N>;
    fn neighbors(&self, node: N) -> impl Iterator<Item = N>;
    fn is_directed(&self) -> bool;
}

impl<N, W> Graph<N> for AdjacencyList<N, W>
where
    N: Node,
    W: crate::graph::Weight,
{
    fn nodes(&self) -> impl Iterator<Item = N> {
        self.0.keys().copied().collect::<Vec<_>>().into_iter()
    }

    fn neighbors(&self, node: N) -> impl Iterator<Item = N> {
        self.0
            .get(&node)
            .map(|neighbors| neighbors.iter().map(|&(n, _)| n).collect::<Vec<_>>())
            .unwrap_or_default()
            .into_iter()
    }

    fn is_directed(&self) -> bool {
        true
    }
}

pub fn hierholzer<N, G>(graph: &G) -> HierholzerResult<N>
where
    N: Node,
    G: Graph<N>,
{
    let is_directed = graph.is_directed();
    let (out_degree, in_degree) = calculate_degrees(graph);

    let (start_node, has_eulerian_path, has_eulerian_cycle) =
        check_eulerian_conditions(&out_degree, &in_degree, is_directed);

    if !has_eulerian_path && !has_eulerian_cycle {
        return HierholzerResult {
            path: Vec::new(),
            has_eulerian_cycle: false,
            has_eulerian_path: false,
        };
    }

    let mut edge_count = create_edge_count(graph);
    let mut stack = Vec::new();
    let mut path = Vec::new();

    stack.push(start_node);

    while let Some(current_vertex) = stack.last().copied() {
        if let Some(neighbors) = edge_count.get_mut(&current_vertex)
            && let Some((&next_vertex, count)) = neighbors.iter_mut().find(|(_, count)| **count > 0)
            {
                *count -= 1;

                if !is_directed
                    && let Some(rev_neighbors) = edge_count.get_mut(&next_vertex)
                        && let Some(rev_count) = rev_neighbors.get_mut(&current_vertex) {
                            *rev_count -= 1;
                        }

                stack.push(next_vertex);
                continue;
            }

        if let Some(vertex) = stack.pop() {
            path.push(vertex);
        }
    }
    path.reverse();

    let total_edges: usize = if is_directed {
        out_degree.values().sum()
    } else {
        out_degree.values().sum::<usize>() / 2
    };

    let valid_path = path.len() == total_edges + 1;

    HierholzerResult {
        path: if valid_path { path } else { Vec::new() },
        has_eulerian_cycle: valid_path && has_eulerian_cycle,
        has_eulerian_path: valid_path && has_eulerian_path,
    }
}

fn calculate_degrees<N: Node, G: Graph<N>>(graph: &G) -> (HashMap<N, usize>, HashMap<N, usize>) {
    let mut out_degree = HashMap::new();
    let mut in_degree = HashMap::new();

    for node in graph.nodes() {
        out_degree.insert(node, 0);
        in_degree.insert(node, 0);
    }

    for node in graph.nodes() {
        let neighbors_count = graph.neighbors(node).count();
        out_degree.insert(node, neighbors_count);

        if graph.is_directed() {
            for neighbor in graph.neighbors(node) {
                *in_degree.entry(neighbor).or_insert(0) += 1;
            }
        }
    }

    if !graph.is_directed() {
        for node in graph.nodes() {
            in_degree.insert(node, out_degree[&node]);
        }
    }

    (out_degree, in_degree)
}

fn create_edge_count<N: Node, G: Graph<N>>(graph: &G) -> HashMap<N, HashMap<N, usize>> {
    let mut edge_count = HashMap::new();

    for node in graph.nodes() {
        let mut neighbor_counts = HashMap::new();
        for neighbor in graph.neighbors(node) {
            *neighbor_counts.entry(neighbor).or_insert(0) += 1;
        }
        edge_count.insert(node, neighbor_counts);
    }

    edge_count
}

fn check_eulerian_conditions<N: Node>(
    out_degree: &HashMap<N, usize>,
    in_degree: &HashMap<N, usize>,
    is_directed: bool,
) -> (N, bool, bool) {
    let nodes: Vec<N> = out_degree.keys().copied().collect();

    if nodes.is_empty() {
        panic!("Graph has no nodes");
    }

    if is_directed {
        check_directed_eulerian(out_degree, in_degree, &nodes)
    } else {
        check_undirected_eulerian(out_degree, &nodes)
    }
}

fn check_directed_eulerian<N: Node>(
    out_degree: &HashMap<N, usize>,
    in_degree: &HashMap<N, usize>,
    nodes: &[N],
) -> (N, bool, bool) {
    let mut start_candidate = None;
    let mut end_candidate = None;
    let mut balanced_nodes = 0;
    let mut total_nodes_with_edges = 0;

    for &node in nodes {
        let out = out_degree.get(&node).copied().unwrap_or(0);
        let inn = in_degree.get(&node).copied().unwrap_or(0);

        if out == 0 && inn == 0 {
            continue;
        }

        total_nodes_with_edges += 1;

        if out == inn {
            balanced_nodes += 1;
        } else if out == inn + 1 {
            if start_candidate.is_some() {
                return (nodes[0], false, false);
            }
            start_candidate = Some(node);
        } else if inn == out + 1 {
            if end_candidate.is_some() {
                return (nodes[0], false, false);
            }
            end_candidate = Some(node);
        } else {
            return (nodes[0], false, false);
        }
    }

    if balanced_nodes == total_nodes_with_edges {
        let start = nodes
            .iter()
            .find(|&&n| out_degree.get(&n).copied().unwrap_or(0) > 0)
            .copied()
            .unwrap_or(nodes[0]);
        (start, true, true)
    } else if start_candidate.is_some()
        && end_candidate.is_some()
        && balanced_nodes == total_nodes_with_edges - 2
    {
        (start_candidate.unwrap(), true, false)
    } else {
        (nodes[0], false, false)
    }
}

fn check_undirected_eulerian<N: Node>(
    out_degree: &HashMap<N, usize>,
    nodes: &[N],
) -> (N, bool, bool) {
    let mut odd_degree_nodes = Vec::new();

    for &node in nodes {
        let degree = out_degree.get(&node).copied().unwrap_or(0);
        if degree > 0 && degree % 2 != 0 {
            odd_degree_nodes.push(node);
        }
    }

    match odd_degree_nodes.len() {
        0 => {
            let start = nodes
                .iter()
                .find(|&&n| out_degree.get(&n).copied().unwrap_or(0) > 0)
                .copied()
                .unwrap_or(nodes[0]);
            (start, true, true)
        }
        2 => (odd_degree_nodes[0], true, false),
        _ => (nodes[0], false, false),
    }
}

pub struct UndirectedEulerianGraph<N: Node> {
    edges: HashMap<N, Vec<N>>,
}

impl<N: Node> Default for UndirectedEulerianGraph<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N: Node> UndirectedEulerianGraph<N> {
    pub fn new() -> Self {
        Self {
            edges: HashMap::new(),
        }
    }

    pub fn add_edge(&mut self, u: N, v: N) {
        self.edges.entry(u).or_default().push(v);
        self.edges.entry(v).or_default().push(u);
    }

    pub fn add_node(&mut self, n: N) {
        self.edges.entry(n).or_default();
    }
}

impl<N: Node> Graph<N> for UndirectedEulerianGraph<N> {
    fn nodes(&self) -> impl Iterator<Item = N> {
        self.edges.keys().copied().collect::<Vec<_>>().into_iter()
    }

    fn neighbors(&self, node: N) -> impl Iterator<Item = N> {
        self.edges
            .get(&node)
            .map(|neighbors| neighbors.to_vec())
            .unwrap_or_default()
            .into_iter()
    }

    fn is_directed(&self) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Graph;

    #[test]
    fn test_eulerian_cycle_directed() {
        let mut graph = AdjacencyList::<char, i32>::new();

        graph.add_node('A');
        graph.add_node('B');
        graph.add_node('C');
        graph.add_edge('A', 'B');
        graph.add_edge('B', 'C');
        graph.add_edge('C', 'A');

        let result = hierholzer(&graph);
        println!(
            "Cycle result: path={:?}, has_cycle={}, has_path={}",
            result.path, result.has_eulerian_cycle, result.has_eulerian_path
        );

        assert!(result.has_eulerian_cycle, "Should have Eulerian cycle");
        assert!(
            result.has_eulerian_path,
            "Should also have Eulerian path (cycle is a special case)"
        );
        assert!(!result.path.is_empty(), "Path should not be empty");
        assert_eq!(
            result.path.len(),
            4,
            "Path should have 4 vertices for 3 edges"
        );
        assert_eq!(
            result.path[0],
            result.path[result.path.len() - 1],
            "Cycle should start and end at same vertex"
        );
    }

    #[test]
    fn test_eulerian_path_only_directed() {
        let mut graph = AdjacencyList::<char, i32>::new();

        graph.add_node('A');
        graph.add_node('B');
        graph.add_node('C');
        graph.add_node('D');
        graph.add_edge('A', 'B');
        graph.add_edge('B', 'C');
        graph.add_edge('C', 'D');

        let result = hierholzer(&graph);
        println!(
            "Path only result: path={:?}, has_cycle={}, has_path={}",
            result.path, result.has_eulerian_cycle, result.has_eulerian_path
        );
        assert!(!result.has_eulerian_cycle, "Should not have Eulerian cycle");
        assert!(result.has_eulerian_path, "Should have Eulerian path");
        assert!(!result.path.is_empty(), "Path should not be empty");
        assert_ne!(
            result.path[0],
            result.path[result.path.len() - 1],
            "Path should start and end at different vertices"
        );
    }

    #[test]
    fn test_eulerian_cycle_undirected() {
        let mut graph = UndirectedEulerianGraph::new();

        graph.add_node('A');
        graph.add_node('B');
        graph.add_node('C');
        graph.add_edge('A', 'B');
        graph.add_edge('B', 'C');
        graph.add_edge('C', 'A');

        let result = hierholzer(&graph);

        assert!(result.has_eulerian_cycle, "Should have Eulerian cycle");
        assert!(
            result.has_eulerian_path,
            "Should also have Eulerian path (cycle is a special case)"
        );
        assert!(!result.path.is_empty(), "Path should not be empty");

        assert_eq!(
            result.path[0],
            result.path[result.path.len() - 1],
            "Cycle should start and end at same vertex"
        );
    }

    #[test]
    fn test_eulerian_path_undirected() {
        let mut graph = UndirectedEulerianGraph::new();

        graph.add_node('A');
        graph.add_node('B');
        graph.add_node('C');
        graph.add_edge('A', 'B');
        graph.add_edge('B', 'C');

        let result = hierholzer(&graph);
        assert!(!result.has_eulerian_cycle, "Should not have Eulerian cycle");
        assert!(result.has_eulerian_path, "Should have Eulerian path");
        assert!(!result.path.is_empty(), "Path should not be empty");

        assert_ne!(
            result.path[0],
            result.path[result.path.len() - 1],
            "Path should start and end at different vertices"
        );
    }

    #[test]
    fn test_single_node() {
        let mut graph = AdjacencyList::<char, i32>::new();
        graph.add_node('A');

        let result = hierholzer(&graph);
        assert!(
            result.has_eulerian_cycle,
            "Single node should have trivial Eulerian cycle"
        );
        assert!(
            result.has_eulerian_path,
            "Single node should also have trivial Eulerian path"
        );
        assert_eq!(result.path, vec!['A']);
    }
}
