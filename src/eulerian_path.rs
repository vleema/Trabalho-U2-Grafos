use crate::graph::Node;
use crate::graphs::AdjacencyList;
use std::collections::{HashMap};

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
            .unwrap_or_else(Vec::new)
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

    // Calcular graus
    let (out_degree, in_degree) = calculate_degrees(graph);

    // Verificar condições Eulerianas
    let (start_node, has_eulerian_path, has_eulerian_cycle) =
        check_eulerian_conditions(&out_degree, &in_degree, is_directed);

    if !has_eulerian_path && !has_eulerian_cycle {
        return HierholzerResult {
            path: Vec::new(),
            has_eulerian_cycle: false,
            has_eulerian_path: false,
        };
    }

    // Criar contador de arestas
    let mut edge_count = create_edge_count(graph);

    let mut stack = Vec::new();
    let mut path = Vec::new();

    stack.push(start_node);

    while let Some(current_vertex) = stack.last().copied() {
        // Verificar se ainda há arestas saindo do vértice atual
        if let Some(neighbors) = edge_count.get_mut(&current_vertex) {
            if let Some((&next_vertex, count)) = neighbors.iter_mut()
                .find(|(_, count)| **count > 0)
            {
                // Remove a aresta
                *count -= 1;

                // Para grafos não direcionados, remove a aresta inversa
                if !is_directed {
                    if let Some(rev_neighbors) = edge_count.get_mut(&next_vertex) {
                        if let Some(rev_count) = rev_neighbors.get_mut(&current_vertex) {
                            *rev_count -= 1;
                        }
                    }
                }

                stack.push(next_vertex);
                continue;
            }
        }

        // Nenhuma aresta saindo, move para o path
        if let Some(vertex) = stack.pop() {
            path.push(vertex);
        }
    }

    path.reverse();

    // Verificar se o caminho encontrado usa todas as arestas
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

fn calculate_degrees<N: Node, G: Graph<N>>(
    graph: &G
) -> (HashMap<N, usize>, HashMap<N, usize>) {
    let mut out_degree = HashMap::new();
    let mut in_degree = HashMap::new();

    // Inicializar todos os nós
    for node in graph.nodes() {
        out_degree.insert(node, 0);
        in_degree.insert(node, 0);
    }

    // Calcular graus
    for node in graph.nodes() {
        let neighbors_count = graph.neighbors(node).count();
        out_degree.insert(node, neighbors_count);

        if graph.is_directed() {
            for neighbor in graph.neighbors(node) {
                *in_degree.entry(neighbor).or_insert(0) += 1;
            }
        }
    }

    // Para grafos não direcionados, in_degree = out_degree
    if !graph.is_directed() {
        for node in graph.nodes() {
            in_degree.insert(node, out_degree[&node]);
        }
    }

    (out_degree, in_degree)
}

fn create_edge_count<N: Node, G: Graph<N>>(
    graph: &G
) -> HashMap<N, HashMap<N, usize>> {
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
    let mut plus_one_count = 0;
    let mut minus_one_count = 0;
    let mut start_candidate = None;

    for &node in nodes {
        let out = out_degree.get(&node).copied().unwrap_or(0);
        let inn = in_degree.get(&node).copied().unwrap_or(0);

        if out == 0 && inn == 0 {
            continue; // Nó isolado
        }

        let diff = out as i32 - inn as i32;

        match diff {
            0 => { /* balanced */ }
            1 => {
                plus_one_count += 1;
                start_candidate = Some(node);
            }
            -1 => {
                minus_one_count += 1;
            }
            _ => {
                return (nodes[0], false, false);
            }
        }
    }

    if plus_one_count == 0 && minus_one_count == 0 {
        // Todos balanceados - ciclo Euleriano
        (nodes[0], false, true)
    } else if plus_one_count == 1 && minus_one_count == 1 {
        // Exatamente um com +1 e um com -1 - caminho Euleriano
        (start_candidate.unwrap(), true, false)
    } else {
        (nodes[0], false, false)
    }
}

fn check_undirected_eulerian<N: Node>(
    out_degree: &HashMap<N, usize>,
    nodes: &[N],
) -> (N, bool, bool) {
    let mut odd_degree_count = 0;
    let mut start_candidate = None;

    for &node in nodes {
        let degree = out_degree.get(&node).copied().unwrap_or(0);
        if degree > 0 && degree % 2 != 0 {
            odd_degree_count += 1;
            start_candidate = Some(node);
        }
    }

    if odd_degree_count == 0 {
        // Todos graus pares - ciclo Euleriano
        (nodes[0], false, true)
    } else if odd_degree_count == 2 {
        // Exatamente dois vértices com grau ímpar - caminho Euleriano
        (start_candidate.unwrap(), true, false)
    } else {
        (nodes[0], false, false)
    }
}

// Implementação para grafos não direcionados para testes
pub struct UndirectedGraph<N: Node> {
    edges: HashMap<N, Vec<N>>,
}

impl<N: Node> UndirectedGraph<N> {
    pub fn new() -> Self {
        Self { edges: HashMap::new() }
    }

    pub fn add_edge(&mut self, u: N, v: N) {
        self.edges.entry(u).or_default().push(v);
        self.edges.entry(v).or_default().push(u);
    }

    pub fn add_node(&mut self, n: N) {
        self.edges.entry(n).or_default();
    }
}

impl<N: Node> Graph<N> for UndirectedGraph<N> {
    fn nodes(&self) -> impl Iterator<Item = N> {
        self.edges.keys().copied().collect::<Vec<_>>().into_iter()
    }

    fn neighbors(&self, node: N) -> impl Iterator<Item = N> {
        self.edges
            .get(&node)
            .map(|neighbors| neighbors.iter().copied().collect::<Vec<_>>())
            .unwrap_or_else(Vec::new)
            .into_iter()
    }

    fn is_directed(&self) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use crate::Graph;

    #[test]
    fn test_eulerian_cycle_directed() {
        let mut graph = AdjacencyList::<char, i32>(HashMap::new());

        graph.add_node('A');
        graph.add_node('B');
        graph.add_node('C');
        graph.add_edge('A', 'B');
        graph.add_edge('B', 'C');
        graph.add_edge('C', 'A');

        let result = hierholzer(&graph);
        assert!(result.has_eulerian_cycle, "Should have Eulerian cycle");
        assert!(!result.has_eulerian_path, "Should not have Eulerian path");
        assert!(!result.path.is_empty(), "Path should not be empty");
        assert_eq!(result.path.len(), 4, "Path should have 4 vertices for 3 edges");
    }

    #[test]
    fn test_eulerian_path_directed() {
        let mut graph = AdjacencyList::<char, i32>(HashMap::new());

        graph.add_node('A');
        graph.add_node('B');
        graph.add_node('C');
        graph.add_node('D');
        graph.add_edge('A', 'B');
        graph.add_edge('B', 'C');
        graph.add_edge('C', 'D');

        let result = hierholzer(&graph);
        assert!(!result.has_eulerian_cycle, "Should not have Eulerian cycle");
        assert!(result.has_eulerian_path, "Should have Eulerian path");
        assert!(!result.path.is_empty(), "Path should not be empty");
    }

    #[test]
    fn test_eulerian_cycle_undirected() {
        let mut graph = UndirectedGraph::new();

        graph.add_node('A');
        graph.add_node('B');
        graph.add_node('C');
        graph.add_edge('A', 'B');
        graph.add_edge('B', 'C');
        graph.add_edge('C', 'A');

        let result = hierholzer(&graph);
        assert!(result.has_eulerian_cycle, "Should have Eulerian cycle");
        assert!(!result.has_eulerian_path, "Should not have Eulerian path");
        assert!(!result.path.is_empty(), "Path should not be empty");
    }

    #[test]
    fn test_eulerian_path_undirected() {
        let mut graph = UndirectedGraph::new();

        graph.add_node('A');
        graph.add_node('B');
        graph.add_node('C');
        graph.add_edge('A', 'B');
        graph.add_edge('B', 'C');

        let result = hierholzer(&graph);
        assert!(!result.has_eulerian_cycle, "Should not have Eulerian cycle");
        assert!(result.has_eulerian_path, "Should have Eulerian path");
        assert!(!result.path.is_empty(), "Path should not be empty");
    }
}