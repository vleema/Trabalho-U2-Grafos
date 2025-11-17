use crate::graph::Node;
use crate::{Graph, UndirectedGraph};
use std::collections::HashMap;

pub struct HierholzerResult<Node> {
    pub path: Vec<Node>,
    pub has_eulerian_path: bool,
    pub has_eulerian_cycle: bool,
}

impl<N: Node> HierholzerResult<N> {
    pub fn new<G: UndirectedGraph<N>>(graph: &G, is_directed: bool) -> Self {
        let mut out_degree = HashMap::new();
        let mut in_degree = HashMap::new();
        Self::compute_every_node_degree(graph, &mut out_degree, &mut in_degree);

        let (mut start_node, has_eulerian_path, has_eulerian_cycle) =
            Self::check_eulerian_conditions(&out_degree, &in_degree, is_directed);

        if !has_eulerian_path && !has_eulerian_cycle {
            return HierholzerResult {
                path: Vec::new(),
                has_eulerian_cycle,
                has_eulerian_path,
            };
        } else if has_eulerian_cycle && has_eulerian_path && out_degree.len() == 1 {
            return HierholzerResult {
                path: out_degree.iter().map(|(k, _)| *k).collect::<Vec<N>>(),
                has_eulerian_cycle,
                has_eulerian_path,
            };
        }

        let mut stack = Vec::new();
        let mut path = Vec::new();
        let mut work_graph: G = graph.clone();

        loop {
            if stack.is_empty() && work_graph.neighbors(start_node).count() == 0 {
                break;
            } else {
                if work_graph.neighbors(start_node).count() > 0 {
                    stack.push(start_node);

                    let next_neighbor = work_graph.neighbors(start_node).next();

                    if let Some(neighbor) = next_neighbor {
                        if is_directed {
                            work_graph.remove_edge(start_node, neighbor);
                        } else {
                            work_graph.remove_undirected_edge(start_node, neighbor);
                        }

                        start_node = neighbor;
                    }
                } else {
                    path.push(start_node);
                    if let Some(s) = stack.pop() {
                        start_node = s;
                    }

                    if stack.is_empty() {
                        path.push(start_node);
                    }
                }
            }
        }
        path.reverse();

        let total_edges: usize = if is_directed {
            out_degree.values().sum()
        } else {
            out_degree.values().sum::<usize>() / 2
        };

        let valid_path = path.len() == total_edges + 1;

        Self {
            path: if valid_path { path } else { Vec::new() },
            has_eulerian_cycle: valid_path && has_eulerian_cycle,
            has_eulerian_path: valid_path && has_eulerian_path,
        }
    }

    fn compute_every_node_degree<G: Graph<N>>(
        graph: &G,
        out_degree: &mut HashMap<N, usize>,
        in_degree: &mut HashMap<N, usize>,
    ) {
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
    }

    fn check_eulerian_conditions(
        out_degree: &HashMap<N, usize>,
        in_degree: &HashMap<N, usize>,
        is_directed: bool,
    ) -> (N, bool, bool) {
        let nodes: Vec<N> = out_degree.keys().copied().collect();

        if nodes.is_empty() {
            panic!("Graph has no nodes");
        }

        if is_directed {
            Self::check_directed_eulerian(out_degree, in_degree, &nodes)
        } else {
            Self::check_undirected_eulerian(out_degree, &nodes)
        }
    }

    fn check_directed_eulerian(
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

    fn check_undirected_eulerian(out_degree: &HashMap<N, usize>, nodes: &[N]) -> (N, bool, bool) {
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Graph, UndirectedGraph, graphs::AdjacencyList};

    #[test]
    fn test_eulerian_cycle_directed() {
        let mut graph = AdjacencyList::<char, i32>::new();

        graph.add_node('A');
        graph.add_node('B');
        graph.add_node('C');
        graph.add_edge('A', 'B');
        graph.add_edge('B', 'C');
        graph.add_edge('C', 'A');

        let result = HierholzerResult::new(&graph, true);
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

        let result = HierholzerResult::new(&graph, true);
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
        let mut graph = AdjacencyList::<char, i32>::new();

        graph.add_node('A');
        graph.add_node('B');
        graph.add_node('C');
        graph.add_undirected_edge('A', 'B');
        graph.add_undirected_edge('B', 'C');
        graph.add_undirected_edge('C', 'A');

        let result = HierholzerResult::new(&graph, false);

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
        let mut graph = AdjacencyList::<i32, i32>::new();
        graph.add_node(1);
        graph.add_node(2);
        graph.add_node(3);
        graph.add_node(4);
        graph.add_undirected_edge(1, 2);
        graph.add_undirected_edge(2, 3);
        graph.add_undirected_edge(3, 4);

        let result = HierholzerResult::new(&graph, false);
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

        let result = HierholzerResult::new(&graph, false);
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

    // Está errado, não? É para ter caminho euleriano
    // #[test]
    // fn test() {
    //     println!("GRAFO 2: Caminho Euleriano (Não Direcionado)");
    //     println!("Vértices: 1, 2, 3, 4, 5, 6, 7");

    //     let mut graph = AdjacencyList::<char, i32>::new();

    //     graph.add_node('1');
    //     graph.add_node('2');
    //     graph.add_node('3');
    //     graph.add_node('4');
    //     graph.add_node('5');
    //     graph.add_node('6');
    //     graph.add_node('7');

    //     graph.add_edge('1', '2');
    //     graph.add_edge('1', '3');
    //     graph.add_edge('2', '3');
    //     graph.add_edge('2', '4');
    //     graph.add_edge('2', '5');
    //     graph.add_edge('3', '4');
    //     graph.add_edge('3', '6');
    //     graph.add_edge('4', '5');
    //     graph.add_edge('4', '6');
    //     graph.add_edge('5', '6');
    //     graph.add_edge('5', '7');
    //     graph.add_edge('6', '7');

    //     let result = HierholzerResult::new(&graph, false);

    //     println!("Resultado:");
    //     println!("- Tem ciclo euleriano: {}", result.has_eulerian_cycle);
    //     println!("- Tem caminho euleriano: {}", result.has_eulerian_path);
    //     println!("- Caminho encontrado: {:?}", result.path);

    //     if result.has_eulerian_cycle {
    //         println!("\nO grafo possui um CICLO EULERIANO!");
    //         println!("Todos os vértices têm grau par");
    //         if !result.path.is_empty() {
    //             println!(
    //                 "Começa e termina no mesmo vértice: {} → ... → {}",
    //                 result.path[0],
    //                 result.path[result.path.len() - 1]
    //             );
    //         }

    //         let expected_length = 12 + 1;
    //         if result.path.len() == expected_length {
    //             println!("Percorre todas as {} arestas exatamente uma vez", 12);
    //         }
    //     }

    //     if result.has_eulerian_path {
    //         println!("O grafo também possui CAMINHO EULERIANO!");
    //         println!("(Um ciclo euleriano é um caso especial de caminho euleriano)");
    //     }
    // }
}
