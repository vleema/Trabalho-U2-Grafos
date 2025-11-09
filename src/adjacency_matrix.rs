use crate::graph::Node;
use crate::{Graph, UndirectedGraph};
use std::collections::{HashMap, HashSet};

/// Representa um grafo usando uma matriz de adjacência.
/// A matriz é implementada como um *map*, onde cada chave
/// guarda um nó e o valor é um conjunto de arestas.
/// Cada elemento do conjunto é uma dupla: 1º elemento indica
/// o vértice adjacente e o 2º elemento o peso da aresta.
#[derive(Debug, Clone)]
pub struct AdjacencyMatrix<T>(pub HashMap<T, HashSet<(T, i32)>>)
where
    T: Node;

impl<T> Graph<T> for AdjacencyMatrix<T>
where
    T: Node,
{
    fn order(&self) -> usize {
        self.0.len()
    }

    fn size(&self) -> usize {
        todo!()
        /*self.0
            .iter()
            .enumerate()
            .map(|(i, _)| self.neighbors(i).count())
            .sum()
        */
    }

    fn node_degrees(&self, _n: T) -> (usize, usize) {
        todo!()
        /*
        let out_deg = self.0[n].iter().filter(|&&v| v != 0).count();
        let in_deg = self.0.iter().filter(|row| row[n] != 0).count();
        (in_deg, out_deg)
            */
    }

    fn nodes(&self) -> impl Iterator<Item = T> {
        self.0.clone().into_keys()
    }

    fn add_node(&mut self, _n: T) {
        todo!()
        /*
        self.0.push(Vec::new());
        let new_order = self.order();

        for r in &mut self.0 {
            while r.len() < new_order {
                r.push(0);
            }
        }
            */
    }

    fn remove_node(&mut self, _n: T) {
        todo!()
        /*
        if n < self.0.len() {
            self.0.remove(n);
            for row in self.0.iter_mut() {
                for idx in n + 1..row.len() {
                    row[idx - 1] = row[idx];
                }
                row.pop();
            }
        }
        */
    }

    fn add_edge(&mut self, _n: T, _m: T) {
        todo!()
        /*
        if let Some(edges) = self.0.get_mut(n)
            && let Some(edge) = edges.get_mut(m)
        {
            if *edge == 1 {
                return;
            }
            *edge = 1;
        }
            */
    }

    fn remove_edge(&mut self, _n: T, _m: T) {
        todo!()
        /*
        if let Some(edges) = self.0.get_mut(n)
            && let Some(edge) = edges.get_mut(m)
        {
            *edge = 0;
        }
        */
    }

    type Neighbors<'a>
        = std::iter::FilterMap<
        std::iter::Enumerate<std::collections::hash_set::Iter<'a, (T, i32)>>,
        fn((usize, &'a (T, i32))) -> Option<T>,
    >
    where
        T: 'a;

    fn neighbors<'a>(&'a self, n: T) -> Option<Self::Neighbors<'a>> {
        fn filter_fn<T: Node>((_, &(node, weight)): (usize, &(T, i32))) -> Option<T> {
            if weight != 0 { Some(node) } else { None }
        }

        if let Some(neighbors) = self.0.get(&n) {
            Some(neighbors.iter().enumerate().filter_map(filter_fn))
        } else {
            None
        }
    }

    type WeightedNeighbors<'a>
        = std::iter::FilterMap<
        std::iter::Enumerate<std::collections::hash_set::Iter<'a, (T, i32)>>,
        fn((usize, &'a (T, i32))) -> Option<(T, i32)>,
    >
    where
        T: 'a;

    fn weighted_neighbors<'a>(&'a self, n: T) -> Option<Self::WeightedNeighbors<'a>> {
        fn filter_fn<T: Node>((_, &(node, weight)): (usize, &(T, i32))) -> Option<(T, i32)> {
            if weight != 0 {
                Some((node, weight))
            } else {
                None
            }
        }

        if let Some(neighbors) = self.0.get(&n) {
            Some(neighbors.iter().enumerate().filter_map(filter_fn))
        } else {
            None
        }
    }

    fn bipartite(&self) -> bool {
        todo!()
        /*
        let n = self.order();
        if n == 0 {
            return true;
        }

        let mut side = vec![None; n]; // None = uncolored, Some(0/1) = partition
        let mut queue = std::collections::VecDeque::new();

        for start in 0..n {
            // skip already colored components
            if side[start].is_some() {
                continue;
            }

            side[start] = Some(0);
            queue.push_back(start);

            while let Some(u) = queue.pop_front() {
                let u_side = side[u].unwrap();

                for (v, &is_edge) in self.0[u].iter().enumerate() {
                    if is_edge == 0 {
                        continue;
                    }

                    if side[v].is_none() {
                        side[v] = Some(1 - u_side);
                        queue.push_back(v);
                    } else if side[v] == Some(u_side) {
                        return false; // adjacent nodes with same color
                    }
                }
            }
        }

        true
        */
    }

    fn underlying_graph(&self) -> Self {
        todo!()
        /*
        let mut matrix: AdjacencyMatrix =
            AdjacencyMatrix(vec![vec![0; self.0.len()]; self.0.len()]);

        for (idx_r, row) in self.0.iter().enumerate() {
            for (idx_c, col) in row.iter().enumerate() {
                if *col == 1 && !matrix.has_edge(idx_c, idx_r) {
                    matrix.add_undirected_edge(idx_r, idx_c);
                }
            }
        }

        matrix
        */
    }
}

impl<T> UndirectedGraph<T> for AdjacencyMatrix<T>
where
    T: Node,
{
    fn undirected_size(&self) -> usize {
        todo!()
        /*
        let mut size = 0;
        for i in 0..self.order() {
            for j in 0..=i {
                if self.0[i][j] > 0 {
                    size += 1;
                }
            }
        }
        size
        */
    }

    fn connected(&self) -> bool {
        todo!()
        /*
        let n = self.order();
        if n == 0 {
            return true;
        }

        let mut visited = vec![false; n];
        let mut stack = vec![0];
        visited[0] = true;

        while let Some(u) = stack.pop() {
            for (v, &is_edge) in self.0[u].iter().enumerate() {
                if is_edge > 0 && !visited[v] {
                    visited[v] = true;
                    stack.push(v);
                }
            }
        }

        visited.into_iter().all(|v| v)
        */
    }

    fn undirected_node_degree(&self, _n: T) -> usize {
        todo!()
        /*
        if let Some(row) = self.0.get(node) {
            row.iter().filter(|&&val| val != 0).count()
        } else {
            0
        }
        */
    }
}

#[cfg(test)]
mod tests {
    /*

    #[test]
    fn undirected_graph_matrix_size() {
        let undirected_m = AdjacencyMatrix(vec![
            vec![1, 1, 0, 1, 0, 0],
            vec![1, 0, 1, 1, 0, 0],
            vec![0, 1, 0, 1, 0, 0],
            vec![1, 1, 1, 0, 1, 1],
            vec![0, 0, 0, 1, 0, 1],
            vec![0, 0, 0, 1, 1, 0],
        ]);
        assert_eq!(undirected_m.undirected_size(), 9);
    }

    #[test]
    fn graph_matrix_size() {
        let directed_m = AdjacencyMatrix(vec![
            vec![1, 0, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
            vec![0, 1, 0, 0, 0, 0],
            vec![1, 1, 1, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 1],
            vec![0, 0, 0, 1, 0, 0],
        ]);
        assert_eq!(directed_m.size(), 9);
    }

    #[test]
    fn adjacency_list_to_matrix() {
        // Grafo: 0 ── 1
        //        │
        //        2
        let list = AdjacencyList(vec![vec![1, 2], vec![0], vec![0]]);
        let matrix = AdjacencyMatrix::from_adjacency_list(&list);

        assert_eq!(matrix.0, vec![vec![0, 1, 1], vec![1, 0, 0], vec![1, 0, 0]]);
    }

    #[test]
    fn matrix_to_list() {
        // Mesmo grafo de cima, mas em matriz
        let matrix = AdjacencyMatrix(vec![vec![0, 1, 1], vec![1, 0, 0], vec![1, 0, 0]]);

        let list = AdjacencyList::from_adjacency_matrix(&matrix);

        assert_eq!(list.0, vec![vec![1, 2], vec![0], vec![0]]);
    }

    #[test]
    fn round_trip_conversion() {
        // Grafo: 0 ── 1 ── 2
        let original_list = AdjacencyList(vec![vec![1], vec![0, 2], vec![1]]);
        let matrix = AdjacencyMatrix::from_adjacency_list(&original_list);
        let converted_list = AdjacencyList::from_adjacency_matrix(&matrix);

        assert_eq!(original_list.0, converted_list.0);
    }

    #[test]
    fn underlying_graph_conversion() {
        // Graph:
        // 0 -> 1 -> 2 <- 3
        //      \    ^
        //       \   |
        //       ->  4
        let original_graph = AdjacencyMatrix(vec![
            vec![0, 1, 0, 0, 0],
            vec![0, 0, 1, 0, 1],
            vec![0, 0, 0, 0, 0],
            vec![0, 0, 1, 0, 0],
            vec![0, 0, 1, 0, 0],
        ]);

        // Current graph:
        // 0 -- 1 -- 2 -- 3
        //      \    |
        //       \   |
        //        -  4
        let underlying_graph = original_graph.underlying_graph();
        assert_eq!(original_graph.order(), underlying_graph.order());
    }

    #[test]
    fn graph_add_new_node() {
        // Graph: 0 -> 2 <- 1
        let mut m = AdjacencyMatrix(vec![vec![0, 0, 1], vec![0, 0, 1], vec![0, 0, 0]]);
        m.add_node(3);
        // Graph: 0 -> 2 <- 1  3
        assert!(m.order() == 4);
        // assert!(!m.underlying_graph().connected());
    }

    #[test]
    fn graph_add_new_node_and_edge() {
        // Graph: 0 -> 2 <- 1
        let mut m = AdjacencyMatrix(vec![vec![0, 0, 1], vec![0, 0, 1], vec![0, 0, 0]]);
        m.add_node(3);
        m.add_edge(1, 3);
        // Graph: 0 -> 2 <- 1 -> 3
        assert!(m.has_edge(1, 3));
        assert!(!m.has_edge(3, 1));
        // assert!(m.underlying_graph().connected());
    }

    #[test]
    fn undirected_graph_add_new_node_and_edge() {
        // Graph: 0 - 2 - 1
        let mut m = AdjacencyMatrix(vec![vec![0, 0, 1], vec![0, 0, 1], vec![1, 1, 0]]);
        m.add_node(3);
        m.add_undirected_edge(1, 3);
        // Graph: 0 - 2 - 1 - 3
        assert!(m.has_edge(1, 3));
        assert!(m.has_edge(3, 1));
        assert_eq!(m.undirected_size(), 3);
        // assert!(!m.underlying_graph().connected());
    }

    #[test]
    fn graph_remove_edge() {
        // Graph:
        // 0 -> 1 -> 2 <- 3
        //      \    ^
        //       \   |
        //       ->  4
        let mut m = AdjacencyMatrix(vec![
            vec![0, 1, 0, 0, 0],
            vec![0, 0, 1, 0, 1],
            vec![0, 0, 0, 0, 0],
            vec![0, 0, 1, 0, 0],
            vec![0, 0, 1, 0, 0],
        ]);

        m.remove_edge(1, 4);
        assert!(!m.has_edge(1, 4));
        assert!(!m.has_edge(4, 1));
        assert!(m.size() == 4);
        // assert!(m.underlying_graph().connected());
    }

    #[test]
    fn graph_duplicate_remove_edge() {
        // Graph:
        // 0 -> 1 -> 2 <- 3
        //      \    ^
        //       \   |
        //       ->  4
        let mut m = AdjacencyMatrix(vec![
            vec![0, 1, 0, 0, 0],
            vec![0, 0, 1, 0, 1],
            vec![0, 0, 0, 0, 0],
            vec![0, 0, 1, 0, 0],
            vec![0, 0, 1, 0, 0],
        ]);

        m.remove_edge(1, 4);
        m.remove_edge(1, 4);
        assert!(!m.has_edge(1, 4));
        assert!(!m.has_edge(4, 1));
        assert!(m.size() == 4);
        // assert!(m.underlying_graph().connected());
    }

    #[test]
    fn graph_remove_node() {
        // Graph:
        // 0 -> 1 -> 2 <- 3
        //      \    ^
        //       \   |
        //       ->  4
        let mut m = AdjacencyMatrix(vec![
            vec![0, 1, 0, 0, 0],
            vec![0, 0, 1, 0, 1],
            vec![0, 0, 0, 0, 0],
            vec![0, 0, 1, 0, 0],
            vec![0, 0, 1, 0, 0],
        ]);

        m.remove_node(2);
        assert!(m.order() == 4);
        assert!(m.size() == 2);
        assert!(!m.has_edge(3, 2));
        assert!(!m.has_edge(1, 2));
        assert!(!m.has_edge(4, 2));
    }

    #[test]
    fn graph_remove_node_and_add_new() {
        // Graph:
        // 0 -> 1 -> 2 <- 3
        //      \    ^
        //       \   |
        //       ->  4
        let mut m = AdjacencyMatrix(vec![
            vec![0, 1, 0, 0, 0],
            vec![0, 0, 1, 0, 1],
            vec![0, 0, 0, 0, 0],
            vec![0, 0, 1, 0, 0],
            vec![0, 0, 1, 0, 0],
        ]);

        m.remove_node(2);

        m.add_node(0);

        m.add_edge(2, 4);
        m.add_edge(2, 3);

        // Graph:
        // 0 -> 1     2
        //   \        | \
        //   \       |  \
        //   -> 3 <-     -> 4
        assert!(m.order() == 5);
        assert!(m.size() == 4);
        assert!(m.has_edge(1, 3));
        assert!(m.has_edge(2, 3));
        assert!(m.has_edge(2, 4));
        assert!(!m.has_edge(4, 2));
    }

    #[test]
    fn undirected_graph_remove_edge() {
        // Graph:
        // 0 -- 1 -- 2 -- 3
        //      \    |
        //       \   |
        //       --  4
        let mut m = AdjacencyMatrix(vec![
            vec![0, 1, 0, 0, 0],
            vec![1, 0, 1, 0, 1],
            vec![0, 1, 0, 1, 1],
            vec![0, 0, 1, 0, 0],
            vec![0, 1, 1, 0, 0],
        ]);

        m.remove_undirected_edge(2, 4);
        assert!(!m.has_edge(2, 4));
        assert!(!m.has_edge(4, 2));
        assert!(m.undirected_size() == 4);
    }

    #[test]
    fn undirected_graph_remove_node() {
        // Graph:
        // 0 -- 1 -- 2 -- 3
        //      \    |
        //       \   |
        //       --  4
        let mut m = AdjacencyMatrix(vec![
            vec![0, 1, 0, 0, 0],
            vec![1, 0, 1, 0, 1],
            vec![0, 1, 0, 1, 1],
            vec![0, 0, 1, 0, 0],
            vec![0, 1, 1, 0, 0],
        ]);

        m.remove_node(4);
        assert_eq!(m.undirected_size(), 3);
        assert!(!m.has_edge(2, 4));
        assert!(!m.has_edge(1, 4));
    }

    #[test]
    fn node_degree_adjacency_matrix() {
        // Grafo: 0 ─ 1
        //        │ /
        //        2
        let matrix = AdjacencyMatrix(vec![vec![0, 1, 1], vec![1, 0, 1], vec![1, 1, 0]]);

        assert_eq!(matrix.undirected_node_degree(0), 2);
        assert_eq!(matrix.undirected_node_degree(1), 2);
        assert_eq!(matrix.undirected_node_degree(2), 2);
    }

    #[test]
    fn adjacency_matrix_order() {
        // Graph: 0 ── 1
        //        │
        //        2
        let matrix = AdjacencyMatrix(vec![vec![0, 1, 1], vec![1, 0, 0], vec![1, 0, 0]]);
        assert_eq!(matrix.order(), 3);
    }

    #[test]
    fn test_connected_graph() {
        // Graph: 0 ─ 1
        //        │ /
        //        2
        let matrix = AdjacencyMatrix(vec![vec![0, 1, 1], vec![1, 0, 1], vec![1, 1, 0]]);
        assert!(matrix.connected());
    }

    #[test]
    fn test_disconnected_graph() {
        // Graph: 0 ─ 1     2
        let matrix = AdjacencyMatrix(vec![vec![0, 1, 0], vec![1, 0, 0], vec![0, 0, 0]]);
        assert!(!matrix.connected());
    }

    #[test]
    fn test_node_degrees_matrix() {
        let mut matrix = AdjacencyMatrix(vec![vec![0, 0, 0]; 3]);
        matrix.0[0][1] = 1;
        matrix.0[1][2] = 1;
        matrix.0[2][0] = 1;

        let degrees_0 = matrix.node_degrees(0);
        let degrees_1 = matrix.node_degrees(1);
        let degrees_2 = matrix.node_degrees(2);

        assert_eq!(degrees_0, (1, 1)); // in: 2->0, out: 0->1
        assert_eq!(degrees_1, (1, 1)); // in: 0->1, out: 1->2
        assert_eq!(degrees_2, (1, 1)); // in: 1->2, out: 2->0
    }
    */
}
