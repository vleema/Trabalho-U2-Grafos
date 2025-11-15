use crate::graph::{Node, Weight, WeightedGraph};
use crate::{Graph, UndirectedGraph};
use std::collections::HashMap;

/// Representa um grafo usando uma lista de adjacência.
/// A lista é implementada como um *map*, onde cada chave
/// guarda um nó e o valor é um conjunto de arestas.
/// Cada elemento do conjunto de arestas é uma dupla:
/// o 1º elemento indica o vértice adjacente e o
/// 2º elemento o peso da aresta.
#[derive(Debug, Clone, Default)]
pub struct AdjacencyList<N: Node, W: Weight>(pub HashMap<N, Vec<(N, W)>>);

impl<N: Node, W: Weight> AdjacencyList<N, W> {
    pub fn new() -> Self {
        AdjacencyList(HashMap::new())
    }
}

impl<N: Node, W: Weight> Graph<N> for AdjacencyList<N, W> {
    fn order(&self) -> usize {
        self.0.len()
    }

    fn size(&self) -> usize {
        self.0
            .keys()
            .map(|node| self.neighbors(*node).count())
            .sum()
    }

    fn node_degrees(&self, _n: N) -> (usize, usize) {
        todo!()
        /*
        let out_deg = self.0[n].iter().filter(|&&v| v != 0).count();
        let in_deg = self.0.iter().filter(|row| row[n] != 0).count();
        (in_deg, out_deg)
            */
    }

    fn nodes(&self) -> impl Iterator<Item = N> {
        self.0.clone().into_keys()
    }

    fn add_node(&mut self, n: N) {
        self.0.insert(n, Vec::new());
    }

    fn remove_node(&mut self, _n: N) {
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

    fn add_edge(&mut self, n: N, m: N) {
        if self.0.contains_key(&m) {
            self.0
                .entry(n)
                .and_modify(|neighbors| neighbors.push((n, W::one())));
        }
    }

    fn remove_edge(&mut self, _n: N, _m: N) {
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
        = impl Iterator<Item = N>
    where
        Self: 'a;

    fn neighbors(&self, n: N) -> Self::Neighbors<'_> {
        self.0
            .get(&n)
            .into_iter()
            .flat_map(|set| set.iter().map(|(n, _)| *n))
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

impl<N: Node, W: Weight> UndirectedGraph<N> for AdjacencyList<N, W> {
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

    fn undirected_node_degree(&self, _n: N) -> usize {
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

impl<N: Node, W: Weight> WeightedGraph<N, W> for AdjacencyList<N, W> {
    fn add_weighted_edge(&mut self, n: N, m: N, w: W) {
        if self.0.contains_key(&m) {
            self.0
                .entry(n)
                .and_modify(|neighbors| neighbors.push((n, w)));
        }
    }

    type WeightedNeighbors<'a>
        = impl Iterator<Item = (N, W)>
    where
        Self: 'a,
        N: 'a;

    fn weighted_neighbors(&self, n: N) -> Self::WeightedNeighbors<'_> {
        self.0
            .get(&n)
            .into_iter()
            .flat_map(|neighbors| neighbors.iter().copied())
    }
}

mod tests {}
