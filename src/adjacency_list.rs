use crate::graph::{Node, Weight, WeightedGraph};
use crate::{Graph, UndirectedGraph};
use std::collections::HashMap;

/// Representa um grafo usando uma lista de adjacência.
/// A lista é implementada como um dicionário, onde cada chave
/// guarda um nó e o valor é um conjunto de arestas.
/// Cada elemento do conjunto de arestas é uma dupla:
/// - 1º elemento indica o vértice adjacente;
/// - 2º elemento indica o peso da aresta.
///
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

    fn node_degrees(&self, n: N) -> (usize, usize) {
        let out_deg = self.0.get(&n).map_or(0, |neighbors| neighbors.len());

        let in_deg = self
            .0
            .iter()
            .filter(|(_, neighbors)| neighbors.iter().any(|(target, _)| *target == n))
            .count();

        (in_deg, out_deg)
    }

    fn nodes(&self) -> impl Iterator<Item = N> {
        self.0.clone().into_keys()
    }

    fn add_node(&mut self, n: N) {
        self.0.insert(n, Vec::new());
    }

    fn add_edge(&mut self, n: N, m: N) {
        if self.0.contains_key(&m) {
            self.0
                .entry(n)
                .and_modify(|neighbors| neighbors.push((m, W::one())));
        }
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

    fn remove_edge(&mut self, n: N, m: N) {
        if self.0.contains_key(&n) {
            self.0
                .entry(n)
                .and_modify(|neighbors| neighbors.retain(|neighbor| neighbor.0 != m));
        }
    }
}

impl<N: Node, W: Weight> UndirectedGraph<N> for AdjacencyList<N, W> {}

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
