use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::{HashMap, HashSet};

use crate::graph::{Node, UndirectedGraph, WeightedGraph};

/// Enum que representa eventos gerados durante a execução de Kruskal.
/// Cada variante carrega uma tupla (u, v, peso).
#[derive(Debug)]
pub enum KruskalEvent<T>
where
    T: Node + Ord,
{
    EdgeConsidered((T, T, i32)),
    EdgeAdded((T, T, i32)),
    EdgeSkipped((T, T, i32)),
}

/// O Struct KruskalIter implementa um iterador passo-a-passo do algoritmo de Kruskal.
/// Mantém referência ao grafo, vetor de arestas ordenadas, índice corrente e um grafo
/// parcial (`accepted_adj`) usado para detectar ciclos.
pub struct KruskalIter<'a, T, G>
where
    T: Node + Ord,
    G: UndirectedGraph<T> + WeightedGraph<T, i32>,
{
    _graph: &'a G,
    edges: Vec<(T, T, i32)>,
    idx: usize,
    accepted_adj: HashMap<T, HashSet<T>>,
}

impl<'a, T, G> KruskalIter<'a, T, G>
where
    T: Node + Ord,
    G: UndirectedGraph<T> + WeightedGraph<T, i32>,
{
    /// Constrói um iterador que implementa o algoritmo de Kruskal.
    ///
    /// ## Argumentos
    /// * `graph`: um tipo que implementa os traços [`UndirectedGraph`] e [`WeightedGraph`]
    ///
    /// ## Fluxo
    /// * Coleta as arestas do grafo e canonicaliza cada aresta para evitar duplicatas;
    /// * Ordena as arestas por peso crescente e armazena em `edges`;
    /// * Inicializa o grafo parcial `accepted_adj` (vazio) e o índice de leitura `idx`;
    /// * O método `next()` varre `arestas` em ordem; para cada aresta testará se a sua inclusão
    ///   cria ciclo usando `connected_by_accepted`; emite eventos [`KruskalEvent::EdgeAdded`]
    ///   ou [`KruskalEvent::EdgeSkipped`] conforme o caso.
    pub fn new(graph: &'a G) -> Self {
        let nodes: Vec<T> = graph.nodes().collect();
        let accepted_adj: HashMap<T, HashSet<T>> = HashMap::with_capacity(nodes.len());

        let mut seen: HashSet<(T, T)> = HashSet::with_capacity(nodes.len() * 2);
        let mut edges: Vec<(T, T, i32)> = Vec::new();

        for &u in &nodes {
            for (v, w) in graph.weighted_neighbors(u) {
                let (a, b) = if u <= v { (u, v) } else { (v, u) };
                if seen.insert((a, b)) {
                    edges.push((a, b, w));
                }
            }
        }

        edges.sort_by(|(ua, va, wa), (ub, vb, wb)| {
            wa.cmp(wb).then_with(|| ua.cmp(ub)).then_with(|| va.cmp(vb))
        });

        KruskalIter {
            _graph: graph,
            edges,
            idx: 0,
            accepted_adj,
        }
    }

    /// Verifica se existe um caminho no grafo parcial `accepted_adj` entre `a` e `b`.
    /// Usada para decidir se a inclusão da aresta (a,b) criaria um ciclo.
    fn connected_by_accepted(&self, a: T, b: T) -> bool {
        if a == b {
            return true;
        }
        let mut stack: Vec<T> = Vec::new();
        let mut seen: HashSet<T> = HashSet::new();
        stack.push(a);
        seen.insert(a);
        while let Some(x) = stack.pop() {
            if let Some(neis) = self.accepted_adj.get(&x) {
                for &nb in neis {
                    if nb == b {
                        return true;
                    }
                    if !seen.contains(&nb) {
                        seen.insert(nb);
                        stack.push(nb);
                    }
                }
            }
        }
        false
    }
}

impl<'a, T, G> Iterator for KruskalIter<'a, T, G>
where
    T: Node + Ord,
    G: UndirectedGraph<T> + WeightedGraph<T, i32>,
{
    type Item = KruskalEvent<T>;

    /// Avança para a próxima aresta ordenada e retorna um evento indicando
    /// se a aresta foi aceita (`EdgeAdded`) ou descartada (`EdgeSkipped`).
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx < self.edges.len() {
            let (u, v, w) = self.edges[self.idx];
            self.idx += 1;

            if !self.connected_by_accepted(u, v) {
                self.accepted_adj.entry(u).or_default().insert(v);
                self.accepted_adj.entry(v).or_default().insert(u);
                Some(KruskalEvent::EdgeAdded((u, v, w)))
            } else {
                Some(KruskalEvent::EdgeSkipped((u, v, w)))
            }
        } else {
            None
        }
    }
}

/// Enum que representa eventos do iterador de Prim.
/// Cada variante carrega os campos (u, v, peso).
#[derive(Debug)]
pub enum PrimEvent<T>
where
    T: Node + Ord,
{
    EdgeAdded(T, T, i32),
    EdgeSkipped(T, T, i32),
}

/// O Struct PrimIter implementa um iterador passo-a-passo do algoritmo de Prim.
/// Mantém referência ao grafo, conjunto de vértices visitados, um heap de arestas
/// candidatas e o número total de nós.
pub struct PrimIter<'a, T, G>
where
    T: Node + Ord,
    G: UndirectedGraph<T> + WeightedGraph<T, i32>,
{
    _graph: &'a G,
    visited: HashSet<T>,
    heap: BinaryHeap<Reverse<(i32, T, T)>>,
    nodes_len: usize,
}

impl<'a, T, G> PrimIter<'a, T, G>
where
    T: Node + Ord,
    G: UndirectedGraph<T> + WeightedGraph<T, i32>,
{
    /// Constrói um iterador que implementa o algoritmo de Prim.
    ///
    /// ## Argumentos
    /// * `graph`: um tipo que implementa os traços [`UndirectedGraph`] e [`WeightedGraph`]
    ///
    /// ## Fluxo
    /// * Escolhe um vértice inicial (o primeiro de `graph.nodes()`);
    /// * Insere o vértice inicial em `visited` e popula o `heap` com as arestas incidentes a ele;
    /// * A cada chamada de `next()` extrai do `heap` a aresta de menor peso; se exatamente um
    ///   extremo estiver em `visited` a aresta é aceita e o novo vértice é incorporado, adicionando
    ///   suas arestas ao `heap`; caso contrário a aresta é descartada;
    pub fn new(graph: &'a G) -> Self {
        let nodes: Vec<T> = graph.nodes().collect();
        let mut visited: HashSet<T> = HashSet::with_capacity(nodes.len());
        let mut heap = BinaryHeap::new();

        if let Some(&s) = nodes.first() {
            visited.insert(s);
            for (v, w) in graph.weighted_neighbors(s) {
                let (a, b) = if s <= v { (s, v) } else { (v, s) };
                heap.push(Reverse((w, a, b)));
            }
        }

        PrimIter {
            _graph: graph,
            visited,
            heap,
            nodes_len: nodes.len(),
        }
    }
}

impl<'a, T, G> Iterator for PrimIter<'a, T, G>
where
    T: Node + Ord,
    G: UndirectedGraph<T> + WeightedGraph<T, i32>,
{
    type Item = PrimEvent<T>;

    /// Extrai a próxima aresta candidata do heap e decide aceitá-la ou descartá-la.
    /// Retorna `EdgeAdded` quando a aresta conecta Z a V\\Z e o novo vértice é incorporado,
    /// ou `EdgeSkipped` quando a aresta não contribui para expandir Z.
    fn next(&mut self) -> Option<Self::Item> {
        if self.visited.len() >= self.nodes_len {
            return None;
        }

        while let Some(Reverse((w, u, v))) = self.heap.pop() {
            let u_vis = self.visited.contains(&u);
            let v_vis = self.visited.contains(&v);

            if u_vis && v_vis {
                return Some(PrimEvent::EdgeSkipped(u, v, w));
            }

            if u_vis ^ v_vis {
                let new = if u_vis { v } else { u };
                let (a_out, b_out) = if u <= v { (u, v) } else { (v, u) };
                self.visited.insert(new);
                for (nv, w2) in self._graph.weighted_neighbors(new) {
                    let (aa, bb) = if new <= nv { (new, nv) } else { (nv, new) };
                    self.heap.push(Reverse((w2, aa, bb)));
                }
                return Some(PrimEvent::EdgeAdded(a_out, b_out, w));
            }

            continue;
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::AdjacencyList;
    use std::collections::{HashMap, HashSet};

    fn build_test_map() -> HashMap<usize, Vec<(usize, i32)>> {
        let mut map: HashMap<usize, Vec<(usize, i32)>> = HashMap::new();
        let insert_undir =
            |m: &mut HashMap<usize, Vec<(usize, i32)>>, a: usize, b: usize, w: i32| {
                m.entry(a).or_insert_with(Vec::new).push((b, w));
                m.entry(b).or_insert_with(Vec::new).push((a, w));
            };

        insert_undir(&mut map, 1, 3, 7);
        insert_undir(&mut map, 2, 3, 2);
        insert_undir(&mut map, 2, 5, 8);
        insert_undir(&mut map, 2, 6, 7);
        insert_undir(&mut map, 3, 4, 6);
        insert_undir(&mut map, 3, 6, 1);
        insert_undir(&mut map, 4, 7, 6);
        insert_undir(&mut map, 5, 6, 2);
        insert_undir(&mut map, 5, 8, 1);
        insert_undir(&mut map, 6, 8, 4);
        insert_undir(&mut map, 6, 9, 1);
        insert_undir(&mut map, 6, 7, 5);
        insert_undir(&mut map, 7, 10, 2);
        insert_undir(&mut map, 8, 9, 6);
        insert_undir(&mut map, 9, 10, 5);

        map
    }

    #[test]
    fn kruskal_graph_adjlist() {
        let map = build_test_map();
        let g: AdjacencyList<usize, i32> = AdjacencyList(map);

        let mut it = g.minimum_spanning_tree_kruskal();

        let mut added: Vec<(usize, usize, i32)> = Vec::new();
        while let Some(ev) = it.next() {
            match ev {
                KruskalEvent::EdgeAdded((u, v, w)) => added.push((u, v, w)),
                KruskalEvent::EdgeSkipped(_) | KruskalEvent::EdgeConsidered(_) => {}
            }
        }

        assert_eq!(added.len(), 9);

        let total_weight: i32 = added.iter().map(|(_, _, w)| *w).sum();
        assert_eq!(total_weight, 27);

        let mut got: HashSet<(usize, usize)> = HashSet::new();
        for (u, v, _) in &added {
            let e = if u < v { (*u, *v) } else { (*v, *u) };
            got.insert(e);
        }

        let mut expected: HashSet<(usize, usize)> = HashSet::new();
        expected.insert((3, 6));
        expected.insert((5, 8));
        expected.insert((6, 9));
        expected.insert((2, 3));
        expected.insert((5, 6));
        expected.insert((7, 10));
        expected.insert((6, 7));
        expected.insert((3, 4));
        expected.insert((1, 3));

        assert_eq!(got, expected);
    }

    #[test]
    fn prim_graph_adjlist() {
        let map = build_test_map();
        let g: AdjacencyList<usize, i32> = AdjacencyList(map);

        let mut it = PrimIter::new(&g);

        let mut added: Vec<(usize, usize, i32)> = Vec::new();
        while let Some(ev) = it.next() {
            match ev {
                PrimEvent::EdgeAdded(u, v, w) => added.push((u, v, w)),
                PrimEvent::EdgeSkipped(_, _, _) => {}
            }
        }

        assert_eq!(added.len(), 9);

        let total_weight: i32 = added.iter().map(|(_, _, w)| *w).sum();
        assert_eq!(total_weight, 27);

        let mut got: HashSet<(usize, usize)> = HashSet::new();
        for (u, v, _) in &added {
            let e = if u < v { (*u, *v) } else { (*v, *u) };
            got.insert(e);
        }

        let mut expected: HashSet<(usize, usize)> = HashSet::new();
        expected.insert((3, 6));
        expected.insert((5, 8));
        expected.insert((6, 9));
        expected.insert((2, 3));
        expected.insert((5, 6));
        expected.insert((7, 10));
        expected.insert((6, 7));
        expected.insert((3, 4));
        expected.insert((1, 3));

        assert_eq!(got, expected);
    }
}
