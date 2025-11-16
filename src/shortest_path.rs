use crate::graph::Node;
use crate::graph::Weight;
use crate::graph::WeightedGraph;
use std::collections::{HashMap, HashSet};

/// Struct que guarda o Caminho Mais Curto de um vértice raiz a todos os outros,
/// descoberto através do Algoritmo de Dijkstra.
///
/// [`DijkstraResult`] guarda no campo `route` um dicionário,
/// onde as chaves são todos os vértices do grafo e os valores uma dupla,
/// onde o 1º elemento guarda a distância até o vértice e o 2º guarda o predecessor dele.
///
/// Para montar o caminho mais curto de A até B, é possível iniciar uma busca no dicionário
/// por B e adentrar em seus predecessores até A.
pub struct DijkstraResult<Node, Weight> {
    pub route: HashMap<Node, (Weight, Option<Node>)>,
}

/// Bloco de implementação para a [`DijkstraResult`] com a função `new()`.
///
impl<N: Node, W: Weight> DijkstraResult<N, W> {
    /// Método que executa o Algoritmo de Dijkstra e retorna um [`DijkstraResult`]
    ///
    /// ## Argumentos
    /// * `graph`: um tipo que implementa o traço [`WeightedGraph`], como [`AdjacencyList`]
    /// * `start`: o nó inicial, deve implementar o tipo [`N`]
    ///
    /// ## Fluxo
    /// * Inicia marcando a distância do vértice `start` como 0 e seu predecessor como `None`;
    /// * Explora os vizinhos do vértice `start` e determina sua distância e predecessor
    /// * Loop principal: enquanto existir vértice não visitado no grafo
    ///     * Recupera o vértice de menor distância e o visita;
    ///     * Explora seus vizinhos não visitados e atualiza suas distâncias e predecessores, caso seja vantajoso
    ///     * Salva o vértice visitado na rota final
    /// * Retorna um [`DijkstraResult`] onde o campo `route` contém todas as informações necessárias para elaborar
    ///   o caminho mais curto entre quaisquer vértices.
    ///
    /// ## Observações
    /// * São utilizados os conjuntos e dicionários auxiliares `visited`, `distance` e `pred`,
    ///   que representam os vértices visitados, a distância até vértice `x` e o predecessor do vértice `x`.
    ///
    pub fn new(graph: &(impl WeightedGraph<N, W> + ?Sized), start: N) -> Self {
        let mut route: HashMap<N, (W, Option<N>)> = HashMap::new();
        let mut visited: HashSet<N> = HashSet::new();
        let mut distance: HashMap<N, W> = HashMap::new();
        let mut pred: HashMap<N, Option<N>> = HashMap::new();
        distance.insert(start, W::zero());
        pred.insert(start, None);

        for (neighbor, weight) in graph.weighted_neighbors(start) {
            pred.insert(neighbor, Some(start));
            distance.insert(neighbor, weight);
        }

        loop {
            let mut unvisited_node: Option<(N, W)> = None;
            for node in graph.nodes() {
                if !visited.contains(&node)
                    && let Some(distance) = distance.get(&node)
                    && (unvisited_node.is_none()
                        || (unvisited_node.is_some() && distance < &unvisited_node.unwrap().1))
                {
                    unvisited_node = Some((node, *distance));
                }
            }

            match unvisited_node {
                None => break,
                Some((node, node_weight)) => {
                    visited.insert(node);

                    for (neighbor, weight) in graph.weighted_neighbors(node) {
                        if !visited.contains(&neighbor) {
                            let new_distance = weight + node_weight;

                            match distance.get(&neighbor) {
                                Some(&neighbor_distance) => {
                                    if neighbor_distance > new_distance {
                                        distance.insert(neighbor, new_distance);
                                        pred.insert(neighbor, Some(node));
                                    }
                                }
                                None => {
                                    distance.insert(neighbor, new_distance);
                                    pred.insert(neighbor, Some(node));
                                }
                            }
                        }
                    }

                    let mut parent: Option<N> = None;
                    if let Some(opt) = pred.get(&node) {
                        parent = *opt;
                    }

                    route.insert(node, (node_weight, parent));
                }
            }
        }
        Self { route }
    }
}

/// Struct que guarda o Caminho Mais Curto de um vértice raiz a todos os outros,
/// descoberto através do Algoritmo de Bellman-Ford.
///
/// [`BellmanFordResult`] guarda os campos:
/// - `dist`: dicionário com a relação vértice-custo para alcançá-lo
/// - `pred`: dicionário com precedência do caminho
/// - `has_negative_cycle`: se tem ciclo ou não
///
/// Para montar o caminho mais curto de A até B, é possível iniciar uma busca no dicionário
/// por B e adentrar em seus predecessores até A.
pub struct BellmanFordResult<Node, Weight> {
    pub dist: HashMap<Node, Weight>,
    pub pred: HashMap<Node, Option<Node>>,
    pub has_negative_cycle: bool,
}

impl<N: Node, W: Weight> BellmanFordResult<N, W> {
    /// Método que executa o Algoritmo de Bellman-Ford e retorna um [`BellmanFordResult`]
    ///
    /// ## Argumentos
    /// * `graph`: um tipo que implementa o traço [`WeightedGraph`], como [`AdjacencyList`]
    /// * `start`: o nó inicial, deve implementar o tipo [`N`]
    ///
    /// ## Fluxo
    /// * Marca todos os vértices com o predecessor `None`;
    /// * Atribui distância infinita para todos os vértices, com exceção para `start`;
    /// * Explora os vizinhos do vértice `start` e determina sua distância e predecessor
    /// * Loop principal: será repetido o seguinte processo n - 1 vezes:
    ///     * Para todo nó, verifique:
    ///         * Para toda aresta (u,v) que "sai" desse nó:
    ///             * Verifique a desigualdade triangular do custo das distâncias
    ///             * Caso sejá mais vantajoso, atualize a distância e a precedência daquele vértice
    /// * Loop secundário: para toda aresta, verifique:
    ///     * Se (u,v) é a melhor alternativa para chegar no vizinho
    ///     * Caso não, há um ciclo negativo
    /// * Retorna um [`BellmanFordResult`] com as variáveis locais `dist`, `pred` e `has_negative_cycle`.
    pub fn new(g: &(impl WeightedGraph<N, W> + ?Sized), start: N) -> Self {
        let mut dist = HashMap::new();
        let mut pred = HashMap::new();

        // inicialização
        for n in g.nodes() {
            pred.insert(n, None);
            dist.insert(n, W::max_value());
        }

        dist.insert(start, W::zero());

        // relaxa todas as arestar n-1 vezes
        for _i in 1..g.order() {
            for out_node in g.nodes() {
                for (in_node, weight) in g.weighted_neighbors(out_node) {
                    let new_dist = dist[&out_node].saturating_add(&weight);

                    if dist[&in_node] > new_dist {
                        dist.insert(in_node, new_dist);
                        pred.insert(in_node, Some(out_node));
                    }
                }
            }
        }

        let mut has_negative_cycle = false;

        // itera por todas as arestas para verificar ciclos
        for out_node in g.nodes() {
            for (in_node, weight) in g.weighted_neighbors(out_node) {
                if dist[&in_node] > dist[&out_node].saturating_add(&weight) {
                    has_negative_cycle = true;
                }
            }
        }

        Self {
            dist,
            pred,
            has_negative_cycle,
        }
    }
}

#[derive(Debug)]
pub struct FloydWarshallResult<Node, Weight> {
    pub dist: HashMap<Node, HashMap<Node, Weight>>,
    pub pred: HashMap<Node, HashMap<Node, Node>>,
}

impl<N: Node, W: Weight> FloydWarshallResult<N, W> {
    pub fn new(g: &(impl WeightedGraph<N, W> + ?Sized)) -> Self {
        let mut dist = HashMap::with_capacity(g.order());
        let mut pred = HashMap::with_capacity(g.order());
        for n in g.nodes() {
            let mut neighbors_dist = HashMap::new();
            let mut neighors_pred = HashMap::new();

            neighbors_dist.insert(n, W::zero());
            neighors_pred.insert(n, n);

            for (neighbor, weight) in g.weighted_neighbors(n) {
                neighbors_dist.insert(neighbor, weight);
                neighors_pred.insert(neighbor, n);
            }

            dist.insert(n, neighbors_dist);
            pred.insert(n, neighors_pred);
        }

        let unwrap_dist = |dist: &HashMap<N, HashMap<N, W>>, i, j| {
            dist.get(&i)
                .and_then(|ds| ds.get(&j))
                .copied()
                .unwrap_or(W::max_value())
        };

        for k in g.nodes() {
            for i in g.nodes() {
                for j in g.nodes() {
                    let dist_ik = unwrap_dist(&dist, i, k);
                    let dist_kj = unwrap_dist(&dist, k, j);
                    let dist_ij = unwrap_dist(&dist, i, j);
                    if let Some(sum) = dist_ik.checked_add(&dist_kj)
                        && sum < dist_ij
                    {
                        dist.entry(i).and_modify(|ds| {
                            ds.entry(j).and_modify(|d| *d = sum).or_insert(sum);
                        });
                        let pred_kj = pred[&k][&j];
                        pred.entry(i).and_modify(|ps| {
                            ps.entry(j).and_modify(|p| *p = pred_kj).or_insert(pred_kj);
                        });
                    }
                }
            }
        }

        Self { dist, pred }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct ShortestPathTree<N, W> {
    pub node: N,
    pub childs: Vec<(W, ShortestPathTree<N, W>)>,
}

impl<N: Node, W: Weight> ShortestPathTree<N, W> {
    pub fn new(g: &(impl WeightedGraph<N, W> + ?Sized), root: N) -> Self {
        fn build_tree<N: Node, W: Weight>(
            visited: &mut HashSet<N>,
            floyd: &FloydWarshallResult<N, W>,
            tree: &mut ShortestPathTree<N, W>,
            root: N,
        ) {
            for (&k, &w) in &floyd.dist[&tree.node] {
                if k != tree.node && floyd.pred[&root][&k] == tree.node {
                    if !visited.insert(k) {
                        continue;
                    }
                    let mut new_child = ShortestPathTree {
                        node: k,
                        childs: vec![],
                    };
                    build_tree(visited, floyd, &mut new_child, root);
                    tree.childs.push((w, new_child));
                }
            }
        }
        let floyd = g.floyd_warshall();
        let mut tree = ShortestPathTree {
            node: root,
            childs: vec![],
        };

        build_tree(&mut HashSet::from([root]), &floyd, &mut tree, root);

        tree
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::graphs::AdjacencyList;

    #[test]
    fn dijkstra_graph() {
        let mut map: HashMap<usize, Vec<(usize, i32)>> = HashMap::new();
        let vec1: Vec<(usize, i32)> = vec![(2, 2), (3, 4), (4, 5)];
        let vec2: Vec<(usize, i32)> = vec![(1, 2), (4, 2)];
        let vec3: Vec<(usize, i32)> = vec![(1, 4), (4, 1), (6, 4)];
        let vec4: Vec<(usize, i32)> = vec![(1, 5), (2, 2), (3, 1), (5, 2), (6, 3)];
        let vec5: Vec<(usize, i32)> = vec![(4, 2), (6, 1), (7, 5)];
        let vec6: Vec<(usize, i32)> = vec![(3, 4), (4, 3), (5, 1), (7, 7)];
        let vec7: Vec<(usize, i32)> = vec![(5, 5), (6, 7), (7, 0)];

        map.insert(1, vec1);
        map.insert(2, vec2);
        map.insert(3, vec3);
        map.insert(4, vec4);
        map.insert(5, vec5);
        map.insert(6, vec6);
        map.insert(7, vec7);

        let g: AdjacencyList<usize, i32> = AdjacencyList(map);
        let DijkstraResult { route } = g.dijkstra(1);

        assert_eq!(route.len(), 7);
        assert_eq!(route.get(&1).unwrap().0, 0);
        assert_eq!(route.get(&2).unwrap().0, 2);
        assert_eq!(route.get(&3).unwrap().0, 4);
        assert_eq!(route.get(&4).unwrap().0, 4);
        assert_eq!(route.get(&5).unwrap().0, 6);
        assert_eq!(route.get(&6).unwrap().0, 7);
        assert_eq!(route.get(&7).unwrap().0, 11);
        assert_eq!(route.get(&1).unwrap().1, None);
        assert_eq!(route.get(&2).unwrap().1, Some(1));
        assert_eq!(route.get(&3).unwrap().1, Some(1));
        assert_eq!(route.get(&4).unwrap().1, Some(2));
        assert_eq!(route.get(&5).unwrap().1, Some(4));
        assert_eq!(route.get(&6).unwrap().1, Some(4));
        assert_eq!(route.get(&7).unwrap().1, Some(5));
    }

    #[test]
    fn dijkstra_digraph() {
        let mut map: HashMap<char, Vec<(char, i32)>> = HashMap::new();
        let vec1: Vec<(char, i32)> = vec![('B', 5), ('C', 2)];
        let vec2: Vec<(char, i32)> = vec![('C', 1), ('D', 4), ('E', 2)];
        let vec3: Vec<(char, i32)> = vec![('E', 7)];
        let vec4: Vec<(char, i32)> = vec![('E', 5), ('F', 3)];
        let vec5: Vec<(char, i32)> = vec![('F', 1)];
        let vec6: Vec<(char, i32)> = vec![];

        map.insert('A', vec1);
        map.insert('B', vec2);
        map.insert('C', vec3);
        map.insert('D', vec4);
        map.insert('E', vec5);
        map.insert('F', vec6);

        let g: AdjacencyList<char, i32> = AdjacencyList(map);
        let DijkstraResult { route } = g.dijkstra('A');

        assert_eq!(route.len(), 6);
        assert_eq!(route.get(&'A').unwrap().0, 0);
        assert_eq!(route.get(&'B').unwrap().0, 5);
        assert_eq!(route.get(&'C').unwrap().0, 2);
        assert_eq!(route.get(&'D').unwrap().0, 9);
        assert_eq!(route.get(&'E').unwrap().0, 7);
        assert_eq!(route.get(&'F').unwrap().0, 8);
        assert_eq!(route.get(&'A').unwrap().1, None);
        assert_eq!(route.get(&'B').unwrap().1, Some('A'));
        assert_eq!(route.get(&'C').unwrap().1, Some('A'));
        assert_eq!(route.get(&'D').unwrap().1, Some('B'));
        assert_eq!(route.get(&'E').unwrap().1, Some('B'));
        assert_eq!(route.get(&'F').unwrap().1, Some('E'));
    }

    #[test]
    fn bellman_ford() {
        let mut map: HashMap<char, Vec<(char, i32)>> = HashMap::new();

        // exemplo do slide
        map.insert('A', vec![('B', 10), ('F', 8)]);
        map.insert('B', vec![('D', 2)]);
        map.insert('C', vec![('B', 1)]);
        map.insert('D', vec![('C', -2)]);
        map.insert('E', vec![('B', -4), ('D', -1)]);
        map.insert('F', vec![('E', 1)]);

        let g: AdjacencyList<char, i32> = AdjacencyList(map);
        let BellmanFordResult {
            dist,
            pred,
            has_negative_cycle,
        } = g.bellman_ford('A');

        assert_eq!(dist[&'A'], 0); // A
        assert_eq!(dist[&'B'], 5); // A -> F -> E -> B
        assert_eq!(dist[&'C'], 5); // A -> F -> E -> B -> D -> C
        assert_eq!(dist[&'D'], 7); // A -> F -> E -> B -> D
        assert_eq!(dist[&'E'], 9); // A -> F -> E
        assert_eq!(dist[&'F'], 8); // A -> F

        assert_eq!(pred[&'A'], None); // A
        assert_eq!(pred[&'B'], Some('E')); // A -> F -> E -> B
        assert_eq!(pred[&'C'], Some('D')); // A -> F -> E -> B -> D -> C
        assert_eq!(pred[&'D'], Some('B')); // A -> F -> E -> B -> D
        assert_eq!(pred[&'E'], Some('F')); // A -> F -> E
        assert_eq!(pred[&'F'], Some('A')); // A -> F

        assert_eq!(has_negative_cycle, false);
    }

    #[test]
    fn floyd_warshall() {
        let mut map: HashMap<char, Vec<(char, i32)>> = HashMap::with_capacity(6);

        map.insert('A', vec![('B', 5), ('C', 2)]);
        map.insert('B', vec![('C', 1), ('D', 4), ('E', 2)]);
        map.insert('C', vec![('E', 7)]);
        map.insert('D', vec![('E', 5), ('F', 3)]);
        map.insert('E', vec![('F', 1)]);
        map.insert('F', vec![]);

        let g = AdjacencyList(map);
        let FloydWarshallResult { dist, pred } = g.floyd_warshall();

        assert_eq!(dist[&'A'][&'B'], 5); // A -> B
        assert_eq!(dist[&'A'][&'C'], 2); // A -> C
        assert_eq!(dist[&'A'][&'D'], 9); // A -> C -> B -> D
        assert_eq!(dist[&'A'][&'E'], 7); // A -> B -> E
        assert_eq!(dist[&'A'][&'F'], 8); // A -> B -> E -> F

        assert_eq!(pred[&'A'][&'B'], 'A'); // A -> B
        assert_eq!(pred[&'A'][&'E'], 'B'); // A -> B -> E
        assert_eq!(pred[&'A'][&'F'], 'E'); // A -> B -> E -> F

        assert_eq!(pred[&'F'].get(&'A'), None);
    }

    #[test]
    fn shortest_path_tree() {
        let mut map: HashMap<char, Vec<(char, i32)>> = HashMap::with_capacity(6);

        map.insert('A', vec![('B', 3), ('D', 1)]);
        map.insert('B', vec![('C', 3)]);
        map.insert('C', vec![('D', 4)]);
        map.insert('D', vec![('B', 2), ('E', 6), ('F', 2)]);
        map.insert('E', vec![('C', 3)]);
        map.insert('F', vec![('A', 6), ('E', 5)]);

        fn sort_tree<N: Ord + Copy, W: Ord + Copy>(tree: &mut ShortestPathTree<N, W>) {
            tree.childs.sort_by_key(|(w, _)| *w);
            for (_, child) in &mut tree.childs {
                sort_tree(child);
            }
        }

        let g = AdjacencyList(map);
        let expected = ShortestPathTree {
            node: 'A',
            childs: vec![
                (
                    1,
                    ShortestPathTree {
                        node: 'D',
                        childs: vec![
                            (
                                2,
                                ShortestPathTree {
                                    node: 'F',
                                    childs: vec![],
                                },
                            ),
                            (
                                6,
                                ShortestPathTree {
                                    node: 'E',
                                    childs: vec![],
                                },
                            ),
                        ],
                    },
                ),
                (
                    3,
                    ShortestPathTree {
                        node: 'B',
                        childs: vec![(
                            3,
                            ShortestPathTree {
                                node: 'C',
                                childs: vec![],
                            },
                        )],
                    },
                ),
            ],
        };
        let mut result = g.shortest_path_tree('A');
        sort_tree(&mut result);
        assert_eq!(expected, result);
    }
}
