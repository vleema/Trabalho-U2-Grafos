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
    /// o caminho mais curto entre quaisquer vértices.
    /// 
    /// ## Observações
    /// * São utilizados os conjuntos e dicionários auxiliares `visited`, `distance` e `pred`,
    /// que representam os vértices visitados, a distância até vértice `x` e o predecessor do vértice `x`.
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
        let DijkstraResult { route }= g.dijkstra('A');

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
    fn floyd_warshall() {
        let mut map: HashMap<char, Vec<(char, i32)>> = HashMap::with_capacity(6);

        map.insert('A', vec![('B', 5), ('C', 2)]);
        map.insert('B', vec![('C', 1), ('D', 4), ('E', 2)]);
        map.insert('C', vec![('E', 7)]);
        map.insert('D', vec![('E', 5), ('F', 3)]);
        map.insert('E', vec![('F', 1)]);
        map.insert('F', vec![]);

        let g: AdjacencyList<char, i32> = AdjacencyList(map);
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
}
