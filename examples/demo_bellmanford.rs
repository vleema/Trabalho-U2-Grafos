use std::collections::HashMap;

use graphs_algorithms::WeightedGraph;
use graphs_algorithms::graphs::AdjacencyList;
use graphs_algorithms::graphs::BellmanFordResult;

fn main() {
    println!("Bem vindo à execução do algoritmo de Bellman-Ford!");

    let mut map: HashMap<usize, Vec<(usize, i32)>> = HashMap::new();
    map.insert(1, vec![(11, 1), (6, 3)]);
    map.insert(2, vec![(1, 2), (3, 8), (6, 7)]);
    map.insert(3, vec![(2, 1), (8, 10), (4, 2)]);
    map.insert(4, vec![(9, 9), (10, 7), (13, 15)]);
    map.insert(5, vec![(4, 4)]);
    map.insert(6, vec![(3, 9), (7, 2)]);
    map.insert(7, vec![(12, 1), (8, 8)]);
    map.insert(8, vec![(9, 7)]);
    map.insert(9, vec![(14, 1), (3, 2)]);
    map.insert(10, vec![(15, 9), (14, 6)]);
    map.insert(11, vec![(6, 0), (16, 2)]);
    map.insert(12, vec![(11, 4), (17, 1)]);
    map.insert(13, vec![(18, 4), (7, 5)]);
    map.insert(14, vec![(15, 1), (19, 18)]);
    map.insert(15, vec![]);
    map.insert(16, vec![(12, 3)]);
    map.insert(17, vec![(12, 1), (19, 5)]);
    map.insert(18, vec![(17, 20), (9, 2)]);
    map.insert(19, vec![]);

    let g: AdjacencyList<usize, i32> = AdjacencyList(map);

    let start = 1;
    let end = 15;

    let BellmanFordResult {
        dist,
        pred,
        has_negative_cycle,
    } = g.bellman_ford(start);

    if has_negative_cycle {
        println!("O Grafo tem ciclo negativo");
    } else {
        println!("O Grafo não tem ciclo negativo");
    }

    let mut current = end;
    let mut path: Vec<(usize, i32)> = vec![];

    while current != start {
        path.push((pred[&current].unwrap(), dist[&current]));
        current = pred[&current].unwrap();
    }

    path.reverse();

    println!("======================================");

    for (p, d) in path {
        println!("Predecessor: {} | Distância: {}", p, d);
    }
}
