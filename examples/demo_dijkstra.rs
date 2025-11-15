use std::collections::HashMap;

use graphs_algorithms::WeightedGraph;
use graphs_algorithms::graphs::AdjacencyList;
use graphs_algorithms::graphs::DijkstraResult;

fn main() {
    println!("Bem vindo à execução do algoritmo de Dijkstra!");

    let mut map :HashMap<usize, Vec<(usize, i32)>> = HashMap::new();
    map.insert(1, vec![(11, 1), (6, 3)]);
    map.insert(2, vec![(1, 2), (3,8), (6, 7)]);
    map.insert(3, vec![(2, 1), (8, 10), (4, 2)]);
    map.insert(4, vec![(9, 9), (10, 7), (13, 15)]);
    map.insert(5, vec![(4, 4)]);
    map.insert(6, vec![(3, 9), (7, 2)]);
    map.insert(7, vec![(12, 1), (8,8)]);
    map.insert(8, vec![(9, 7)]);
    map.insert(9, vec![(14, 1), (3, 2)]);
    map.insert(10, vec![(15, 9), (14, 6)]);
    map.insert(11, vec![(6, 0), (16, 2)]);
    map.insert(12, vec![(11, 4), (17, 1)]);
    map.insert(13, vec![(18, 4), (7, 5)]);
    map.insert(14, vec![(15, 1), (19, 18)]);
    map.insert(15, vec![]);
    map.insert(16, vec![(12, 3)]);
    map.insert(17, vec![(12, 1), (19,5)]);
    map.insert(18, vec![(17, 20), (9, 2)]);
    map.insert(19, vec![]);

    let g: AdjacencyList<usize, i32> = AdjacencyList(map);

    let start = 1; 
    let mut end = 15;
    let DijkstraResult { route} = g.dijkstra(start);
    println!("Esse é o caminho entre o início = 1 e fim = 15: ");
    let mut path: Vec<(usize, usize)> = vec![];

    loop {
        if let Some(node) = route.get(&end) {

        match node.1 {
            Some(parent) => {
                path.push((parent, end));
                end = parent;
            }
            None => {
                break;
            }
        }
        }
        else { break;}
    }
    path.reverse();
    for edge in path {
        print!("{:?} ", edge);
    }
    println!();
    println!("Custo: {}", route.get(&15).unwrap().0)

}
