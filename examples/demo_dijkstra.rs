use graphs_algorithms::Graph;
use graphs_algorithms::graphs::AdjacencyList;
use graphs_algorithms::graphs::DijkstraEvent;
use graphs_algorithms::graphs::DijkstraIter;
use std::collections::HashMap;

fn main() {
    println!("Bem vindo à execução do algoritmo de Dijkstra!");
    let mut g: AdjacencyList<usize> = AdjacencyList::new();

    let edges = vec![
        (1, 6, 3),
        (1, 11, 1),
        (2, 1, 2),
        (2, 6, 7),
        (2, 3, 8),
        (3, 2, 1),
        (3, 8, 10),
        (3, 4, 2),
        (4, 9, 9),
        (4, 10, 7),
        (4, 13, 15),
        (5, 4, 4),
        (6, 3, 9),
        (6, 7, 2),
        (7, 8, 8),
        (7, 12, 1),
        (8, 9, 7),
        (9, 3, 2),
        (9, 14, 1),
        (10, 5, 5),
        (10, 14, 6),
        (10, 15, 9),
        (11, 6, 0),
        (11, 16, 2),
        (12, 11, 4),
        (12, 17, 1),
        (13, 7, 5),
        (13, 18, 4),
        (14, 15, 1),
        (14, 19, 18),
        (16, 12, 3),
        (17, 12, 1),
        (17, 19, 5),
        (18, 9, 2),
        (18, 17, 20),
    ];

    for i in 1..=19 {
        g.add_node(i);
    }

    for (u, v, w) in edges {
        g.add_edge(u, v, w);
    }

    let mut iter: DijkstraIter<'_, usize, AdjacencyList<usize>> = g.shortest_path_dijkstra(1);
    let mut discovered_edges: HashMap<usize, (Option<usize>, i32)> = HashMap::new();
    while let Some(event) = iter.next() {
        match event {
            DijkstraEvent::Finish => {}
            DijkstraEvent::Discover((u, w, v)) => {
                discovered_edges.insert(u, (v, w));
            }
        }
    }

    println!("O caminho mais curto entre s = 1 e fim = 15 é: ");
    let mut path: Vec<(usize, usize)> = vec![];
    let mut start: usize = 15;
    let distance = discovered_edges.get(&start).unwrap().1;
    loop {
        let node = discovered_edges.get(&start).unwrap();
        match node.0 {
            Some(parent) => {
                path.push((parent, start));
                start = parent;
            }
            None => {
                break;
            }
        }
    }
    path.sort_by(|n1, n2| n1.0.cmp(&n2.0));
    for edge in path {
        print!("{:?} ", edge);
    }
    println!("");
    println!("Custo: {}", distance);
}
