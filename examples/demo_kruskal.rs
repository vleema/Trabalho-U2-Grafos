use graphs_algorithms::KruskalEvent;
use graphs_algorithms::UndirectedGraph;
use graphs_algorithms::graphs::AdjacencyList;
use std::collections::HashMap;

fn build_test_map() -> HashMap<usize, Vec<(usize, i32)>> {
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

    // escolhe o menor peso para cada aresta não direcionada
    let mut best: HashMap<(usize, usize), i32> = HashMap::new();
    for (a, b, w) in edges {
        let key = if a <= b { (a, b) } else { (b, a) };
        best.entry(key)
            .and_modify(|existing| {
                if w < *existing {
                    *existing = w
                }
            })
            .or_insert(w);
    }

    // constrói o mapa de adjacência como HashMap<node, Vec<(node, peso)>>
    let mut map: HashMap<usize, Vec<(usize, i32)>> = HashMap::new();
    for ((u, v), w) in best {
        map.entry(u).or_insert_with(Vec::new).push((v, w));
        map.entry(v).or_insert_with(Vec::new).push((u, w));
    }
    map
}

fn main() {
    println!("Demo Kruskal - grafo de exemplo (não direcionado)");

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

    println!("Arestas da MST (Kruskal):");
    for (u, v, w) in &added {
        println!("{} - {} (peso {})", u, v, w);
    }
    let total: i32 = added.iter().map(|(_, _, w)| *w).sum();
    println!("Peso total: {}", total);
}
