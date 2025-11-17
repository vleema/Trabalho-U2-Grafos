use std::collections::HashMap;

use graphs_algorithms::Graph;
use graphs_algorithms::WeightedGraph;
use graphs_algorithms::graphs::AdjacencyList;
use graphs_algorithms::graphs::FloydWarshallResult;
use graphs_algorithms::graphs::ShortestPathTree;

fn print_spt_recursive(
    tree: &ShortestPathTree<char, i32>,
    prefix: &str,
    is_last: bool,
    root_node: char,
    fw_result: &FloydWarshallResult<char, i32>,
) {
    let connector = if is_last { "└──" } else { "├──" };
    let dist = fw_result.dist[&root_node][&tree.node];
    println!("{}{} {} (custo: {})", prefix, connector, tree.node, dist);

    let child_prefix = format!("{}{}", prefix, if is_last { "    " } else { "│   " });

    let mut sorted_childs = tree.childs.clone();
    sorted_childs.sort_by_key(|(_, child)| child.node);

    let num_children = sorted_childs.len();
    for (i, (_, child)) in sorted_childs.iter().enumerate() {
        let is_child_last = i == num_children - 1;
        print_spt_recursive(child, &child_prefix, is_child_last, root_node, fw_result);
    }
}

fn print_spt(
    tree: &ShortestPathTree<char, i32>,
    root_node: char,
    fw_result: &FloydWarshallResult<char, i32>,
) {
    println!("{} (custo: 0)", tree.node);
    let mut sorted_childs = tree.childs.clone();
    sorted_childs.sort_by_key(|(_, child)| child.node);

    let num_children = sorted_childs.len();
    for (i, (_, child)) in sorted_childs.iter().enumerate() {
        let is_last = i == num_children - 1;
        print_spt_recursive(child, "", is_last, root_node, fw_result);
    }
}

fn print_tb(nodes: &Vec<char>, fw_result: &FloydWarshallResult<char, i32>) {
    println!("Matriz de distâncias mínimas entre todos os pares de cidades:");
    print!("      ");
    for &node in nodes {
        print!("{:>5}", node);
    }
    println!();
    println!("------|------------------------------------");

    for &from_node in nodes {
        print!("{:>5} |", from_node);
        for &to_node in nodes {
            if let Some(dist) = fw_result.dist.get(&from_node).and_then(|d| d.get(&to_node)) {
                print!("{:>5}", dist);
            } else {
                print!("{:>5}", "∞");
            }
        }
        println!();
    }
    println!();
}

fn main() {
    println!("Bem vindo à execução do algoritmo de Floyd-Warshall!");
    println!("Este algoritmo encontra o caminho mais curto entre todos os pares de vértices.");
    println!();

    // O grafo pode ser visto como um mapa de cidades e o tempo de viagem entre elas.
    // A: Araraquara
    // B: Bauru
    // C: Campinas
    // D: Dourados
    // E: Esmeraldas
    // F: Florianópolis
    let mut map: HashMap<char, Vec<(char, i32)>> = HashMap::with_capacity(6);

    map.insert('A', vec![('B', 3), ('D', 1)]);
    map.insert('B', vec![('C', 3)]);
    map.insert('C', vec![('D', 4)]);
    map.insert('D', vec![('B', 2), ('E', 6), ('F', 2)]);
    map.insert('E', vec![('C', 3)]);
    map.insert('F', vec![('A', 6), ('E', 5)]);

    let g = AdjacencyList(map);

    let result = g.floyd_warshall();

    let mut nodes: Vec<_> = g.nodes().collect();
    nodes.sort();

    print_tb(&nodes, &result);
    println!();

    {
        let root_node = 'A';
        println!("Árvore de Menores Caminhos a partir de '{}':", root_node);
        let spt = g.shortest_path_tree(root_node);
        print_spt(&spt, root_node, &result);
    }
    println!();
    {
        let root_node = 'D';
        println!("Árvore de Menores Caminhos a partir de '{}':", root_node);
        let spt = g.shortest_path_tree(root_node);
        print_spt(&spt, root_node, &result);
    }
    println!();
    {
        let root_node = 'F';
        println!("Árvore de Menores Caminhos a partir de '{}':", root_node);
        let spt = g.shortest_path_tree(root_node);
        print_spt(&spt, root_node, &result);
    }
}
