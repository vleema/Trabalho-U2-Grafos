use graphs_algorithms::eulerian_graph::{hierholzer, UndirectedGraph};
use graphs_algorithms::Graph;
use graphs_algorithms::graphs::AdjacencyList;

fn main() {
    demo_eulerian_cycle();
    println!("\n------------------------------------------------\n");
    demo_eulerian_path();
}

fn demo_eulerian_cycle() {
    println!("GRAFO 1: Ciclo Euleriano (Direcionado)");
    println!("Vértices: A, B, C, D, E, F");

    let mut graph = AdjacencyList::<char, i32>::new();

    graph.add_node('A');
    graph.add_node('B');
    graph.add_node('C');
    graph.add_node('D');
    graph.add_node('E');
    graph.add_node('F');

    graph.add_edge('A', 'B');
    graph.add_edge('A', 'F');
    graph.add_edge('B', 'A');
    graph.add_edge('B', 'D');
    graph.add_edge('C', 'B');
    graph.add_edge('D', 'B');
    graph.add_edge('D', 'C');
    graph.add_edge('E', 'A');
    graph.add_edge('E', 'D');
    graph.add_edge('F', 'E');

    let result = hierholzer(&graph);

    println!("Resultado:");
    println!("- Tem ciclo euleriano: {}", result.has_eulerian_cycle);
    println!("- Tem caminho euleriano: {}", result.has_eulerian_path);
    println!("- Caminho encontrado: {:?}", result.path);

    if result.has_eulerian_cycle {
        println!("\n✅ O grafo possui um CICLO EULERIANO!");
        println!("Começa e termina no mesmo vértice: {} → ... → {}",
                 result.path[0], result.path[result.path.len()-1]);

        let expected_length = 9 + 1;
        if result.path.len() == expected_length {
            println!("Percorre todas as {} arestas exatamente uma vez", 9);
        }
    } else if result.has_eulerian_path {
        println!("\nO grafo possui um CAMINHO EULERIANO!");
    } else {
        println!("\nO grafo NÃO é euleriano");
    }
}


fn demo_eulerian_path() {
    println!("GRAFO 2: Caminho Euleriano (Direcionado)");
    println!("Vértices: 1, 2, 3, 4, 5, 6, 7");

    let mut graph = UndirectedGraph::new();

    graph.add_node('1');
    graph.add_node('2');
    graph.add_node('3');
    graph.add_node('4');
    graph.add_node('5');
    graph.add_node('6');
    graph.add_node('7');

    graph.add_edge('1', '2');
    graph.add_edge('1', '3');
    graph.add_edge('2', '3');
    graph.add_edge('2', '4');
    graph.add_edge('2', '5');
    graph.add_edge('3', '4');
    graph.add_edge('3', '6');
    graph.add_edge('4', '5');
    graph.add_edge('4', '6');
    graph.add_edge('5', '6');
    graph.add_edge('5', '7');
    graph.add_edge('6', '7');

    let result = hierholzer(&graph);

    println!("Resultado:");
    println!("- Tem ciclo euleriano: {}", result.has_eulerian_cycle);
    println!("- Tem caminho euleriano: {}", result.has_eulerian_path);
    println!("- Caminho encontrado: {:?}", result.path);

    if result.has_eulerian_cycle {
        println!("\nO grafo possui um CICLO EULERIANO!");
    } else if result.has_eulerian_path {
        println!("\nO grafo possui um CAMINHO EULERIANO!");
        if !result.path.is_empty() {
            println!("Começa em {} e termina em {}",
                     result.path[0], result.path[result.path.len()-1]);
        }
    } else {
        println!("\n❌ O grafo NÃO é euleriano");
    }
}