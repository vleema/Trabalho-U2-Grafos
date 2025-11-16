//! Estruturas de dados e algoritmos para Grafos.
//!
//! Crate que fornece algoritmos e estruturas de dados para Grafos.
//!
//! A organização do crate é feita em diversos módulos:
//! - `adjacency_list`: guarda a representação de um grafo no formato da Lista de Adjacência,
//! bastante popular e comum de implementar;
//! - `eulerian_cycle`: armazena os algoritmos para detecção de ciclos e caminhos eulerianos em um
//! grafo;
//! - `minimum_spanning_tree`: armazena os algoritmos para a criação de árvores geradoras mínimas a
//! partir de um grafo. Os algoritmos incluem Kruskal, Prim e Boruvka;
//! - `shortest_path`: armazena os algoritmos para a detecção do caminho mais curto em um grafo. Os
//! algoritmos incluem Dijkstra, Bellman-Ford e Floyd-Warshall;
//! - `traversal`: armazena os algoritmos para a travessia em um grafo. Os algoritmos incluem a
//! BFS, DFS, DFS com classificação de arestas e identificação de componentes.

#![feature(impl_trait_in_assoc_type)]

mod adjacency_list;
mod eulerian_cycle;
mod graph;
mod minimum_spanning_tree;
mod shortest_path;
mod traversal;

pub use graph::Graph;
pub use graph::Node;
pub use graph::UndirectedGraph;
pub use graph::WeightedGraph;

pub mod graphs {
    pub use crate::adjacency_list::AdjacencyList;
    pub use crate::shortest_path::DijkstraResult;
    pub use crate::traversal::BfsEvent;
    pub use crate::traversal::BfsIter;
    pub use crate::traversal::BiconnectedComponentsIter;
    pub use crate::traversal::DfsEdgesIter;
    pub use crate::traversal::DfsEvent;
    pub use crate::traversal::DfsIter;
    pub use crate::traversal::Edge;
}
