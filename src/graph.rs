use num_traits::{Bounded, CheckedAdd, One, Zero};

use crate::{
    graphs::{BfsIter, BiconnectedComponentsIter, DfsEdgesIter, DfsIter, DijkstraResult, Edge},
    shortest_path::FloydWarshallResult,
};
use std::{hash::Hash, iter::Sum};

/// Traço que define um nó de um grafo (orientado ou não).
pub trait Node: Eq + Hash + Copy {}

/// Implementação do traço Node.
///
/// Aqui, é definido que qualquer tipo [`T`] que implemente os traços
/// [`Eq`], `Hash` e `Copy` é candidato a ser um Node.
///
/// A princípio, não é possível definir que `String` seja um Node,
/// pois em Rust este tipo não é capaz de implementar `Copy`, somente `Clone`.
impl<T> Node for T where T: Eq + Hash + Copy {}

/// Traço que define um grafo orientado genérico.
///
/// Qualquer tipo que implementar este traço e definir suas operações é capaz de
/// representar um grafo, seja uma matriz de adjacência, estrela direta, lista
/// de adjacência e quaisquer outras.
///
/// # Tipos Genéricos
/// - `N`: Tipo que representa cada nó de um grafo, implementa `Node`.
pub trait Graph<N: Node> {
    /// Retorna a ordem do grafo, i.e. a quantidade de vértices.
    fn order(&self) -> usize;

    /// Retorna o tamanho do grafo, i.e. a quantidade de arestas.
    ///
    /// # Observações
    /// Em um grafo orientado, uma aresta `(u, v)``e uma `(v, u)`
    /// contam como arestas diferentes, ao contrário dos grafos
    /// não orientados.
    fn size(&self) -> usize;

    /// Retorna o grau interno e o grau externo de um vértice `n`
    ///
    /// # Argumentos
    /// * `n` — The node whose degrees are being queried.
    ///
    /// # Retorno
    /// Uma tupla `(usize, usize)` onde:
    /// - O primeiro elemento é o grau interno (quantas arestas
    /// entram no vértice);
    /// - O segundo elemento é o grau externo (quantas arestas
    /// saem do vértice).
    fn node_degrees(&self, n: N) -> (usize, usize);

    /// Retorna um iterador para todos os nós do grafo.
    fn nodes(&self) -> impl Iterator<Item = N>;

    /// Adiciona um novo nó no grafo.
    ///
    /// O novo nó inicialmente não tem vizinhos. Se o nó
    /// já existe, nada deve acontecer.
    fn add_node(&mut self, n: N);

    /// Removes a node and all edges connected to it.
    ///
    /// If the node does not exist, this operation has no effect.
    fn remove_node(&mut self, n: N);

    /// Adds a **directed edge** from node `n` to node `m`.
    ///
    /// If either node does not exist, this operation has no effect.
    fn add_edge(&mut self, n: N, m: N);

    /// Removes a **directed edge** from node `n` to node `m`, if it exists.
    ///
    /// If either node does not exist, this operation has no effect.
    fn remove_edge(&mut self, n: N, m: N);

    type Neighbors<'a>: Iterator<Item = N>
    where
        Self: 'a;

    /// Retorna um iterador para todos os vértices vizinhos de um nó específico.
    /// $ Argumentos
    /// * `n` - O nó cujos vizinhos serão listados e iterados.
    fn neighbors(&self, n: N) -> Self::Neighbors<'_>;

    /// Verifica se existe uma aresta direcionada do nó `n` ao nó `m`.
    fn has_edge(&self, n: N, m: N) -> bool {
        self.neighbors(n).any(|neighbor| neighbor == m)
    }

    /// Retorna um iterador para uma Busca em Profundidade (DFS) que inicia do nó
    /// indicado por `start`.
    ///
    /// O iterador retorna, a cada iteração, um `DfsEvent`, que representa um passo na travessia.
    fn dfs(&self, start: N) -> DfsIter<'_, N, Self> {
        DfsIter::new(self, start)
    }

    /// Retorna um iterador para uma Busca em Largura (BFS) que inicia do nó
    /// indicado por `start`.
    ///
    /// O iterador retorna, a cada iteração, um `BfsEvent`, que representa um passo na travessia.
    fn bfs(&self, start: N) -> BfsIter<'_, N, Self> {
        BfsIter::new(self, start)
    }

    /// Retorna um iterador para uma DFS capaz de classificar cada aresta encontrada
    /// durante a iteração.
    fn classify_edges(&self, start: N) -> DfsEdgesIter<'_, N, Self> {
        DfsEdgesIter::new(self, start)
    }
}

/// Trait defining operations for **undirected graphs**.
///
/// Extends [`Graph`], treating each edge as a bidirectional connection `(n <-> m)`.
/// Provides utility methods for manipulation and analysis of undirected graphs,
/// including connectivity checks, biconnected components, and edge classification.
pub trait UndirectedGraph<N: Node>: Graph<N> {
    /// Returns the total number of **undirected edges** in the graph.
    fn undirected_size(&self) -> usize;

    /// Verifica a conectividade do grafo e retorna um booleano.
    ///
    /// A conectividade é checada verificando se há um caminho entre todos os pares de vértices.
    fn connected(&self) -> bool;

    fn biconnected_components(&self, start: N) -> BiconnectedComponentsIter<'_, N, Self> {
        BiconnectedComponentsIter::new(self, start)
    }

    /// Adds an **undirected edge** `(n <-> m)` to the graph.
    ///
    /// Internally, this adds both directed edges `(n -> m)` and `(m -> n)`.
    fn add_undirected_edge(&mut self, n: N, m: N) {
        self.add_edge(n, m);
        self.add_edge(m, n);
    }

    /// Removes an **undirected edge** `(n <-> m)` from the graph.
    ///
    /// Internally, this removes both directed edges `(n <-> m)` and `(m <-> n)`.
    fn remove_undirected_edge(&mut self, n: N, m: N) {
        self.remove_edge(n, m);
        self.remove_edge(m, n);
    }

    /// Returns the **degree** of the given node,
    /// considering all undirected connections.
    fn undirected_node_degree(&self, n: N) -> usize {
        self.neighbors(n).count()
    }

    /// Returns an iterator classifying the **undirected edges** of the graph.
    ///
    /// Only edges of types [`Edge::Tree`] and [`Edge::Back`] are considered,
    /// as these represent meaningful relations in undirected graphs.
    fn classify_undirected_edges<'a>(&'a self, start: N) -> impl Iterator<Item = Edge<N>>
    where
        N: 'a,
    {
        DfsEdgesIter::new(self, start)
            .filter(|edge| matches!(edge, Edge::Tree(_, _) | Edge::Back(_, _)))
    }
}

/// Traço que define o tipo para o peso de uma aresta ponderada.
///
/// Este traço é importante para não haver limitação de valores para um peso,
/// permitindo pesos negativos, positivos, pequenos, grandes, inteiros, decimais,
/// entre demais tipos numéricos.
///
pub trait Weight: CheckedAdd + Ord + Bounded + Zero + One + Copy {}

/// Implementação do traço `Weight`.
///
/// Aqui, é definido que qualquer tipo `T` que implemente os traços listados
/// é um bom candidato para ser o peso de uma aresta. Isto inclui todos os tipos
/// numéricos, indo de números sem sinal até de ponto flutuante.
///
/// Vale notar que tais traços vêm, em sua maioria, do crate `num_traits`.
impl<T> Weight for T where T: CheckedAdd + Ord + Bounded + One + Zero + Copy + Sum {}

/// Traço que define um grafo ponderado genérico.
///
/// Para implementar este traço é necessário que o tipo implemente também o traço `Graph`.
/// Implementar este traço é estender o grafo original para o uso de arestas ponderadas.
///
/// Este traço contém métodos úteis para geração de árvores geradoras mínimas e
/// detecção do caminho mais curto entre vértices.
///
/// # Tipos Genéricos
/// - `N`: qualquer tipo que implemente o traço `Node`;
/// - `W`: qualquer tipo que implemente o traço `Weight`;
pub trait WeightedGraph<N: Node, W: Weight>: Graph<N> {
    type WeightedNeighbors<'a>: Iterator<Item = (N, W)>
    where
        Self: 'a;

    /// Retorna um iterador para todos os vértices vizinhos de um nó específico `n`.
    ///
    /// Este iterador guarda uma dupla, onde:
    /// - 1º elemento é o valor do vértice em si;
    /// - 2º elemento é o peso da aresta entre o vértice `n` e o vizinho.
    fn weighted_neighbors(&self, n: N) -> Self::WeightedNeighbors<'_>;

    /// Adiciona uma aresta ponderada ao grafo.
    ///
    /// # Argumentos
    /// - `n`: vértice  
    fn add_weighted_edge(&mut self, n: N, m: N, w: W);

    /// Executa o algoritmo de Dijkstra no grafo a fim de encontrar o caminho mais curto
    /// para todos os vértices a partir de uma origem.
    ///
    /// # Argumentos
    /// - `start`: origem da busca
    ///
    /// # Retorno
    /// - Uma struct `DijkstraResult` com o campo `route` que guarda todos os dados
    /// necessários para visualizar o caminho mais curto entre os vértices.
    fn dijkstra(&self, start: N) -> DijkstraResult<N, W> {
        DijkstraResult::new(self, start)
    }

    /// Executa o algoritmo de Floyd-Warshall no grafo a fim de encontrar o
    /// caminho mais curto dentre todos os pares de vértices.
    ///
    /// # Retorno
    /// Uma struct `FloydWarshallResult` com dois dicionários:
    /// - `dist`: armazena a distância de cada vértice para todos os outros;
    /// - `pred`: armazena o predecessor de cada vértice para que possa chegar em cada um;
    fn floyd_warshall(&self) -> FloydWarshallResult<N, W> {
        FloydWarshallResult::new(self)
    }
}
