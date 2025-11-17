use num_traits::{Bounded, CheckedAdd, One, SaturatingAdd, Zero};

use crate::{
    graphs::{BfsIter, DfsIter, DijkstraResult},
    shortest_path::{BellmanFordResult, FloydWarshallResult, ShortestPathTree},
};
use std::{fmt::Debug, hash::Hash, iter::Sum};

/// Traço que define um nó de um grafo (orientado ou não).
pub trait Node: Eq + Hash + Copy + Debug + Ord {}

/// Implementação do traço Node.
///
/// Aqui, é definido que qualquer tipo [`T`] que implemente os traços
/// [`Eq`], `Hash`, `Copy`, `Debug` e `Ord` é candidato a ser um Node.
///
/// A princípio, não é possível definir que `String` seja um Node,
/// pois em Rust este tipo não é capaz de implementar `Copy`, somente `Clone`.
impl<T> Node for T where T: Eq + Hash + Copy + Debug + Ord {}

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
    ///   entram no vértice);
    /// - O segundo elemento é o grau externo (quantas arestas
    ///   saem do vértice).
    fn node_degrees(&self, n: N) -> (usize, usize);

    /// Retorna um iterador para todos os nós do grafo.
    fn nodes(&self) -> impl Iterator<Item = N>;

    /// Adiciona um novo nó no grafo.
    ///
    /// O novo nó inicialmente não tem vizinhos. Se o nó
    /// já existe, nada deve acontecer.
    fn add_node(&mut self, n: N);

    /// Adiciona uma nova aresta no grafo que vai do nó `n` ao nó `m`.
    ///
    /// Se nenhum dos nós existe, nada acontece.
    fn add_edge(&mut self, n: N, m: N);

    /// Remove a aresta no grafo que vai do nó `n` ao nó `m`.
    ///
    /// Se nenhum dos nós existe, nada acontece.
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

    /// Retorna uma indicação de que o grafo atual é direcionado.
    fn is_directed(&self) -> bool {
        true
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
}

/// Traço que define um grafo não orientado genérico.
///
/// Este traço estende o traço [`Graph`] e trata cada aresta como bidirecional.
///
/// Qualquer tipo que implementar este traço e definir suas operações é capaz de
/// representar um grafo não orientado, seja uma matriz de adjacência,
/// estrela direta, lista de adjacência e quaisquer outras.
///
/// # Tipos Genéricos
/// - `N`: Tipo que representa cada nó de um grafo, implementa `Node`.
pub trait UndirectedGraph<N: Node>: Graph<N> {
    /// Retorna uma indicação de que o grafo atual é direcionado.
    fn is_directed() -> bool {
        false
    }

    /// Adiciona uma aresta não direcionada no grafo entre os nós `n` e `m`.
    ///
    /// Internamente, adiciona duas arestas orientadas de `n` para `m` e de `m` para `n`.
    fn add_undirected_edge(&mut self, n: N, m: N) {
        self.add_edge(n, m);
        self.add_edge(m, n);
    }

    /// Remove a aresta não direcionada no grafo entre os nós `n` e `m`.
    ///
    /// Internamente, remove as arestas orientadas tanto de `n` para `m` quanto `m` para `n`.
    fn remove_undirected_edge(&mut self, n: N, m: N) {
        self.remove_edge(n, m);
        self.remove_edge(m, n);
    }

    /// Calcula o grau do vértice `n`.
    fn undirected_node_degree(&self, n: N) -> usize {
        self.neighbors(n).count()
    }

    fn minimum_spanning_tree_kruskal(
        &self,
    ) -> crate::minimum_spanning_tree::KruskalIter<'_, N, Self>
    where
        N: Ord,
        Self: WeightedGraph<N, i32>,
    {
        crate::minimum_spanning_tree::KruskalIter::new(self)
    }

    fn minimum_spanning_tree_prim(&self) -> crate::minimum_spanning_tree::PrimIter<'_, N, Self>
    where
        N: Ord,
        Self: WeightedGraph<N, i32>,
    {
        crate::minimum_spanning_tree::PrimIter::new(self)
    }
}

/// Traço que define o tipo para o peso de uma aresta ponderada.
///
/// Este traço é importante para não haver limitação de valores para um peso,
/// permitindo pesos negativos, positivos, pequenos, grandes, inteiros, decimais,
/// entre demais tipos numéricos.
///
pub trait Weight: CheckedAdd + Ord + Bounded + Zero + One + Copy + SaturatingAdd {}

/// Implementação do traço `Weight`.
///
/// Aqui, é definido que qualquer tipo `T` que implemente os traços listados
/// é um bom candidato para ser o peso de uma aresta. Isto inclui todos os tipos
/// numéricos, indo de números sem sinal até de ponto flutuante.
///
/// Vale notar que tais traços vêm, em sua maioria, do crate `num_traits`.
impl<T> Weight for T where T: CheckedAdd + Ord + Bounded + One + Zero + Copy + Sum + SaturatingAdd {}

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
    ///   necessários para visualizar o caminho mais curto entre os vértices.
    fn dijkstra(&self, start: N) -> DijkstraResult<N, W> {
        DijkstraResult::new(self, start)
    }

    /// Executa o algoritmo de Bellman-Ford e fim de encontrar o caminho mais curto para
    /// todos os vértices a partir de uma origem. Também identifica ciclos.
    ///
    /// # Argumentos
    /// - `start`: origem da busca
    ///
    /// # Retorno
    /// - Uma struct `BellmanFordResult` que contém:
    /// - `dist`: armazena a distância de cada vértice para todos os outros;
    /// - `pred`: armazena o predecessor de cada vértice para que possa chegar em cada um;
    /// - `has_negative_cycle`: um booleano correspondente a presença ou não de um ciclo negativo no grafo;
    fn bellman_ford(&self, start: N) -> BellmanFordResult<N, W> {
        BellmanFordResult::new(self, start)
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

    /// Gera uma árvore de caminhos mínimos que parte do vértice `root`.
    ///
    /// # Argumentos
    /// - `root`: vértice origem da busca.
    ///
    /// # Retorno
    /// Uma `ShortestPathTree` contendo as distâncias e predecessores mínimos
    /// para alcançar cada vértice alcançável a partir de `root`.
    fn shortest_path_tree(&self, root: N) -> ShortestPathTree<N, W> {
        ShortestPathTree::new(self, root)
    }
}
