use crate::graph::Node;
use crate::graph::Weight;
use crate::graph::WeightedGraph;
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub enum DijkstraEvent<N, W>
where
    N: Node,
    W: Weight,
{
    Discover((N, W, Option<N>)),
    Finish,
}

#[derive(Debug)]
pub struct DijkstraIter<'a, N, W, G>
where
    N: Node,
    W: Weight,
    G: WeightedGraph<N, W>,
{
    graph: &'a G,
    visited: HashSet<N>,
    distance: HashMap<N, W>,
    parent: HashMap<N, Option<N>>,
}

impl<'a, N, W, G> DijkstraIter<'a, N, W, G>
where
    N: Node,
    W: Weight,
    G: WeightedGraph<N, W>,
{
    pub fn new(graph: &'a G, start: N) -> Self {
        let visited: HashSet<N> = HashSet::new();
        let mut distance: HashMap<N, W> = HashMap::new();
        let mut parent: HashMap<N, Option<N>> = HashMap::new();
        distance.insert(start, W::zero());
        parent.insert(start, None);

        for (neighbor, weight) in graph.weighted_neighbors(start) {
            parent.insert(neighbor, Some(start));
            distance.insert(neighbor, weight);
        }

        Self {
            graph,
            visited,
            distance,
            parent,
        }
    }
}

impl<'a, N, W, G> Iterator for DijkstraIter<'a, N, W, G>
where
    N: Node,
    W: Weight,
    G: WeightedGraph<N, W>,
{
    type Item = DijkstraEvent<N, W>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut unvisited_node: Option<(N, W)> = None;

        for node in self.graph.nodes() {
            if !self.visited.contains(&node)
                && let Some(distance) = self.distance.get(&node)
                && (unvisited_node.is_none()
                    || (unvisited_node.is_some() && distance < &unvisited_node.unwrap().1))
            {
                unvisited_node = Some((node, *distance));
            }
        }

        match unvisited_node {
            None => None,
            Some((node, node_weight)) => {
                self.visited.insert(node);

                for (neighbor, weight) in self.graph.weighted_neighbors(node) {
                    if !self.visited.contains(&neighbor) {
                        let new_distance = weight + node_weight;

                        match self.distance.get(&neighbor) {
                            Some(&neighbor_distance) => {
                                if neighbor_distance > new_distance {
                                    self.distance.insert(neighbor, new_distance);
                                    self.parent.insert(neighbor, Some(node));
                                }
                            }
                            None => {
                                self.distance.insert(neighbor, new_distance);
                                self.parent.insert(neighbor, Some(node));
                            }
                        }
                    }
                }

                let mut parent: Option<N> = None;
                if let Some(opt) = self.parent.get(&node) {
                    parent = *opt;
                }

                Some(DijkstraEvent::Discover((node, node_weight, parent)))
            }
        }
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
        let mut iter = g.djikstra(1);

        for event in &mut iter {
            match event {
                DijkstraEvent::Discover((node, weight, parent)) => println!(
                    "Visitamos o vértice {} e agora tem distância {} a partir do predecessor {}",
                    node,
                    weight,
                    parent.unwrap_or(0)
                ),
                DijkstraEvent::Finish => {}
            }
        }
        assert_eq!(iter.visited.len(), 7);
        assert_eq!(iter.distance.len(), 7);
        assert_eq!(iter.parent.len(), 7);
        assert_eq!(iter.distance.get(&1), Some(0).as_ref());
        assert_eq!(iter.distance.get(&2), Some(2).as_ref());
        assert_eq!(iter.distance.get(&3), Some(4).as_ref());
        assert_eq!(iter.distance.get(&4), Some(4).as_ref());
        assert_eq!(iter.distance.get(&5), Some(6).as_ref());
        assert_eq!(iter.distance.get(&6), Some(7).as_ref());
        assert_eq!(iter.distance.get(&7), Some(11).as_ref());
        assert_eq!(iter.parent.get(&1), Some(None).as_ref());
        assert_eq!(iter.parent.get(&2), Some(Some(1)).as_ref());
        assert_eq!(iter.parent.get(&3), Some(Some(1)).as_ref());
        assert_eq!(iter.parent.get(&4), Some(Some(2)).as_ref());
        assert_eq!(iter.parent.get(&5), Some(Some(4)).as_ref());
        assert_eq!(iter.parent.get(&6), Some(Some(4)).as_ref());
        assert_eq!(iter.parent.get(&7), Some(Some(5)).as_ref());
        println!("Fim das iterações")
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
        let mut iter = g.djikstra('A');
        for event in &mut iter {
            if let DijkstraEvent::Discover((node, weight, parent)) = event {
                println!(
                    "Visitamos o vértice {} e agora tem distância {} a partir do predecessor {}",
                    node,
                    weight,
                    parent.unwrap_or('-')
                )
            }
        }

        assert_eq!(iter.visited.len(), 6);
        assert_eq!(iter.distance.len(), 6);
        assert_eq!(iter.parent.len(), 6);
        assert_eq!(iter.distance.get(&'A'), Some(0).as_ref());
        assert_eq!(iter.distance.get(&'B'), Some(5).as_ref());
        assert_eq!(iter.distance.get(&'C'), Some(2).as_ref());
        assert_eq!(iter.distance.get(&'D'), Some(9).as_ref());
        assert_eq!(iter.distance.get(&'E'), Some(7).as_ref());
        assert_eq!(iter.distance.get(&'F'), Some(8).as_ref());
        assert_eq!(iter.parent.get(&'A'), Some(None).as_ref());
        assert_eq!(iter.parent.get(&'B'), Some(Some('A')).as_ref());
        assert_eq!(iter.parent.get(&'C'), Some(Some('A')).as_ref());
        assert_eq!(iter.parent.get(&'D'), Some(Some('B')).as_ref());
        assert_eq!(iter.parent.get(&'E'), Some(Some('B')).as_ref());
        assert_eq!(iter.parent.get(&'F'), Some(Some('E')).as_ref());
        println!("Fim das iterações")
    }
}
