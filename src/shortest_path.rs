use crate::graph::Graph;
use crate::graph::Node;
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub enum DijkstraEvent<T>
where
    T: Node,
{
    Discover((T, i32, Option<T>)),
    Finish,
}

#[derive(Debug)]
pub struct DijkstraIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
{
    graph: &'a G,
    visited: HashSet<T>,
    distance: HashMap<T, i32>,
    parent: HashMap<T, Option<T>>,
}

impl<'a, T, G> DijkstraIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
{
    pub fn new(graph: &'a G, start: T) -> Self {
        let visited: HashSet<T> = HashSet::new();
        let mut distance: HashMap<T, i32> = HashMap::new();
        let mut parent: HashMap<T, Option<T>> = HashMap::new();
        distance.insert(start, 0);
        parent.insert(start, None);

        if let Some(neighbors) = graph.neighbors(start) {
            for neighbor in neighbors {
                parent.insert(neighbor.0, Some(start));
                distance.insert(neighbor.0, neighbor.1);
            }
        }

        Self {
            graph,
            visited,
            distance,
            parent,
        }
    }
}

impl<'a, T, G> Iterator for DijkstraIter<'a, T, G>
where
    T: Node,
    G: Graph<T>,
{
    type Item = DijkstraEvent<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut unvisited_node: Option<(T, i32)> = None;

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

                if let Some(neighbors) = self.graph.neighbors(node) {
                    for (neighbor, edge_weight) in neighbors {
                        if !self.visited.contains(&neighbor) {
                            let new_distance = edge_weight + node_weight;

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
                }

                let mut parent: Option<T> = None;
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
    use crate::{Graph, graphs::AdjacencyList};

    #[test]
    fn dijkstra_graph() {
        let mut map: HashMap<usize, HashSet<(usize, i32)>> = HashMap::new();
        let mut set1: HashSet<(usize, i32)> = HashSet::new();
        set1.insert((1, 0));
        set1.insert((2, 2));
        set1.insert((3, 4));
        set1.insert((4, 5));
        set1.insert((5, 0));
        set1.insert((6, 0));
        set1.insert((7, 0));
        let mut set2: HashSet<(usize, i32)> = HashSet::new();
        set2.insert((1, 2));
        set2.insert((2, 0));
        set2.insert((3, 0));
        set2.insert((4, 2));
        set2.insert((5, 0));
        set2.insert((6, 0));
        set2.insert((7, 0));
        let mut set3: HashSet<(usize, i32)> = HashSet::new();
        set3.insert((1, 4));
        set3.insert((2, 0));
        set3.insert((3, 0));
        set3.insert((4, 1));
        set3.insert((5, 0));
        set3.insert((6, 4));
        set3.insert((7, 0));
        let mut set4: HashSet<(usize, i32)> = HashSet::new();
        set4.insert((1, 5));
        set4.insert((2, 2));
        set4.insert((3, 1));
        set4.insert((4, 0));
        set4.insert((5, 2));
        set4.insert((6, 3));
        set4.insert((7, 0));
        let mut set5: HashSet<(usize, i32)> = HashSet::new();
        set5.insert((1, 0));
        set5.insert((2, 0));
        set5.insert((3, 0));
        set5.insert((4, 2));
        set5.insert((5, 0));
        set5.insert((6, 1));
        set5.insert((7, 5));
        let mut set6: HashSet<(usize, i32)> = HashSet::new();
        set6.insert((1, 0));
        set6.insert((2, 0));
        set6.insert((3, 4));
        set6.insert((4, 3));
        set6.insert((5, 1));
        set6.insert((6, 0));
        set6.insert((7, 7));
        let mut set7: HashSet<(usize, i32)> = HashSet::new();
        set7.insert((1, 0));
        set7.insert((2, 0));
        set7.insert((3, 0));
        set7.insert((4, 0));
        set7.insert((5, 5));
        set7.insert((6, 7));
        set7.insert((7, 0));

        map.insert(1, set1);
        map.insert(2, set2);
        map.insert(3, set3);
        map.insert(4, set4);
        map.insert(5, set5);
        map.insert(6, set6);
        map.insert(7, set7);

        let g: AdjacencyList<usize> = AdjacencyList(map);
        let mut iter: DijkstraIter<usize, AdjacencyList<usize>> = g.shortest_path_dijkstra(1);

        while let Some(event) = iter.next() {
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
        assert_eq!(iter.distance.get(&1), Some(0 as i32).as_ref());
        assert_eq!(iter.distance.get(&2), Some(2 as i32).as_ref());
        assert_eq!(iter.distance.get(&3), Some(4 as i32).as_ref());
        assert_eq!(iter.distance.get(&4), Some(4 as i32).as_ref());
        assert_eq!(iter.distance.get(&5), Some(6 as i32).as_ref());
        assert_eq!(iter.distance.get(&6), Some(7 as i32).as_ref());
        assert_eq!(iter.distance.get(&7), Some(11 as i32).as_ref());
        assert_eq!(iter.parent.get(&1), Some(None).as_ref());
        assert_eq!(iter.parent.get(&2), Some(Some(1 as usize)).as_ref());
        assert_eq!(iter.parent.get(&3), Some(Some(1 as usize)).as_ref());
        assert_eq!(iter.parent.get(&4), Some(Some(2 as usize)).as_ref());
        assert_eq!(iter.parent.get(&5), Some(Some(4 as usize)).as_ref());
        assert_eq!(iter.parent.get(&6), Some(Some(4 as usize)).as_ref());
        assert_eq!(iter.parent.get(&7), Some(Some(5 as usize)).as_ref());
        println!("Fim das iterações")
    }

    #[test]
    fn dijkstra_digraph() {
        let mut map: HashMap<char, HashSet<(char, i32)>> = HashMap::new();
        let mut set1: HashSet<(char, i32)> = HashSet::new();
        set1.insert(('A', 0));
        set1.insert(('B', 5));
        set1.insert(('C', 2));
        set1.insert(('D', 0));
        set1.insert(('E', 0));
        set1.insert(('F', 0));
        let mut set2: HashSet<(char, i32)> = HashSet::new();
        set2.insert(('A', 0));
        set2.insert(('B', 0));
        set2.insert(('C', 1));
        set2.insert(('D', 4));
        set2.insert(('E', 2));
        set2.insert(('F', 0));
        let mut set3: HashSet<(char, i32)> = HashSet::new();
        set3.insert(('A', 0));
        set3.insert(('B', 0));
        set3.insert(('C', 0));
        set3.insert(('D', 0));
        set3.insert(('E', 7));
        set3.insert(('F', 0));
        let mut set4: HashSet<(char, i32)> = HashSet::new();
        set4.insert(('A', 0));
        set4.insert(('B', 0));
        set4.insert(('C', 0));
        set4.insert(('D', 0));
        set4.insert(('E', 5));
        set4.insert(('F', 3));
        let mut set5: HashSet<(char, i32)> = HashSet::new();
        set5.insert(('A', 0));
        set5.insert(('B', 0));
        set5.insert(('C', 0));
        set5.insert(('D', 0));
        set5.insert(('E', 0));
        set5.insert(('F', 1));
        let mut set6: HashSet<(char, i32)> = HashSet::new();
        set6.insert(('A', 0));
        set6.insert(('B', 0));
        set6.insert(('C', 0));
        set6.insert(('D', 0));
        set6.insert(('E', 0));
        set6.insert(('F', 0));

        map.insert('A', set1);
        map.insert('B', set2);
        map.insert('C', set3);
        map.insert('D', set4);
        map.insert('E', set5);
        map.insert('F', set6);

        let g: AdjacencyList<char> = AdjacencyList(map);
        let mut iter: DijkstraIter<char, AdjacencyList<char>> = g.shortest_path_dijkstra('A');
        while let Some(event) = iter.next() {
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
        assert_eq!(iter.distance.get(&'A'), Some(0 as i32).as_ref());
        assert_eq!(iter.distance.get(&'B'), Some(5 as i32).as_ref());
        assert_eq!(iter.distance.get(&'C'), Some(2 as i32).as_ref());
        assert_eq!(iter.distance.get(&'D'), Some(9 as i32).as_ref());
        assert_eq!(iter.distance.get(&'E'), Some(7 as i32).as_ref());
        assert_eq!(iter.distance.get(&'F'), Some(8 as i32).as_ref());
        assert_eq!(iter.parent.get(&'A'), Some(None).as_ref());
        assert_eq!(iter.parent.get(&'B'), Some(Some('A')).as_ref());
        assert_eq!(iter.parent.get(&'C'), Some(Some('A')).as_ref());
        assert_eq!(iter.parent.get(&'D'), Some(Some('B')).as_ref());
        assert_eq!(iter.parent.get(&'E'), Some(Some('B')).as_ref());
        assert_eq!(iter.parent.get(&'F'), Some(Some('E')).as_ref());
        println!("Fim das iterações")
    }
}
