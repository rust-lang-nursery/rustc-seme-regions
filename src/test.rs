#![cfg(test)]

use crate::{GraphRef, Point, SemeRegion};
use petgraph::algo::dominators::{self, Dominators};
use petgraph::graph::{Graph, Neighbors, NodeIndex};
use petgraph::Direction;

struct GraphPair {
    graph: Graph<(), ()>,
    dominators: Dominators<NodeIndex>,
}

impl GraphPair {
    fn new(edges: &[(usize, usize)]) -> GraphPair {
        let num_nodes = edges
            .iter()
            .map(|(a, b)| ::std::cmp::max(a + 1, b + 1))
            .max()
            .unwrap_or(0);

        let mut graph = Graph::new();

        for _ in 0..num_nodes {
            graph.add_node(());
        }

        for &(p, q) in edges {
            graph.add_edge(NodeIndex::new(p), NodeIndex::new(q), ());
        }

        let dominators = dominators::simple_fast(&graph, NodeIndex::entry());

        GraphPair { graph, dominators }
    }
}

impl Point for NodeIndex {
    fn entry() -> Self {
        NodeIndex::new(0)
    }
}

impl GraphRef<NodeIndex> for &'g GraphPair {
    type Predecessors = Neighbors<'g, ()>;

    fn predecessors(self, point: NodeIndex) -> Self::Predecessors {
        self.graph.neighbors_directed(point, Direction::Incoming)
    }

    fn immediate_dominator(self, point: NodeIndex) -> Option<NodeIndex> {
        self.dominators.immediate_dominator(point)
    }

    fn dominates(self, point1: NodeIndex, point2: NodeIndex) -> bool {
        self.dominators
            .dominators(point2)
            .unwrap()
            .any(|p| p == point1)
    }

    fn mutual_dominator(self, point1: NodeIndex, point2: NodeIndex) -> NodeIndex {
        for p in self.dominators.dominators(point2).unwrap() {
            // invariant: p dominates point2
            if self.dominates(p, point1) {
                return p;
            }
        }
        panic!("no mutual dominator of {:?} and {:?}", point1, point2)
    }
}

macro_rules! assert_contents {
    ($region:expr, $graph:expr, +[$($c:expr),*] - [$($n:expr),*]) => {
        $(
            assert!(
                $region.contains($graph, NodeIndex::new($c)),
                "region should contain {:?} but does not",
                $c,
            );
        )*

        $(
            assert!(
                !$region.contains($graph, NodeIndex::new($n)),
                "region should not contain {:?} but does",
                $n,
            );
        )*
    }
}

#[test]
fn diamond1() {
    // Flow -->
    //
    //     1
    //   /   \
    // 0      3
    //   \   /
    //     2

    let g = &GraphPair::new(&[(0, 1), (0, 2), (1, 3), (2, 3)]);
    let mut r = SemeRegion::empty();

    r.add_point(g, NodeIndex::new(3));
    assert_contents!(r, g, +[3] -[0, 1, 2]);

    // Adding 1 forces us to contain 0, because that is mutual
    // dominator of 1 and 3. Once we have 0, we must have 2.
    r.add_point(g, NodeIndex::new(1));
    assert_contents!(r, g, +[0, 1, 2, 3] -[]);
}

#[test]
fn diamond2() {
    // Flow -->
    //
    //     1
    //   /   \
    // 0      3
    //   \   /
    //     2

    let g = &GraphPair::new(&[(0, 1), (0, 2), (1, 3), (2, 3)]);

    // We can contain 0 and 1
    let mut r = SemeRegion::empty();
    r.add_point(g, NodeIndex::new(0));
    r.add_point(g, NodeIndex::new(2));
    assert_contents!(r, g, +[0, 2] -[1, 3]);

    // We can contain 0 and 2
    let mut r = SemeRegion::empty();
    r.add_point(g, NodeIndex::new(0));
    r.add_point(g, NodeIndex::new(1));
    assert_contents!(r, g, +[0, 1] -[2, 3]);

    // But 0 and 3 forces 1 and 2
    let mut r = SemeRegion::empty();
    r.add_point(g, NodeIndex::new(0));
    r.add_point(g, NodeIndex::new(3));
    assert_contents!(r, g, +[0, 1, 2, 3] -[]);
}
