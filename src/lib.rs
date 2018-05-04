#![feature(crate_in_paths)]
#![feature(extern_absolute_paths)]
#![feature(extern_prelude)]
#![feature(in_band_lifetimes)]

use std::fmt::Debug;

mod test;

/// Single entry, multiple exit region.
///
/// The region can be visualized as `{H, {Ts}}`, where `H` is the
/// "head" and Ts is a set of "tail" nodes. In all cases, H dominates
/// all of the tails (to be valid, there is an add'l "continuity"
/// requirement see below). The region contains all points P where:
///
/// - H dominates P
/// - there exists some T in Ts where P dominates T
///
/// In other words, the point P is "in between" the head H and some
/// tail T on the dominator tree. You can test this by walking up the
/// dom tree from each tail T until you reach either H or P -- if you
/// ever find P before H (or if P == H) then P is contained.
///
/// To be complete, a region must also be **continuous**:
///
/// - For each node N in the region where N != H, all predecessors of
///   N are in the region.
#[derive(Clone, Debug)]
pub struct SemeRegion<P: Point> {
    head: P,
    tails: Vec<P>,
}

pub trait Point: Copy + Ord + Debug {
    fn entry() -> Self;
}

pub trait GraphRef<P: Point>: Copy {
    type Predecessors: Iterator<Item = P>;
    fn predecessors(self, point: P) -> Self::Predecessors;

    /// Returns the immediate dominator of `point` -- if `point` is
    /// the entry to the graph, then returns `point`.
    fn immediate_dominator(self, point: P) -> Option<P>;

    /// True if point1 dominates point2.
    fn dominates(self, point1: P, point2: P) -> bool;

    fn mutual_dominator(self, point1: P, point2: P) -> P;
}

impl<P: Point> SemeRegion<P> {
    pub fn empty() -> SemeRegion<P> {
        SemeRegion {
            head: P::entry(),
            tails: vec![],
        }
    }

    pub fn is_empty(&self) -> bool {
        self.tails.is_empty()
    }

    /// True if `point` is contained within the region.
    pub fn contains(&self, graph: impl GraphRef<P>, point: P) -> bool {
        // Not the most efficient impl, but the easiest and most readable.
        graph.dominates(self.head, point) && self.dominates_any_tail(graph, point)
    }

    /// True if `point` dominates any of our tails.
    fn dominates_any_tail(&self, graph: impl GraphRef<P>, point: P) -> bool {
        self.tails.iter().any(|&tail| graph.dominates(point, tail))
    }

    pub fn add_point(&mut self, graph: impl GraphRef<P>, point: P) {
        if self.tails.is_empty() {
            // Region is empty; create singleton region.
            self.head = point;
            self.tails.push(point);
            return;
        }

        if graph.dominates(self.head, point) {
            return self.add_point_dominated_by_head(graph, point);
        }

        // The existing head H does not dominate P. We will have to
        // pick a new head M that dominates both H and P (the "dashed
        // line" indicaets that M and P are not part of region yet):
        //
        // ```
        //         M
        //        : :
        //       :   :
        //      H     P
        //     / \
        //    /   \
        //   T1---Tn
        // ```

        let old_head = self.head;
        let new_head = graph.mutual_dominator(old_head, point);
        self.head = new_head;
        self.ensure_continuity(graph, new_head, old_head);

        // At this point, we have something like this region (note
        // that ensuring continuity will not modidy `self.head`,
        // though it may add tails, which we have elided from this
        // diagram):
        //
        //         M
        //        / :
        //       /   :
        //      H     P
        //     / \
        //    /   \
        //   T1---Tn
        //
        // Key point is that `P` is now dominated by `self.head`
        // (which is M), so we can invoke `add_point_dominated_by_head`

        self.add_point_dominated_by_head(graph, point);
    }

    pub fn add_region(&mut self, graph: impl GraphRef<P>, region: &SemeRegion<P>) {
        if region.is_empty() {
            return;
        }

        self.add_point(graph, region.head);
        for &tail in &region.tails {
            self.add_point(graph, tail)
        }
    }

    /// Add `point` to the region in the case where we know that
    /// `point` is dominated by `self.head`. (See comment in the
    /// function for detailed breakdown).
    fn add_point_dominated_by_head(&mut self, graph: impl GraphRef<P>, point: P) {
        debug_assert!(graph.dominates(self.head, point));

        // We now want to distinguish one of a few cases:
        //
        // **Noop case:** point dominates a tail. In that case, it is
        // already contained in the region.
        //
        // ```
        //      H
        //     / \
        //    / P \
        //   T1---Tn
        // ```
        //
        // **Extension case:** a tail dominates point. In that case, we can
        // replace the tail with point (and then "fixup", see below).
        //
        // ```
        //      H
        //     / \
        //    /   \
        //   T1---Tn
        //         |
        //         P
        // ```
        //
        // **New case:** T is not related to a known tail. Just have
        // to add a new tail.
        //
        // ```
        //      H------+
        //     / \     |
        //    /   \    P
        //   T1---Tn
        // ```
        //
        // In the last two cases, after we adjust the tail, we
        // have to run "fixup". This will walk the new nodes that
        // have been added and guarantee the continuity invariant.
        //
        // To determine which case we are in, we walk up the dom
        // tree from P. If we encounter a tail, then we are in the
        // extension case. If we encounter head, then we are in
        // either in the "noop" or "new" case.

        let mut p = point;
        loop {
            if let Some(index) = self.tails.iter().position(|&t| t == p) {
                // Found one of the tails. This is the extension case
                // -- unless `p == point`, in which case the point is
                // already contained in the set.
                if p == point {
                    return;
                }

                self.tails[index] = point;
                return self.ensure_continuity(graph, p, point);
            }

            if p == self.head {
                return self.add_point_dominated_by_head_and_not_by_tail(graph, point);
            }

            p = graph.immediate_dominator(p).unwrap();
        }
    }

    /// We found that P is dominated by the head but it is *not*
    /// dominated by any of the tails. This means that either P is
    /// within the region (if it dominates a tail) or else it is a new
    /// "branch".
    fn add_point_dominated_by_head_and_not_by_tail(&mut self, graph: impl GraphRef<P>, point: P) {
        if self.dominates_any_tail(graph, point) {
            // already contained, the "noop" case above.
            return;
        }

        // "extension" case.
        self.tails.push(point);
        let head = self.head;
        self.ensure_continuity(graph, head, point);
    }

    /// Ensures that, for any node P that lies between `parent`
    /// (exclusive) and `child` (inclusive) on the dominator tree, all
    /// predecessors of P are contained in `self`.
    ///
    /// Presuming that `parent` and `child` are both dominated by
    /// `self.head`, then this routine does not modify `self.head`. To
    /// see why, consider some node `P` that lies between `parent`
    /// (exclusive) and `child`.  Clearly `P` is strictly dominated by
    /// `parent` and hence by `self.head`. This implies that each
    /// predecessor `Q` of `P` must be either be equal to `self.head`
    /// (in which case it is included in the region) or dominated by
    /// `self.head` (otherwise, there would be a path to `P` through
    /// `Q` that bypasses `self.head`). So adding Q to the region will
    /// not modify `self.head`.
    fn ensure_continuity(&mut self, graph: impl GraphRef<P>, parent: P, child: P) {
        let mut point = child;
        while point != parent {
            for predecessor in graph.predecessors(point) {
                self.add_point(graph, predecessor);
            }

            point = graph.immediate_dominator(point).unwrap();
        }
    }
}
