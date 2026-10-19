import Thesis.CausalTransport.CompletenessCertificates

namespace Thesis
namespace Causality

open Probability

/-!
# Failure records and finite hedge extraction

Retains the original finite failure records, graph tests and failure-to-hedge
transport lemmas. No new engine failure case is added by this extraction.

Every extracted declaration keeps its original namespace, statement, proof
script and order. The new boundary only lets later work import a completed
artifact instead of retaining this section's elaboration state. Existing
clients may still import Completeness for the entire historical interface.
No theorem is dropped, weakened or replaced by an assumption.

Historical branch-specific unpackers remain historical facts: their quantity
is not evidence that a published semantic completeness theorem has been
inhabited. Current-engine compilation and hedge semantics retain their
existing independently checked assembly boundaries.
-/

/-! ## Failure records and finite hedge extraction -/

theorem failedHedgeSelection_small_single
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    G.isSingleCComponent (failedHedgeSelection fail).small = true := by
  rcases (identifyJoint_eq_failed_free G q hfail).2 with ⟨root, hroot, hEq⟩
  exact isSingleCComponent_of_self G fail.free hroot hEq

theorem failedHedgeSelection_small_nonempty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.isEmpty (failedHedgeSelection fail).small = false :=
  isSingleCComponent_nonempty G _
    (failedHedgeSelection_small_single G q hfail)

theorem failedHedgeSelection_small_subset
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.subsetBool (failedHedgeSelection fail).small
      (failedHedgeSelection fail).large = true :=
  (NodeSet.subsetBool_eq_true_iff _ _).mpr
    (identifyJoint_eq_failed_free G q hfail).1

theorem failedHedgeSelection_child_wellFormed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    childWellFormedBool (failedHedgeSelection fail).large
      (failedHedgeSelection fail).child = true :=
  closedForestChild_wellFormed fail.remaining fail.free
    (identifyJoint_eq_failed_free G q hfail).1

theorem failedHedgeSelection_childClosed
    (fail : IdentificationFail S) :
    childClosedBool (failedHedgeSelection fail).small
      (failedHedgeSelection fail).child = true :=
  closedForestChild_childClosed fail.remaining fail.free

theorem failedHedgeSelection_large_single
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    G.isSingleCComponent (failedHedgeSelection fail).large = true :=
  identifyJoint_eq_failed G q hfail

theorem failedHedgeSelection_large_nonempty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.isEmpty (failedHedgeSelection fail).large = false :=
  isSingleCComponent_nonempty G _
    (failedHedgeSelection_large_single G q hfail)

/--
Vertex tests of the failure-record selection, once the remaining set
still meets the original action.
-/
theorem failedHedgeSelection_largeVerticesReady
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action =
        true) :
    largeVerticesReady G q (failedHedgeSelection fail).large = true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_, hmeets⟩
  refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
  · have hempty := failedHedgeSelection_large_nonempty G q hfail
    cases h : NodeSet.isEmpty (failedHedgeSelection fail).large
    · rfl
    · exact False.elim (Bool.false_ne_true (hempty.symm.trans h))
  · exact failedHedgeSelection_large_single G q hfail

/--
Small-side tests of the failure-record selection that do not mention the
original action or kept-sink inclusion.  Child-closure is by construction
of `closedForestChild`.
-/
theorem failedHedgeSelection_smallForestCore
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    ((!NodeSet.isEmpty (failedHedgeSelection fail).small) &&
      G.isSingleCComponent (failedHedgeSelection fail).small &&
      NodeSet.subsetBool (failedHedgeSelection fail).small
        (failedHedgeSelection fail).large &&
      childClosedBool (failedHedgeSelection fail).small
        (failedHedgeSelection fail).child) = true := by
  have hempty := failedHedgeSelection_small_nonempty G q hfail
  have hneg : (!NodeSet.isEmpty (failedHedgeSelection fail).small) = true := by
    cases h : NodeSet.isEmpty (failedHedgeSelection fail).small
    · rfl
    · exact False.elim (Bool.false_ne_true (hempty.symm.trans h))
  refine Bool.and_eq_true_iff.mpr ⟨?_, failedHedgeSelection_childClosed fail⟩
  refine Bool.and_eq_true_iff.mpr ⟨?_,
    failedHedgeSelection_small_subset G q hfail⟩
  exact Bool.and_eq_true_iff.mpr ⟨hneg,
    failedHedgeSelection_small_single G q hfail⟩

/--
A vertex that is ancestral of `targets` but not itself a target has a
directed successor that is still ancestral.  That first step is the
outgoing edge required of every cut vertex in a C-forest.
-/
theorem ancestorOfWithin_first_successor
    (G : ObservedGraph S) (nodes : NodeSet S)
    (m : GraphMutilation S) (targets : NodeSet S)
    {parent : Fin S.count}
    (hanc : G.ancestorOfWithin nodes m targets parent = true)
    (hnotY : targets parent = false) :
    Exists fun child =>
      nodes child = true ∧
        G.observedDirectedEdge m parent child = true ∧
          G.ancestorOfWithin nodes m targets child = true := by
  have _hnode : nodes parent = true :=
    (Bool.and_eq_true_iff.mp hanc).1
  have hany :
      (NodeSet.members (NodeSet.inter targets nodes)).any (fun target =>
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (G.directedEdgeWithin nodes m) S.count parent target) = true :=
    (Bool.and_eq_true_iff.mp hanc).2
  rcases List.any_eq_true.mp hany with ⟨y, yMem, hy⟩
  have hyInter : NodeSet.inter targets nodes y = true :=
    (NodeSet.mem_members_iff _ y).mp yMem
  have hyT : targets y = true :=
    NodeSet.inter_subset_left targets nodes y hyInter
  have complete : forall node, node ∈ NodeSet.enumerated S :=
    NodeSet.mem_enumerated S
  have bounded :
      FiniteReachability.BoundedWalk (G.directedEdgeWithin nodes m)
        S.count parent y :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (NodeSet.enumerated S) (G.directedEdgeWithin nodes m)
      finBeq_eq_true_iff complete S.count parent y).mp hy
  rcases bounded with ⟨length, hle, ⟨walk⟩⟩
  cases length with
  | zero =>
      cases walk
      exact False.elim (Bool.false_ne_true (hnotY.symm.trans hyT))
  | succ n =>
      cases walk with
      | @step _ _ middle _ first rest =>
          have hedgeParts := Bool.and_eq_true_iff.mp first
          have hboth := Bool.and_eq_true_iff.mp hedgeParts.1
          have hmid : nodes middle = true := hboth.2
          have hedge : G.observedDirectedEdge m parent middle = true :=
            hedgeParts.2
          have boundedMid :
              FiniteReachability.BoundedWalk
                (G.directedEdgeWithin nodes m) S.count middle y :=
            FiniteReachability.BoundedWalk.mono
              (Nat.le_trans (Nat.le_succ n) hle)
              ⟨n, Nat.le_refl n, ⟨rest⟩⟩
          have hyMid :
              FiniteReachability.within finBeq (NodeSet.enumerated S)
                (G.directedEdgeWithin nodes m) S.count middle y = true :=
            (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
              (NodeSet.enumerated S) (G.directedEdgeWithin nodes m)
              finBeq_eq_true_iff complete S.count middle y).mpr boundedMid
          have hancMid : G.ancestorOfWithin nodes m targets middle = true :=
            Bool.and_eq_true_iff.mpr
              ⟨hmid, List.any_eq_true.mpr ⟨y, yMem, hyMid⟩⟩
          exact ⟨middle, hmid, hedge, hancMid⟩

/--
Kept sinks of the failure-record forest lie in the free side once the
remaining set is ancestral of the outcome in `G_{\overline{cut}}` and
the cut avoids the outcome.  Every cut vertex then has a directed
successor in the remaining set.
-/
theorem failedHedgeSelection_keptSinks_of_ancestral
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true)
    (hnotY :
      NodeSet.Disjoint (NodeSet.diff fail.remaining fail.free)
        (NodeSet.inter q.outcome fail.remaining)) :
    NodeSet.subsetBool
      (keptSinks (failedHedgeSelection fail).large
        (failedHedgeSelection fail).child)
      (failedHedgeSelection fail).small = true :=
  (NodeSet.subsetBool_eq_true_iff _ _).mpr
    (closedForestChild_keptSinks_subset fail.remaining fail.free
      (fun parent hL hS => by
        have hcut :
            NodeSet.diff fail.remaining fail.free parent = true :=
          Bool.and_eq_true_iff.mpr ⟨hL, by simp [hS]⟩
        have hancP :
            G.ancestorOfWithin fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter q.outcome fail.remaining) parent = true :=
          ancestorOfWithin_of_ancestralSet G fail.remaining _ _ hanc hL
        have hnot : NodeSet.inter q.outcome fail.remaining parent = false :=
          hnotY parent hcut
        rcases ancestorOfWithin_first_successor G fail.remaining
            (GraphMutilation.bar
              (NodeSet.diff fail.remaining fail.free))
            (NodeSet.inter q.outcome fail.remaining) hancP hnot with
          ⟨child, hchild, hedge, _⟩
        have hdir : S.directed parent child = true :=
          ((observedDirectedEdge_bar G
              (NodeSet.diff fail.remaining fail.free)).mp hedge).1
        exact ⟨child,
          (mem_directedChildren_iff fail.remaining parent child).mpr
            ⟨hchild, hdir⟩⟩))

/--
Kept sinks lie in the free component once the remaining set is ancestral
of that component in `G_{\overline{cut}}`.  The cut is disjoint from
`free` by construction, so this does not need `cut ⊆ X`.
-/
theorem failedHedgeSelection_keptSinks_of_free_ancestral
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true) :
    NodeSet.subsetBool
      (keptSinks (failedHedgeSelection fail).large
        (failedHedgeSelection fail).child)
      (failedHedgeSelection fail).small = true :=
  (NodeSet.subsetBool_eq_true_iff _ _).mpr
    (closedForestChild_keptSinks_subset fail.remaining fail.free
      (fun parent hL hS => by
        have hcut :
            NodeSet.diff fail.remaining fail.free parent = true :=
          Bool.and_eq_true_iff.mpr ⟨hL, by simp [hS]⟩
        have hancP :
            G.ancestorOfWithin fail.remaining
              (GraphMutilation.bar
                (NodeSet.diff fail.remaining fail.free))
              (NodeSet.inter fail.free fail.remaining) parent = true :=
          ancestorOfWithin_of_ancestralSet G fail.remaining _ _ hanc hL
        have hnotP :
            NodeSet.inter fail.free fail.remaining parent = false := by
          have hfreeF : fail.free parent = false :=
            NodeSet.Disjoint.diff_right fail.remaining fail.free parent hcut
          simp [NodeSet.inter, hfreeF]
        rcases ancestorOfWithin_first_successor G fail.remaining
            (GraphMutilation.bar
              (NodeSet.diff fail.remaining fail.free))
            (NodeSet.inter fail.free fail.remaining) hancP hnotP with
          ⟨child, hchild, hedge, _⟩
        have hdir : S.directed parent child = true :=
          ((observedDirectedEdge_bar G
              (NodeSet.diff fail.remaining fail.free)).mp hedge).1
        exact ⟨child,
          (mem_directedChildren_iff fail.remaining parent child).mpr
            ⟨hchild, hdir⟩⟩))

/--
The remaining small-side Boolean tests, once the original action avoids
the free component and the kept sinks lie in that component.
-/
theorem failedHedgeSelection_smallForestReady_of
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true)
    (hkept :
      NodeSet.subsetBool
        (keptSinks (failedHedgeSelection fail).large
          (failedHedgeSelection fail).child)
        (failedHedgeSelection fail).small = true) :
    smallForestReady G q (failedHedgeSelection fail).large
      (failedHedgeSelection fail).child
      (failedHedgeSelection fail).small = true := by
  have core := failedHedgeSelection_smallForestCore G q hfail
  have hABCD := Bool.and_eq_true_iff.mp core
  have hABC := Bool.and_eq_true_iff.mp hABCD.1
  have hAB := Bool.and_eq_true_iff.mp hABC.1
  simp [smallForestReady, hAB.1, hAB.2, hABC.2, hdisj, hABCD.2, hkept]

/-- A remaining-set edge of `G_{\overline{X}}` is an unmutilated directed edge. -/
theorem directedEdgeWithin_bar_implies_mutilatedDirected
    (G : ObservedGraph S) (nodes action : NodeSet S)
    {parent child : Fin S.count}
    (h :
      G.directedEdgeWithin nodes (GraphMutilation.bar action)
        parent child = true) :
    mutilatedDirected S action parent child = true := by
  have parts := Bool.and_eq_true_iff.mp h
  have hedge := (observedDirectedEdge_bar G action).mp parts.2
  simp [mutilatedDirected, hedge.2]
  exact hedge.1

/--
Ancestry inside a remaining set, after incoming arrows to the action are
cut, yields a directed walk to some remaining outcome vertex in
`G_{\overline{X}}`.
-/
theorem ancestorOfWithin_reaches_outcome
    (G : ObservedGraph S) (nodes action outcome : NodeSet S)
    {source : Fin S.count}
    (hanc :
      G.ancestorOfWithin nodes (GraphMutilation.bar action) outcome
        source = true) :
    Exists fun y =>
      outcome y = true ∧
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (mutilatedDirected S action) S.count source y = true := by
  have hany :
      (NodeSet.members (NodeSet.inter outcome nodes)).any (fun target =>
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (G.directedEdgeWithin nodes (GraphMutilation.bar action))
          S.count source target) = true :=
    (Bool.and_eq_true_iff.mp hanc).2
  rcases List.any_eq_true.mp hany with ⟨y, yMem, hy⟩
  have hyInter : NodeSet.inter outcome nodes y = true :=
    (NodeSet.mem_members_iff _ y).mp yMem
  have hyOut : outcome y = true :=
    NodeSet.inter_subset_left outcome nodes y hyInter
  have complete : forall node, node ∈ NodeSet.enumerated S :=
    NodeSet.mem_enumerated S
  have bounded :
      FiniteReachability.BoundedWalk
        (G.directedEdgeWithin nodes (GraphMutilation.bar action))
        S.count source y :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (NodeSet.enumerated S)
      (G.directedEdgeWithin nodes (GraphMutilation.bar action))
      finBeq_eq_true_iff complete S.count source y).mp hy
  rcases bounded with ⟨length, hle, ⟨walk⟩⟩
  have walk' :
      FiniteReachability.ExactWalk (mutilatedDirected S action)
        length source y :=
    FiniteReachability.exactWalk_mono
      (fun i j hij =>
        directedEdgeWithin_bar_implies_mutilatedDirected G nodes action hij)
      walk
  have hyMutil :
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (mutilatedDirected S action) S.count source y = true :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (NodeSet.enumerated S) (mutilatedDirected S action)
      finBeq_eq_true_iff complete S.count source y).mpr
      ⟨length, hle, ⟨walk'⟩⟩
  exact ⟨y, hyOut, hyMutil⟩

/--
If the remaining set is ancestral of the query outcome in `G_{\overline{X}}`,
every selected root reaches some outcome vertex along mutilated directed
edges.
-/
theorem rootsReachOutcomeBool_of_ancestralSet
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (nodes roots : NodeSet S)
    (hanc :
      NodeSet.equal
        (G.ancestralSet nodes (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome nodes))
        nodes = true)
    (hsub : NodeSet.Subset roots nodes) :
    rootsReachOutcomeBool q roots = true := by
  refine List.all_eq_true.mpr ?_
  intro root hmem
  have hroot : roots root = true :=
    (NodeSet.mem_members_iff roots root).mp hmem
  have hancR :
      G.ancestorOfWithin nodes (GraphMutilation.bar q.action)
        (NodeSet.inter q.outcome nodes) root = true :=
    ancestorOfWithin_of_ancestralSet G nodes _ _ hanc (hsub root hroot)
  rcases ancestorOfWithin_reaches_outcome G nodes q.action
      (NodeSet.inter q.outcome nodes) hancR with ⟨y, hyInter, hyWalk⟩
  have hyOut : q.outcome y = true :=
    NodeSet.inter_subset_left q.outcome nodes y hyInter
  refine List.any_eq_true.mpr ?_
  exact ⟨y, (NodeSet.mem_members_iff q.outcome y).mpr hyOut, hyWalk⟩

/--
Pointwise ancestry is enough for the selected-root reachability test.

This is the form used by structural failure traces.  A shrink frame can show
that each eventual failure vertex belongs to the outer ancestral set even
when the whole outer remaining set is not ancestral, so requiring a global
set equality would lose exactly the information preserved by that frame.
-/
theorem rootsReachOutcomeBool_of_each_ancestor
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (nodes roots : NodeSet S)
    (hanc :
      forall {root : Fin S.count}, roots root = true ->
        G.ancestorOfWithin nodes (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome nodes) root = true) :
    rootsReachOutcomeBool q roots = true := by
  refine List.all_eq_true.mpr ?_
  intro root hmem
  have hroot : roots root = true :=
    (NodeSet.mem_members_iff roots root).mp hmem
  have hancR :
      G.ancestorOfWithin nodes (GraphMutilation.bar q.action)
        (NodeSet.inter q.outcome nodes) root = true :=
    hanc hroot
  rcases ancestorOfWithin_reaches_outcome G nodes q.action
      (NodeSet.inter q.outcome nodes) hancR with ⟨y, hyInter, hyWalk⟩
  have hyOut : q.outcome y = true :=
    NodeSet.inter_subset_left q.outcome nodes y hyInter
  refine List.any_eq_true.mpr ?_
  exact ⟨y, (NodeSet.mem_members_iff q.outcome y).mpr hyOut, hyWalk⟩

theorem failedHedgeSelection_rootsReach_of_ancestral
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    rootsReachOutcomeBool q
      (keptSinks (failedHedgeSelection fail).large
        (failedHedgeSelection fail).child) = true :=
  rootsReachOutcomeBool_of_ancestralSet G q fail.remaining
    (keptSinks fail.remaining (closedForestChild fail.remaining fail.free))
    hanc
    (keptSinks_subset _ _)

/--
Boolean hedge tests of the failure-record selection, once the remaining
set meets the original action, kept roots reach the outcome, and the
small-side forest tests pass.
-/
theorem failedHedgeSelection_tests_of
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hreach :
      rootsReachOutcomeBool q
        (keptSinks (failedHedgeSelection fail).large
          (failedHedgeSelection fail).child) = true)
    (hsmall :
      smallForestReady G q (failedHedgeSelection fail).large
        (failedHedgeSelection fail).child
        (failedHedgeSelection fail).small = true) :
    hedgeTestsHold G q (failedHedgeSelection fail) = true := by
  have hverts :=
    failedHedgeSelection_largeVerticesReady G q hfail hmeets
  have hwell := failedHedgeSelection_child_wellFormed G q hfail
  have hchild : largeChildReady G q (failedHedgeSelection fail).large
      (failedHedgeSelection fail).child = true := by
    simp [largeChildReady, hwell, hreach]
  simp [hedgeTestsHold, hverts, hchild, hsmall]

/--
When the recorded free side is `remaining \ (remaining ∩ X)`, the cut
is exactly the original action inside the remaining set.
-/
theorem failedHedgeSelection_cut_eq_of_free
    (fail : IdentificationFail S) (action : NodeSet S)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter action fail.remaining)) = true) :
    NodeSet.diff fail.remaining fail.free =
      NodeSet.inter action fail.remaining := by
  have eq := (NodeSet.equal_eq_true_iff _ _).mp hfree
  rw [eq, NodeSet.diff_diff]
  exact NodeSet.inter_eq_of_subset
    (NodeSet.inter_subset_right action fail.remaining)

/--
A cut inside the original action is disjoint from the original
outcome, hence from remaining outcome vertices.
-/
theorem failedHedgeSelection_notY_of_cut
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hsub :
      NodeSet.Subset (NodeSet.diff fail.remaining fail.free) q.action) :
    NodeSet.Disjoint (NodeSet.diff fail.remaining fail.free)
      (NodeSet.inter q.outcome fail.remaining) :=
  fun i hi => by
    have hact : q.action i = true := hsub i hi
    have hout : q.outcome i = false := q.action_outcome_disjoint i hact
    simp [NodeSet.inter, hout]

/--
Boolean hedge tests of the failure-record selection, when the cut is the
original action inside the remaining set and that remaining set is
ancestral of the original outcome in `G_{\overline{cut}}`.
-/
theorem failedHedgeSelection_tests_of_local_action
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    hedgeTestsHold G q (failedHedgeSelection fail) = true := by
  have hcut := failedHedgeSelection_cut_eq_of_free fail q.action hfree
  have hsub : NodeSet.Subset (NodeSet.diff fail.remaining fail.free)
      q.action := by
    intro i hi
    have hi' : NodeSet.inter q.action fail.remaining i = true := by
      simpa [hcut] using hi
    exact NodeSet.inter_subset_left q.action fail.remaining i hi'
  have hcutIncl :
      NodeSet.Subset (NodeSet.inter q.action fail.remaining)
        (NodeSet.diff fail.remaining fail.free) := by
    intro i hi
    simpa [hcut] using hi
  have hmeets := failedHedgeSelection_meets_action_of_cut G q hfail hsub
  have hdisj := failedHedgeSelection_avoids_action_of_cut G q hfail hcutIncl
  have hnotY := failedHedgeSelection_notY_of_cut G q hfail hsub
  have hkept :=
    failedHedgeSelection_keptSinks_of_ancestral G q hfail hanc hnotY
  have hsmall :=
    failedHedgeSelection_smallForestReady_of G q hfail hdisj hkept
  have hancBar :
      G.ancestralSet fail.remaining
        (GraphMutilation.bar (NodeSet.inter q.action fail.remaining))
        (NodeSet.inter q.outcome fail.remaining) =
        fail.remaining := by
    have heq := (NodeSet.equal_eq_true_iff _ _).mp hanc
    simpa [hcut] using heq
  have hancAction :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true := by
    have heq :
        G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining) = fail.remaining := by
      rw [← ancestralSet_bar_inter]
      exact hancBar
    exact (NodeSet.equal_eq_true_iff _ _).mpr heq
  have hreach :=
    failedHedgeSelection_rootsReach_of_ancestral G q hfail hancAction
  exact failedHedgeSelection_tests_of G q hfail hmeets hreach hsmall

/-- An exact walk on Boolean edges is an inductive directed reachability. -/
theorem directedReachableBy_of_exactWalk
    {edge : Fin S.count -> Fin S.count -> Bool}
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (fun i j => edge i j) length source target) :
    DirectedReachableBy S (fun i j => edge i j = true) source target :=
  match walk with
  | .refl node => .refl node
  | .step first rest =>
      DirectedReachableBy.step_left first
        (directedReachableBy_of_exactWalk rest)

theorem directedReachableBy_of_within
    (action : NodeSet S) {source target : Fin S.count}
    (h : FiniteReachability.within finBeq (NodeSet.enumerated S)
          (mutilatedDirected S action) S.count source target = true) :
    DirectedReachableBy S
      (fun i j => mutilatedDirected S action i j = true) source target := by
  have complete : forall node, node ∈ NodeSet.enumerated S :=
    NodeSet.mem_enumerated S
  have bounded :
      FiniteReachability.BoundedWalk (mutilatedDirected S action)
        S.count source target :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (NodeSet.enumerated S) (mutilatedDirected S action)
      finBeq_eq_true_iff complete S.count source target).mp h
  rcases bounded with ⟨_length, _le, ⟨walk⟩⟩
  exact directedReachableBy_of_exactWalk walk

theorem rootsReachOutcome_of_bool
    (q : JointKernelQuery S) (roots : NodeSet S)
    (h : rootsReachOutcomeBool q roots = true) :
    forall root,
      roots root = true ->
        Exists fun outcome =>
          q.outcome outcome = true /\
            DirectedReachableBy S
              (fun i j => mutilatedDirected S q.action i j = true)
              root outcome := by
  intro root hroot
  have rootMem : root ∈ NodeSet.members roots :=
    (NodeSet.mem_members_iff roots root).mpr hroot
  have anyY :
      (NodeSet.members q.outcome).any (fun y =>
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (mutilatedDirected S q.action) S.count root y) = true :=
    (List.all_eq_true.mp h) root rootMem
  rcases List.any_eq_true.mp anyY with ⟨y, yMem, hy⟩
  exact ⟨y, (NodeSet.mem_members_iff q.outcome y).mp yMem,
    directedReachableBy_of_within q.action hy⟩

/-!
### Recovering executable outcome data from a hedge witness

`HedgeWitness.roots_reach_outcome` deliberately states its mathematical
content as an inductive reachability proposition.  The countermodel, however,
must choose an actual downstream outcome in `Type`.  The lemmas below first
reflect the inductive walk back into the finite Boolean search.  Selection can
then use `listFirstAny`, so no existential is eliminated into data and no
choice principle is introduced.
-/

/-- An inductive Boolean-edge walk determines a finite exact walk. -/
theorem finiteReachable_of_directedReachableBy
    {edge : Fin S.count → Fin S.count → Bool}
    {source target : Fin S.count}
    (reachable : DirectedReachableBy S
      (fun i j => edge i j = true) source target) :
    FiniteReachability.Reachable edge source target := by
  induction reachable with
  | refl =>
      exact FiniteReachability.Reachable.refl edge source
  | tail previous last inductionHypothesis =>
      rcases inductionHypothesis with ⟨length, ⟨walk⟩⟩
      exact ⟨length + 1,
        ⟨FiniteReachability.exactWalk_snoc walk last⟩⟩

/--
On the complete observed-node enumeration, inductive reachability is accepted
by the bounded Boolean search with its standard `S.count` fuel.
-/
theorem finiteWithin_of_directedReachableBy
    {edge : Fin S.count → Fin S.count → Bool}
    {source target : Fin S.count}
    (reachable : DirectedReachableBy S
      (fun i j => edge i j = true) source target) :
    FiniteReachability.within finBeq (NodeSet.enumerated S) edge
        S.count source target = true := by
  have finiteReachable := finiteReachable_of_directedReachableBy reachable
  have bounded := FiniteReachability.boundedWalk_of_reachable finBeq
    (NodeSet.enumerated S) edge finBeq_eq_true_iff
    (NodeSet.mem_enumerated S) finiteReachable
  have found :=
    (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
      (NodeSet.enumerated S) edge finBeq_eq_true_iff
      (NodeSet.mem_enumerated S) (NodeSet.enumerated S).length
      source target).mpr bounded
  simpa [NodeSet.length_enumerated] using found

/-- The propositional root-to-outcome condition reflects to its Boolean test. -/
theorem rootsReachOutcomeBool_of_reachable
    (q : JointKernelQuery S) (roots : NodeSet S)
    (reachable : forall root,
      roots root = true →
        Exists fun outcome =>
          q.outcome outcome = true ∧
            DirectedReachableBy S
              (fun i j => mutilatedDirected S q.action i j = true)
              root outcome) :
    rootsReachOutcomeBool q roots = true := by
  unfold rootsReachOutcomeBool
  apply List.all_eq_true.mpr
  intro root rootMember
  have rootSelected :=
    (NodeSet.mem_members_iff roots root).mp rootMember
  rcases reachable root rootSelected with
    ⟨outcome, outcomeSelected, path⟩
  apply List.any_eq_true.mpr
  exact ⟨outcome,
    (NodeSet.mem_members_iff q.outcome outcome).mpr outcomeSelected,
    finiteWithin_of_directedReachableBy path⟩

/-- Every abstract hedge witness satisfies the executable reachability test. -/
theorem HedgeWitness.rootsReachOutcomeBool
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    rootsReachOutcomeBool q w.roots = true :=
  rootsReachOutcomeBool_of_reachable q w.roots w.roots_reach_outcome

/-- Every selected forest root reaches some enumerated query outcome.  This
is the root-uniform form of the action-branch fact used below. -/
theorem HedgeWitness.root_reaches_outcome_any
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    (NodeSet.members q.outcome).any (fun outcome =>
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (mutilatedDirected S q.action) S.count root outcome) = true :=
  (List.all_eq_true.mp w.rootsReachOutcomeBool) root
    ((NodeSet.mem_members_iff w.roots root).mpr rootIn)

/--
Canonical reachable outcome for an arbitrary forest root.  The non-root
branch returns the witness's already certified outcome seed, making the
function total; all routing theorems use the selected-root branch.
-/
def HedgeWitness.rootReadoutOutcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count) : Fin S.count :=
  if rootIn : w.roots root = true then
    listFirstAny (NodeSet.members q.outcome)
      (fun outcome =>
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (mutilatedDirected S q.action) S.count root outcome)
      (w.root_reaches_outcome_any root rootIn)
  else
    w.outcomeSeed

/-- The root-indexed selector always returns a query outcome, including its
irrelevant fallback branch. -/
theorem HedgeWitness.rootReadoutOutcome_in_outcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count) :
    q.outcome (w.rootReadoutOutcome root) = true := by
  by_cases rootIn : w.roots root = true
  · unfold HedgeWitness.rootReadoutOutcome
    rw [dif_pos rootIn]
    exact (NodeSet.mem_members_iff q.outcome _).mp
      (listFirstAny_mem (NodeSet.members q.outcome) _
        (w.root_reaches_outcome_any root rootIn))
  · simp [HedgeWitness.rootReadoutOutcome, rootIn,
      w.outcomeSeed_in_outcome]

/-- A selected root reaches its root-indexed outcome in the mutilated graph. -/
theorem HedgeWitness.root_reaches_rootReadoutOutcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    FiniteReachability.within finBeq (NodeSet.enumerated S)
      (mutilatedDirected S q.action) S.count root
        (w.rootReadoutOutcome root) = true := by
  unfold HedgeWitness.rootReadoutOutcome
  rw [dif_pos rootIn]
  exact listFirstAny_pred (NodeSet.members q.outcome) _
    (w.root_reaches_outcome_any root rootIn)

/-- The action branch's computed root reaches some enumerated outcome. -/
theorem HedgeWitness.actionRoot_reaches_outcome_any
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    (NodeSet.members q.outcome).any (fun outcome =>
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (mutilatedDirected S q.action) S.count w.actionRoot outcome) = true :=
  w.root_reaches_outcome_any w.actionRoot w.actionRoot_in_roots

/--
Canonical reachable query outcome used by the eventual parity readout.  The
list search, rather than a proposition-level existential, supplies the data.
-/
def HedgeWitness.parityReadoutOutcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : Fin S.count :=
  listFirstAny (NodeSet.members q.outcome)
    (fun outcome =>
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (mutilatedDirected S q.action) S.count w.actionRoot outcome)
    w.actionRoot_reaches_outcome_any

/-- The selected parity-readout vertex belongs to the query outcome. -/
theorem HedgeWitness.parityReadoutOutcome_in_outcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    q.outcome w.parityReadoutOutcome = true :=
  (NodeSet.mem_members_iff q.outcome w.parityReadoutOutcome).mp
    (listFirstAny_mem (NodeSet.members q.outcome) _
      w.actionRoot_reaches_outcome_any)

/-- The selected outcome is reached in the action-mutilated graph. -/
theorem HedgeWitness.actionRoot_reaches_parityReadoutOutcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    FiniteReachability.within finBeq (NodeSet.enumerated S)
      (mutilatedDirected S q.action) S.count w.actionRoot
        w.parityReadoutOutcome = true :=
  listFirstAny_pred (NodeSet.members q.outcome) _
    w.actionRoot_reaches_outcome_any

/-!
### A canonical directed route to the selected outcome

The Boolean reachability certificate can also drive an explicit route.  At
each positive fuel level, the construction takes the first enumerated child
whose remaining bounded search still reaches the target.  Its proof argument
is used only to rule out a failed search; the selected vertices themselves are
computed by `find?` through `listFirstAny`.
-/

/--
A nontrivial bounded reachability certificate contains a first edge whose
target remains reachable with one less unit of fuel.
-/
theorem finiteWithin_successor_any
    {α : Type} (same : α → α → Bool) (nodes : List α)
    (edge : α → α → Bool)
    (same_iff : ∀ left right, same left right = true ↔ left = right)
    (complete : ∀ node, node ∈ nodes)
    {fuel : Nat} {source target : α}
    (reachable : FiniteReachability.within same nodes edge (fuel + 1)
      source target = true)
    (different : same source target = false) :
    nodes.any (fun middle => edge source middle &&
      FiniteReachability.within same nodes edge fuel middle target) = true := by
  have bounded :=
    (FiniteReachability.within_eq_true_iff_boundedWalk same nodes edge
      same_iff complete (fuel + 1) source target).mp reachable
  rcases bounded with ⟨length, bound, ⟨walk⟩⟩
  cases walk with
  | refl =>
      have sameSelf : same source source = true :=
        (same_iff source source).mpr rfl
      rw [sameSelf] at different
      contradiction
  | @step restLength _ middle _ first rest =>
      have restBound : restLength ≤ fuel := by omega
      have restReachable :
          FiniteReachability.within same nodes edge fuel middle target =
            true :=
        (FiniteReachability.within_eq_true_iff_boundedWalk same nodes edge
          same_iff complete fuel middle target).mpr
            ⟨restLength, restBound, ⟨rest⟩⟩
      exact List.any_eq_true.mpr
        ⟨middle, complete middle,
          Bool.and_eq_true_iff.mpr ⟨first, restReachable⟩⟩

/--
Executable route following edges of the action-mutilated observed graph.
The decreasing reachability proof supplies the recursive call but contributes
no nonconstructive data.
-/
def mutilatedDirectedRoute (action : NodeSet S) (target : Fin S.count) :
    (fuel : Nat) → (source : Fin S.count) →
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (mutilatedDirected S action) fuel source target = true →
      List (Fin S.count)
  | 0, source, _reachable => [source]
  | fuel + 1, source, reachable =>
      if same : finBeq source target = true then
        [source]
      else
        let candidates := NodeSet.enumerated S
        let continues := fun middle =>
          mutilatedDirected S action source middle &&
            FiniteReachability.within finBeq candidates
              (mutilatedDirected S action) fuel middle target
        let found : candidates.any continues = true :=
          finiteWithin_successor_any finBeq candidates
            (mutilatedDirected S action) finBeq_eq_true_iff
            (NodeSet.mem_enumerated S) reachable
            (Bool.eq_false_iff.mpr same)
        let next := listFirstAny candidates continues found
        let nextReachable :
            FiniteReachability.within finBeq candidates
              (mutilatedDirected S action) fuel next target = true :=
          (Bool.and_eq_true_iff.mp
            (listFirstAny_pred candidates continues found)).2
        source :: mutilatedDirectedRoute action target fuel next nextReachable

/-- The canonical route has the advertised endpoints and mutilated edges. -/
theorem mutilatedDirectedRoute_spec (action : NodeSet S)
    (target : Fin S.count) (fuel : Nat) (source : Fin S.count)
    (reachable : FiniteReachability.within finBeq (NodeSet.enumerated S)
      (mutilatedDirected S action) fuel source target = true) :
    let route := mutilatedDirectedRoute action target fuel source reachable
    route.head? = some source ∧
      route.getLast? = some target ∧
        PathSpecification.Consecutive
          (fun parent child =>
            mutilatedDirected S action parent child = true) route := by
  induction fuel generalizing source with
  | zero =>
      have bounded :=
        (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
          (NodeSet.enumerated S) (mutilatedDirected S action)
          finBeq_eq_true_iff (NodeSet.mem_enumerated S) 0 source target).mp
          reachable
      rcases bounded with ⟨length, bound, ⟨walk⟩⟩
      have lengthZero : length = 0 := Nat.eq_zero_of_le_zero bound
      subst length
      have sourceEq : source = target := walk.eq_of_length_zero
      subst source
      simp [mutilatedDirectedRoute, PathSpecification.Consecutive]
  | succ fuel inductionHypothesis =>
      by_cases same : finBeq source target = true
      · have sourceEq : source = target :=
          (finBeq_eq_true_iff source target).mp same
        subst source
        simp [mutilatedDirectedRoute, same,
          PathSpecification.Consecutive]
      · have different : finBeq source target = false :=
          Bool.eq_false_iff.mpr same
        let candidates := NodeSet.enumerated S
        let continues := fun middle =>
          mutilatedDirected S action source middle &&
            FiniteReachability.within finBeq candidates
              (mutilatedDirected S action) fuel middle target
        have found : candidates.any continues = true :=
          finiteWithin_successor_any finBeq candidates
            (mutilatedDirected S action) finBeq_eq_true_iff
            (NodeSet.mem_enumerated S) reachable different
        let next := listFirstAny candidates continues found
        have nextParts : continues next = true :=
          listFirstAny_pred candidates continues found
        have firstEdge : mutilatedDirected S action source next = true :=
          (Bool.and_eq_true_iff.mp nextParts).1
        have nextReachable :
            FiniteReachability.within finBeq candidates
              (mutilatedDirected S action) fuel next target = true :=
          (Bool.and_eq_true_iff.mp nextParts).2
        have rest := inductionHypothesis next nextReachable
        dsimp only at rest
        rw [mutilatedDirectedRoute]
        simp only [same, Bool.false_eq_true, ↓reduceDIte]
        cases routeEq : mutilatedDirectedRoute action target fuel next
            nextReachable with
        | nil =>
            have impossible := rest.1
            rw [routeEq] at impossible
            simp at impossible
        | cons head tail =>
            have headEq : head = next := by
              have restHead := rest.1
              rw [routeEq] at restHead
              simpa using restHead
            subst head
            rw [routeEq] at rest
            exact ⟨rfl, rest.2.1, firstEdge, rest.2.2⟩

/-- A mutilated directed edge cannot enter the intervention set. -/
theorem action_false_of_mutilatedDirected
    (action : NodeSet S) {parent child : Fin S.count}
    (edge : mutilatedDirected S action parent child = true) :
    action child = false := by
  cases selected : action child with
  | false => rfl
  | true => simp [mutilatedDirected, selected] at edge

/--
If the first vertex is not intervened, every vertex of a consecutive
mutilated directed route is likewise free under that intervention.
-/
theorem consecutive_mutilatedDirected_avoids_action
    (action : NodeSet S) (route : List (Fin S.count))
    (source : Fin S.count) (starts : route.head? = some source)
    (sourceFree : action source = false)
    (consecutive : PathSpecification.Consecutive
      (fun parent child =>
        mutilatedDirected S action parent child = true) route) :
    ∀ node, node ∈ route → action node = false := by
  induction route generalizing source with
  | nil =>
      intro node member
      simp at member
  | cons head tail inductionHypothesis =>
      have headEq : head = source := by
        simpa using Option.some.inj starts
      subst head
      cases tail with
      | nil =>
          intro node member
          simpa using List.mem_singleton.mp member ▸ sourceFree
      | cons next rest =>
          have firstEdge : mutilatedDirected S action source next = true :=
            consecutive.1
          have nextFree := action_false_of_mutilatedDirected action firstEdge
          intro node member
          rcases List.mem_cons.mp member with same | tailMember
          · simpa [same] using sourceFree
          · exact inductionHypothesis next rfl nextFree consecutive.2 node
              tailMember

/-!
The observed topological order makes any directed readout route strictly
increasing.  Besides ruling out cycles, this gives the uniqueness needed to
turn a route into an executable child-to-parent lookup without selecting from
a proposition-level existence proof.
-/

/-- Every vertex after the head of a strictly increasing finite route is
strictly later than that head. -/
theorem PathSpecification.Consecutive.fin_lt_of_mem_tail
    {n : Nat} {head : Fin n} {tail : List (Fin n)}
    (consecutive : PathSpecification.Consecutive
      (fun left right : Fin n => left.val < right.val) (head :: tail)) :
    ∀ node, node ∈ tail → head.val < node.val := by
  induction tail generalizing head with
  | nil =>
      intro node member
      simp at member
  | cons next rest inductionHypothesis =>
      have first : head.val < next.val := consecutive.1
      intro node member
      rcases List.mem_cons.mp member with same | later
      · simpa [same] using first
      · exact Nat.lt_trans first
          (inductionHypothesis consecutive.2 node later)

/-- A route that strictly increases in `Fin`'s value has no repeated vertex. -/
theorem PathSpecification.Consecutive.nodup_of_fin_lt
    {n : Nat} (route : List (Fin n))
    (consecutive : PathSpecification.Consecutive
      (fun left right : Fin n => left.val < right.val) route) :
    route.Nodup := by
  induction route with
  | nil => exact List.nodup_nil
  | cons head tail inductionHypothesis =>
      apply List.nodup_cons.mpr
      constructor
      · intro member
        have impossible := consecutive.fin_lt_of_mem_tail head member
        exact (Nat.lt_irrefl head.val impossible).elim
      · cases tail with
        | nil => exact List.nodup_nil
        | cons next rest =>
            exact inductionHypothesis consecutive.2

/--
Return the vertex immediately before the first occurrence of `target` in a
route.  A head occurrence has no predecessor; later occurrences are found by
the adjacent-pair scan.  The construction is entirely data-driven.
-/
def routePredecessor {α : Type} [DecidableEq α] :
    List α → α → Option α
  | parent :: child :: rest, target =>
      if child = target then some parent
      else routePredecessor (child :: rest) target
  | _, _target => none

/-- An immediately displayed child is assigned its displayed parent. -/
@[simp] theorem routePredecessor_pair
    {α : Type} [DecidableEq α]
    (parent child : α) (rest : List α) :
    routePredecessor (parent :: child :: rest) child = some parent := by
  simp [routePredecessor]

/-- A displayed adjacent pair is found after a front segment that contains
neither a previous target nor the target as its final vertex. -/
theorem routePredecessor_append_pair
    {α : Type} [DecidableEq α]
    (front : List α) (parent target : α) (suffix : List α)
    (targetNotFront : target ∉ front) (parentNe : parent ≠ target) :
    routePredecessor (front ++ parent :: target :: suffix) target =
      some parent := by
  induction front with
  | nil => simp
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          change (if parent = target then some first
            else routePredecessor (parent :: target :: suffix) target) =
              some parent
          rw [if_neg parentNe]
          exact routePredecessor_pair parent target suffix
      | cons second rest =>
          have secondNe : second ≠ target := by
            intro equal
            apply targetNotFront
            simp [equal]
          have targetNotRest : target ∉ second :: rest := by
            intro member
            apply targetNotFront
            exact List.mem_cons_of_mem first member
          simp only [List.cons_append]
          rw [routePredecessor]
          simp only [secondNe, ↓reduceIte]
          exact inductionHypothesis targetNotRest

/-- On a duplicate-free route, the predecessor scan finds any displayed
adjacent pair, independently of where that pair occurs. -/
theorem routePredecessor_of_adjacent_nodup
    {α : Type} [DecidableEq α]
    (front : List α) (parent target : α) (suffix : List α)
    (nodup : (front ++ parent :: target :: suffix).Nodup) :
    routePredecessor (front ++ parent :: target :: suffix) target =
      some parent := by
  have parts := List.nodup_append.mp nodup
  have targetNotFront : target ∉ front := by
    intro member
    exact parts.2.2 target member target (by simp) rfl
  have parentNe : parent ≠ target := by
    intro equal
    have tailNodup := parts.2.1
    have parentFresh := (List.nodup_cons.mp tailNodup).1
    apply parentFresh
    simp [equal]
  exact routePredecessor_append_pair front parent target suffix
    targetNotFront parentNe

/-- Auxiliary suffix induction: the lookup in the full route recognizes
every adjacent pair of a duplicate-free suffix. -/
theorem routePredecessor_consecutive_suffix
    {α : Type} [DecidableEq α]
    (front suffix : List α) (nodup : (front ++ suffix).Nodup) :
    PathSpecification.Consecutive
      (fun parent child =>
        routePredecessor (front ++ suffix) child = some parent)
      suffix := by
  induction suffix generalizing front with
  | nil => trivial
  | cons parent tail inductionHypothesis =>
      cases tail with
      | nil => trivial
      | cons child rest =>
          constructor
          · exact routePredecessor_of_adjacent_nodup front parent child
              rest nodup
          · have reassociated :
                front ++ parent :: child :: rest =
                  (front ++ [parent]) ++ child :: rest := by
              simp
            have restNodup :
                ((front ++ [parent]) ++ child :: rest).Nodup := by
              rw [← reassociated]
              exact nodup
            have tailConsecutive :=
              inductionHypothesis (front ++ [parent]) restNodup
            rw [reassociated]
            exact tailConsecutive

/-- The predecessor lookup for a duplicate-free route recognizes every one
of its consecutive parent-child pairs. -/
theorem routePredecessor_consecutive
    {α : Type} [DecidableEq α]
    (route : List α) (nodup : route.Nodup) :
    PathSpecification.Consecutive
      (fun parent child => routePredecessor route child = some parent)
      route := by
  simpa using routePredecessor_consecutive_suffix ([] : List α)
    route (by simpa using nodup)

/-- A target absent from the route cannot acquire a predecessor. -/
theorem routePredecessor_eq_none_of_not_mem
    {α : Type} [DecidableEq α] (route : List α) (target : α)
    (absent : target ∉ route) :
    routePredecessor route target = none := by
  induction route with
  | nil => rfl
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil => rfl
      | cons second rest =>
          have secondNe : second ≠ target := by
            intro equal
            apply absent
            simp [equal]
          have absentTail : target ∉ second :: rest := by
            intro member
            exact absent (List.mem_cons_of_mem first member)
          change (if second = target then some first
            else routePredecessor (second :: rest) target) = none
          rw [if_neg secondNe]
          exact inductionHypothesis absentTail

/-- The first vertex of a duplicate-free route has no predecessor. -/
theorem routePredecessor_head_eq_none
    {α : Type} [DecidableEq α] (route : List α) (head : α)
    (starts : route.head? = some head) (nodup : route.Nodup) :
    routePredecessor route head = none := by
  cases route with
  | nil => simp at starts
  | cons first tail =>
      have firstEq : first = head := by
        simpa using Option.some.inj starts
      subst first
      have fresh : head ∉ tail := (List.nodup_cons.mp nodup).1
      cases tail with
      | nil => rfl
      | cons second rest =>
          have secondNe : second ≠ head := by
            intro equal
            apply fresh
            simp [equal]
          change (if second = head then some head
            else routePredecessor (second :: rest) head) = none
          rw [if_neg secondNe]
          exact routePredecessor_eq_none_of_not_mem
            (second :: rest) head fresh

/-- Any predecessor returned by the scan is an actual consecutive edge of
the route.  This converse complements `routePredecessor_consecutive`. -/
theorem routePredecessor_rel_of_eq_some
    {α : Type} [DecidableEq α] (relation : α → α → Prop)
    (route : List α) (parent child : α)
    (consecutive : PathSpecification.Consecutive relation route)
    (found : routePredecessor route child = some parent) :
    relation parent child := by
  induction route with
  | nil => simp [routePredecessor] at found
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil => simp [routePredecessor] at found
      | cons second rest =>
          if same : second = child then
            subst second
            have parentEq : first = parent := by
              simpa [routePredecessor] using found
            subst parent
            exact consecutive.1
          else
            have tailFound :
                routePredecessor (second :: rest) child = some parent := by
              simpa [routePredecessor, same] using found
            exact inductionHypothesis consecutive.2 tailFound

/-- Return the vertex immediately after the first occurrence of `target` in a
route.  This is the forward dual of `routePredecessor`. -/
def routeSuccessor {α : Type} [DecidableEq α] :
    List α → α → Option α
  | parent :: child :: rest, target =>
      if parent = target then some child
      else routeSuccessor (child :: rest) target
  | _, _target => none

/-- Any successor returned by the scan is an actual consecutive edge. -/
theorem routeSuccessor_rel_of_eq_some
    {α : Type} [DecidableEq α] (relation : α → α → Prop)
    (route : List α) (parent child : α)
    (consecutive : PathSpecification.Consecutive relation route)
    (found : routeSuccessor route parent = some child) :
    relation parent child := by
  induction route with
  | nil => simp [routeSuccessor] at found
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil => simp [routeSuccessor] at found
      | cons second rest =>
          if same : first = parent then
            subst first
            have childEq : second = child := by
              simpa [routeSuccessor] using found
            subst child
            exact consecutive.1
          else
            have tailFound :
                routeSuccessor (second :: rest) parent = some child := by
              simpa [routeSuccessor, same] using found
            exact inductionHypothesis consecutive.2 tailFound

/-- Both endpoints returned by a successor scan occur on the scanned route. -/
theorem routeSuccessor_mem
    {α : Type} [DecidableEq α] (route : List α) (parent child : α)
    (found : routeSuccessor route parent = some child) :
    parent ∈ route ∧ child ∈ route := by
  induction route with
  | nil => simp [routeSuccessor] at found
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil => simp [routeSuccessor] at found
      | cons second rest =>
          if same : first = parent then
            subst first
            have childEq : second = child := by
              simpa [routeSuccessor] using found
            subst child
            simp
          else
            have tailFound :
                routeSuccessor (second :: rest) parent = some child := by
              simpa [routeSuccessor, same] using found
            have members := inductionHypothesis tailFound
            exact ⟨List.mem_cons_of_mem first members.1,
              List.mem_cons_of_mem first members.2⟩

/-- A nonterminal member of a duplicate-free route has a successor. -/
theorem routeSuccessor_isSome_of_mem_of_not_last
    {α : Type} [DecidableEq α] (route : List α) (target : α)
    (nodup : route.Nodup) (member : target ∈ route)
    (notLast : route.getLast? ≠ some target) :
    (routeSuccessor route target).isSome = true := by
  induction route with
  | nil => simp at member
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          have targetEq : target = first := List.mem_singleton.mp member
          have same : first = target := targetEq.symm
          subst first
          exact False.elim (notLast rfl)
      | cons second rest =>
          if same : first = target then
            simp [routeSuccessor, same]
          else
            have tailMember : target ∈ second :: rest := by
              rcases List.mem_cons.mp member with equal | later
              · exact False.elim (same equal.symm)
              · exact later
            have tailNodup : (second :: rest).Nodup :=
              (List.nodup_cons.mp nodup).2
            have tailNotLast :
                (second :: rest).getLast? ≠ some target := by
              intro equal
              apply notLast
              simpa [List.getLast?_cons_cons] using equal
            simpa [routeSuccessor, same] using
              inductionHypothesis tailNodup tailMember tailNotLast

/-- Select the first route in a list that supplies a successor for `parent`. -/
def firstRouteSuccessor {α : Type} [DecidableEq α] :
    List (List α) → α → Option α
  | [], _parent => none
  | route :: routes, parent =>
      match routeSuccessor route parent with
      | some child => some child
      | none => firstRouteSuccessor routes parent

/-- A successful multi-route lookup comes from one of the listed routes. -/
theorem firstRouteSuccessor_eq_some
    {α : Type} [DecidableEq α]
    (routes : List (List α)) (parent child : α)
    (found : firstRouteSuccessor routes parent = some child) :
    Exists fun route =>
      route ∈ routes ∧ routeSuccessor route parent = some child := by
  induction routes with
  | nil => simp [firstRouteSuccessor] at found
  | cons route routes inductionHypothesis =>
      cases routeFound : routeSuccessor route parent with
      | none =>
          have tailFound : firstRouteSuccessor routes parent = some child := by
            simpa [firstRouteSuccessor, routeFound] using found
          rcases inductionHypothesis tailFound with
            ⟨witness, member, equal⟩
          exact ⟨witness, List.mem_cons_of_mem route member, equal⟩
      | some candidate =>
          have candidateEq : candidate = child := by
            simpa [firstRouteSuccessor, routeFound] using found
          subst candidate
          exact ⟨route, List.mem_cons_self, routeFound⟩

/-- If any listed route supplies a successor, the first-successful-route
search also supplies one. -/
theorem firstRouteSuccessor_isSome_of_member
    {α : Type} [DecidableEq α]
    (routes : List (List α)) (route : List α) (parent : α)
    (routeMember : route ∈ routes)
    (hasSuccessor : (routeSuccessor route parent).isSome = true) :
    (firstRouteSuccessor routes parent).isSome = true := by
  induction routes with
  | nil => simp at routeMember
  | cons first rest inductionHypothesis =>
      cases firstFound : routeSuccessor first parent with
      | some child => simp [firstRouteSuccessor, firstFound]
      | none =>
          have routeInRest : route ∈ rest := by
            rcases List.mem_cons.mp routeMember with equal | later
            · subst first
              simp [firstFound] at hasSuccessor
            · exact later
          simpa [firstRouteSuccessor, firstFound] using
            inductionHypothesis routeInRest

/-- If a value is preserved across every consecutive pair, its values at the
two advertised endpoints agree. -/
theorem PathSpecification.Consecutive.end_eq_start_of_step_eq
    {α β : Type} (value : α → β)
    (route : List α) (source target : α)
    (starts : route.head? = some source)
    (finishes : route.getLast? = some target)
    (consecutive : PathSpecification.Consecutive
      (fun parent child => value child = value parent) route) :
    value target = value source := by
  induction route generalizing source with
  | nil => simp at starts
  | cons head tail inductionHypothesis =>
      have headEq : head = source := by
        simpa using Option.some.inj starts
      subst head
      cases tail with
      | nil =>
          have targetEq : source = target := by
            simpa using Option.some.inj finishes
          subst target
          rfl
      | cons next rest =>
          have tailFinishes : (next :: rest).getLast? = some target := by
            simpa [List.getLast?_cons_cons] using finishes
          exact
            (inductionHypothesis next rfl tailFinishes consecutive.2).trans
              consecutive.1

/-- Canonical root-to-outcome route for every selected root of a hedge.  The
singleton fallback makes the function total away from `w.roots`. -/
def HedgeWitness.rootReadoutRoute
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count) : List (Fin S.count) :=
  if rootIn : w.roots root = true then
    mutilatedDirectedRoute q.action (w.rootReadoutOutcome root) S.count root
      (w.root_reaches_rootReadoutOutcome root rootIn)
  else
    [root]

/-- A selected root's route starts at that root. -/
theorem HedgeWitness.rootReadoutRoute_starts
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    (w.rootReadoutRoute root).head? = some root := by
  unfold HedgeWitness.rootReadoutRoute
  rw [dif_pos rootIn]
  simpa using
    (mutilatedDirectedRoute_spec q.action (w.rootReadoutOutcome root) S.count
      root (w.root_reaches_rootReadoutOutcome root rootIn)).1

/-- A selected root's route ends at its canonical query outcome. -/
theorem HedgeWitness.rootReadoutRoute_finishes
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    (w.rootReadoutRoute root).getLast? =
      some (w.rootReadoutOutcome root) := by
  unfold HedgeWitness.rootReadoutRoute
  rw [dif_pos rootIn]
  simpa using
    (mutilatedDirectedRoute_spec q.action (w.rootReadoutOutcome root) S.count
      root (w.root_reaches_rootReadoutOutcome root rootIn)).2.1

/-- Every edge of a selected root's route survives the query intervention. -/
theorem HedgeWitness.rootReadoutRoute_consecutive
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    PathSpecification.Consecutive
      (fun parent child =>
        mutilatedDirected S q.action parent child = true)
      (w.rootReadoutRoute root) := by
  unfold HedgeWitness.rootReadoutRoute
  rw [dif_pos rootIn]
  simpa using
    (mutilatedDirectedRoute_spec q.action (w.rootReadoutOutcome root) S.count
      root (w.root_reaches_rootReadoutOutcome root rootIn)).2.2

/-- Strict topological increase makes every selected root's route
duplicate-free. -/
theorem HedgeWitness.rootReadoutRoute_nodup
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    (w.rootReadoutRoute root).Nodup := by
  apply PathSpecification.Consecutive.nodup_of_fin_lt
    (w.rootReadoutRoute root)
  exact (w.rootReadoutRoute_consecutive root rootIn).mono
    (fun parent child edge => mutilatedDirected_earlier S q.action edge)

/-- No vertex of a selected root's canonical route is intervened upon. -/
theorem HedgeWitness.rootReadoutRoute_avoids_action
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    ∀ node, node ∈ w.rootReadoutRoute root → q.action node = false := by
  have rootInSmall := ((w.small_forest.roots_exact root).mp rootIn).1
  have rootFree := w.small_avoids_intervention root rootInSmall
  exact consecutive_mutilatedDirected_avoids_action q.action
    (w.rootReadoutRoute root) root (w.rootReadoutRoute_starts root rootIn)
    rootFree (w.rootReadoutRoute_consecutive root rootIn)

/-- Deterministic predecessor lookup for a root-indexed readout route. -/
def HedgeWitness.rootReadoutParent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root child : Fin S.count) :
    Option (Fin S.count) :=
  routePredecessor (w.rootReadoutRoute root) child

/-- The predecessor lookup recognizes every pair of a selected root's route. -/
theorem HedgeWitness.rootReadoutParent_consecutive
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    PathSpecification.Consecutive
      (fun parent child => w.rootReadoutParent root child = some parent)
      (w.rootReadoutRoute root) := by
  simpa [HedgeWitness.rootReadoutParent] using
    routePredecessor_consecutive (w.rootReadoutRoute root)
      (w.rootReadoutRoute_nodup root rootIn)

/-- A selected route source has no predecessor on its own route. -/
theorem HedgeWitness.rootReadoutParent_source
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    w.rootReadoutParent root root = none := by
  exact routePredecessor_head_eq_none (w.rootReadoutRoute root) root
    (w.rootReadoutRoute_starts root rootIn)
    (w.rootReadoutRoute_nodup root rootIn)

/-- Every predecessor returned on a selected root's route is its actual
action-mutilated directed edge. -/
theorem HedgeWitness.rootReadoutParent_mutilatedDirected
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) {parent child : Fin S.count}
    (found : w.rootReadoutParent root child = some parent) :
    mutilatedDirected S q.action parent child = true := by
  apply routePredecessor_rel_of_eq_some
    (fun left right => mutilatedDirected S q.action left right = true)
    (w.rootReadoutRoute root) parent child
    (w.rootReadoutRoute_consecutive root rootIn)
  simpa [HedgeWitness.rootReadoutParent] using found

/-- Canonical routes for all hedge roots, in the stable enumeration order of
the root set. -/
def HedgeWitness.rootReadoutRoutes
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : List (List (Fin S.count)) :=
  (NodeSet.members w.roots).map w.rootReadoutRoute

/-!
The all-root readout must not choose two different outgoing edges at an
intersection.  `rootReadoutSuccessor` therefore takes the first available
route successor at each vertex.  Once routes merge they follow one selected
suffix, giving an acyclic no-splitting routing forest.  Query outcomes are
forced to be sinks, so encountering an outcome truncates any longer route.
-/

/-- First-route successor map for the complete root-to-outcome routing
forest, with every query outcome made a sink. -/
def HedgeWitness.rootReadoutSuccessor
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : ForestChild S :=
  fun parent =>
    if q.outcome parent then none
    else firstRouteSuccessor w.rootReadoutRoutes parent

/-- Every selected routing successor is an edge of the action-mutilated
observed graph. -/
theorem HedgeWitness.rootReadoutSuccessor_mutilatedDirected
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) {parent child : Fin S.count}
    (found : w.rootReadoutSuccessor parent = some child) :
    mutilatedDirected S q.action parent child = true := by
  unfold HedgeWitness.rootReadoutSuccessor at found
  split at found
  · contradiction
  · rcases firstRouteSuccessor_eq_some
        w.rootReadoutRoutes parent child found with
      ⟨route, routeMember, routeFound⟩
    rcases List.mem_map.mp routeMember with
      ⟨root, rootMember, routeEq⟩
    have rootIn := (NodeSet.mem_members_iff w.roots root).mp rootMember
    subst route
    exact routeSuccessor_rel_of_eq_some
      (fun left right => mutilatedDirected S q.action left right = true)
      (w.rootReadoutRoute root) parent child
      (w.rootReadoutRoute_consecutive root rootIn) routeFound

/-- A routing successor is in particular a genuine directed edge of the
original signature. -/
theorem HedgeWitness.rootReadoutSuccessor_directed
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) {parent child : Fin S.count}
    (found : w.rootReadoutSuccessor parent = some child) :
    S.directed parent child = true := by
  have edge := w.rootReadoutSuccessor_mutilatedDirected found
  unfold mutilatedDirected at edge
  split at edge
  · contradiction
  · exact edge

/-- Routing successors are strictly later in the observed topological order. -/
theorem HedgeWitness.rootReadoutSuccessor_earlier
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) {parent child : Fin S.count}
    (found : w.rootReadoutSuccessor parent = some child) :
    parent.val < child.val :=
  mutilatedDirected_earlier S q.action
    (w.rootReadoutSuccessor_mutilatedDirected found)

/-- Query outcomes are terminal vertices of the routing forest. -/
theorem HedgeWitness.rootReadoutSuccessor_of_outcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) {parent : Fin S.count}
    (outcome : q.outcome parent = true) :
    w.rootReadoutSuccessor parent = none := by
  simp [HedgeWitness.rootReadoutSuccessor, outcome]

/-- Vertices used by at least one canonical root-to-outcome route. -/
def HedgeWitness.rootReadoutNodes
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : NodeSet S :=
  fun node => decide (node ∈ w.rootReadoutRoutes.flatten)

/-- Boolean membership in the routing node set is ordinary flattened-list
membership. -/
theorem HedgeWitness.rootReadoutNodes_iff
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (node : Fin S.count) :
    w.rootReadoutNodes node = true ↔
      node ∈ w.rootReadoutRoutes.flatten := by
  simp [HedgeWitness.rootReadoutNodes]

/-- Both endpoints of every selected routing edge belong to the routing node
set. -/
theorem HedgeWitness.rootReadoutSuccessor_nodes
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) {parent child : Fin S.count}
    (found : w.rootReadoutSuccessor parent = some child) :
    w.rootReadoutNodes parent = true ∧
      w.rootReadoutNodes child = true := by
  unfold HedgeWitness.rootReadoutSuccessor at found
  split at found
  · contradiction
  · rcases firstRouteSuccessor_eq_some
        w.rootReadoutRoutes parent child found with
      ⟨route, routeMember, routeFound⟩
    have members := routeSuccessor_mem route parent child routeFound
    constructor
    · apply (w.rootReadoutNodes_iff parent).mpr
      exact List.mem_flatten.mpr ⟨route, routeMember, members.1⟩
    · apply (w.rootReadoutNodes_iff child).mpr
      exact List.mem_flatten.mpr ⟨route, routeMember, members.2⟩

/-- Every routing vertex outside the query outcome set has a selected
successor. -/
theorem HedgeWitness.rootReadoutSuccessor_exists_of_node
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (node : Fin S.count)
    (nodeIn : w.rootReadoutNodes node = true)
    (notOutcome : q.outcome node = false) :
    Exists fun child => w.rootReadoutSuccessor node = some child := by
  have flatMember := (w.rootReadoutNodes_iff node).mp nodeIn
  rcases List.mem_flatten.mp flatMember with
    ⟨route, routeMember, nodeMember⟩
  rcases List.mem_map.mp routeMember with
    ⟨root, rootMember, routeEq⟩
  have rootIn := (NodeSet.mem_members_iff w.roots root).mp rootMember
  subst route
  have notLast : (w.rootReadoutRoute root).getLast? ≠ some node := by
    intro equal
    have endpoint := w.rootReadoutRoute_finishes root rootIn
    have nodeEq : w.rootReadoutOutcome root = node :=
      Option.some.inj (endpoint.symm.trans equal)
    have selected := w.rootReadoutOutcome_in_outcome root
    rw [nodeEq, notOutcome] at selected
    contradiction
  have routeSome := routeSuccessor_isSome_of_mem_of_not_last
    (w.rootReadoutRoute root) node
    (w.rootReadoutRoute_nodup root rootIn) nodeMember notLast
  have firstSome := firstRouteSuccessor_isSome_of_member
    w.rootReadoutRoutes (w.rootReadoutRoute root) node
    (List.mem_map.mpr ⟨root, rootMember, rfl⟩) routeSome
  have allSome : (w.rootReadoutSuccessor node).isSome = true := by
    simp [HedgeWitness.rootReadoutSuccessor, notOutcome, firstSome]
  exact Option.isSome_iff_exists.mp allSome

/-- Every hedge root belongs to the union of its canonical readout routes. -/
theorem HedgeWitness.root_in_rootReadoutNodes
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    w.rootReadoutNodes root = true := by
  apply (w.rootReadoutNodes_iff root).mpr
  apply List.mem_flatten.mpr
  refine ⟨w.rootReadoutRoute root, ?_, ?_⟩
  · exact List.mem_map.mpr
      ⟨root, (NodeSet.mem_members_iff w.roots root).mpr rootIn, rfl⟩
  · have starts := w.rootReadoutRoute_starts root rootIn
    cases routeEq : w.rootReadoutRoute root with
    | nil => simp [routeEq] at starts
    | cons head tail =>
        have headEq : head = root := by
          rw [routeEq] at starts
          simpa using Option.some.inj starts
        simp [headEq]

/-- Every vertex used by the union of canonical root routes is free under the
query intervention.  This lifts the route-local avoidance theorem through
the flattened, root-indexed route enumeration. -/
theorem HedgeWitness.rootReadoutNodes_avoids_action
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (node : Fin S.count)
    (nodeIn : w.rootReadoutNodes node = true) :
    q.action node = false := by
  have flatMember := (w.rootReadoutNodes_iff node).mp nodeIn
  rcases List.mem_flatten.mp flatMember with
    ⟨route, routeMember, nodeMember⟩
  rcases List.mem_map.mp routeMember with
    ⟨root, rootMember, routeEq⟩
  have rootIn := (NodeSet.mem_members_iff w.roots root).mp rootMember
  subst route
  exact w.rootReadoutRoute_avoids_action root rootIn node nodeMember

/-- A routing sink is necessarily a query outcome. -/
theorem HedgeWitness.rootReadoutSuccessor_none_is_outcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (node : Fin S.count)
    (nodeIn : w.rootReadoutNodes node = true)
    (sink : w.rootReadoutSuccessor node = none) :
    q.outcome node = true := by
  cases outcome : q.outcome node with
  | true => rfl
  | false =>
      rcases w.rootReadoutSuccessor_exists_of_node node nodeIn outcome with
        ⟨child, found⟩
      rw [sink] at found
      contradiction

/-- The routing successor map mentions only selected vertices and valid
directed edges. -/
theorem HedgeWitness.rootReadoutSuccessor_wellFormed
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    childWellFormedBool w.rootReadoutNodes
      w.rootReadoutSuccessor = true := by
  unfold childWellFormedBool
  apply List.all_eq_true.mpr
  intro parent _member
  cases parentIn : w.rootReadoutNodes parent with
  | false =>
      have successorNone : w.rootReadoutSuccessor parent = none := by
        cases successorEq : w.rootReadoutSuccessor parent with
        | none => rfl
        | some child =>
            have inside := (w.rootReadoutSuccessor_nodes successorEq).1
            rw [parentIn] at inside
            contradiction
      simp [successorNone]
  | true =>
      cases successorEq : w.rootReadoutSuccessor parent with
      | none => rfl
      | some child =>
          have childIn := (w.rootReadoutSuccessor_nodes successorEq).2
          have edge := w.rootReadoutSuccessor_directed successorEq
          simp [childIn, edge]

/-- Outcome sink reached by following the no-splitting routing forest from a
selected hedge root. -/
def HedgeWitness.rootReadoutSink
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) : Fin S.count :=
  forestSink w.rootReadoutNodes w.rootReadoutSuccessor
    w.rootReadoutSuccessor_wellFormed root
    (w.root_in_rootReadoutNodes root rootIn)

/-- Following the selected routing forest from any hedge root terminates at
a vertex in the query outcome set. -/
theorem HedgeWitness.rootReadoutSink_in_outcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (root : Fin S.count)
    (rootIn : w.roots root = true) :
    q.outcome (w.rootReadoutSink root rootIn) = true := by
  have sinkSpec := forestSink_spec w.rootReadoutNodes
    w.rootReadoutSuccessor w.rootReadoutSuccessor_wellFormed root
    (w.root_in_rootReadoutNodes root rootIn)
  exact w.rootReadoutSuccessor_none_is_outcome
    (w.rootReadoutSink root rootIn) sinkSpec.1 sinkSpec.2

/-!
### Composing a c-forest with its outcome readout

A readout route may pass through another vertex of the hedge forest.  Treating
the forest and readout maps independently would then split one Boolean stream
between two successors.  The left-biased composition below avoids that bug.
For the hedge-specific maps, the action-free readout edge receives priority:
once a stream reaches a routing vertex it stays on that route instead of being
redirected through a later intervened forest vertex.  Every selected edge
remains a genuine directed edge, and strict topological order therefore still
makes the combined map acyclic.
-/

/-- Use `preferred` on every selected priority vertex and `fallback`
elsewhere.  In particular, a priority sink remains a sink: `none` does not
fall through to the other map. -/
def forestChildPrioritize (priorityNodes : NodeSet S)
    (preferred fallback : ForestChild S) : ForestChild S :=
  fun parent =>
    if priorityNodes parent then preferred parent else fallback parent

/-- Priority composition preserves executable child-map well-formedness on
the union of the priority and fallback node sets. -/
theorem childWellFormedBool_forestChildPrioritize
    (priorityNodes fallbackNodes : NodeSet S)
    (preferred fallback : ForestChild S)
    (preferredWellFormed :
      childWellFormedBool priorityNodes preferred = true)
    (fallbackWellFormed :
      childWellFormedBool fallbackNodes fallback = true) :
    childWellFormedBool (NodeSet.union priorityNodes fallbackNodes)
      (forestChildPrioritize priorityNodes preferred fallback) = true := by
  unfold childWellFormedBool
  apply List.all_eq_true.mpr
  intro parent _member
  cases priority : priorityNodes parent with
  | true =>
      cases preferredEq : preferred parent with
      | some child =>
          have edgeData := childWellFormed_edge priorityNodes preferred
            preferredWellFormed preferredEq
          simp [forestChildPrioritize, priority, preferredEq, NodeSet.union,
            edgeData.2.1, edgeData.2.2]
      | none =>
          simp [forestChildPrioritize, priority, preferredEq,
            NodeSet.union]
  | false =>
      cases fallbackEq : fallback parent with
      | some child =>
          have edgeData := childWellFormed_edge fallbackNodes fallback
            fallbackWellFormed fallbackEq
          simp [forestChildPrioritize, priority, fallbackEq, NodeSet.union,
            edgeData.1, edgeData.2.1, edgeData.2.2]
      | none =>
          simp only [forestChildPrioritize, priority, fallbackEq]
          cases NodeSet.union priorityNodes fallbackNodes parent <;> rfl

/-- Nodes participating in either the large c-forest or an outcome readout
route. -/
def HedgeWitness.largeOutcomeFlowNodes
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : NodeSet S :=
  NodeSet.union w.rootReadoutNodes w.large

/-- Follow large c-forest edges until a canonical readout route is reached,
then give that action-free route priority all the way to an outcome. -/
def HedgeWitness.largeOutcomeFlowSuccessor
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : ForestChild S :=
  forestChildPrioritize w.rootReadoutNodes w.rootReadoutSuccessor w.child

/-- The composed large-forest/outcome successor is well formed on its union
node set. -/
theorem HedgeWitness.largeOutcomeFlowSuccessor_wellFormed
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    childWellFormedBool w.largeOutcomeFlowNodes
      w.largeOutcomeFlowSuccessor = true :=
  childWellFormedBool_forestChildPrioritize w.rootReadoutNodes w.large
    w.rootReadoutSuccessor w.child w.rootReadoutSuccessor_wellFormed
    w.large_forest.wellFormedBool

/-- Every sink of the composed large flow is a query outcome.  A sink inside
the large forest is a declared common root; otherwise it was already a sink
of the canonical readout routing forest. -/
theorem HedgeWitness.largeOutcomeFlowSinks_subset_outcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    NodeSet.Subset
      (keptSinks w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor)
      q.outcome := by
  intro node sink
  have sinkData :=
    (keptSinks_iff w.largeOutcomeFlowNodes
      w.largeOutcomeFlowSuccessor node).mp sink
  cases inReadout : w.rootReadoutNodes node with
  | true =>
      exact w.rootReadoutSuccessor_none_is_outcome node
        inReadout (by
          simpa [HedgeWitness.largeOutcomeFlowSuccessor,
            forestChildPrioritize, inReadout] using sinkData.2)
  | false =>
      have inLarge : w.large node = true := by
        simpa [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union, inReadout]
          using sinkData.1
      have childNone : w.child node = none := by
        simpa [HedgeWitness.largeOutcomeFlowSuccessor,
          forestChildPrioritize, inReadout] using sinkData.2
      have inRoot := (w.large_forest.roots_exact node).mpr
        ⟨inLarge, childNone⟩
      have rootInReadout := w.root_in_rootReadoutNodes node inRoot
      rw [inReadout] at rootInReadout
      contradiction

/-- If a composed large-flow edge enters a vertex outside the canonical
readout, then its parent is outside the readout as well.  Readout priority is
the essential point: a parent already on a route can only point to another
route vertex. -/
theorem HedgeWitness.largeOutcomeFlowSuccessor_parent_not_readout
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) {parent child : Fin S.count}
    (childNotReadout : w.rootReadoutNodes child = false)
    (found : w.largeOutcomeFlowSuccessor parent = some child) :
    w.rootReadoutNodes parent = false := by
  cases parentReadout : w.rootReadoutNodes parent with
  | false => rfl
  | true =>
      have routeFound : w.rootReadoutSuccessor parent = some child := by
        simpa [HedgeWitness.largeOutcomeFlowSuccessor,
          forestChildPrioritize, parentReadout] using found
      have childReadout := (w.rootReadoutSuccessor_nodes routeFound).2
      rw [childNotReadout] at childReadout
      contradiction

/-- Nodes participating in either the action-avoiding small c-forest or an
outcome readout route. -/
def HedgeWitness.smallOutcomeFlowNodes
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : NodeSet S :=
  NodeSet.union w.rootReadoutNodes w.small

/-- Follow small-forest kept edges until a canonical readout route is reached,
then give the action-free route priority. -/
def HedgeWitness.smallOutcomeFlowSuccessor
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : ForestChild S :=
  forestChildPrioritize w.rootReadoutNodes w.rootReadoutSuccessor
    (restrictChild w.small w.child)

/-- The composed small-forest/outcome successor is well formed on its union
node set. -/
theorem HedgeWitness.smallOutcomeFlowSuccessor_wellFormed
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    childWellFormedBool w.smallOutcomeFlowNodes
      w.smallOutcomeFlowSuccessor = true :=
  childWellFormedBool_forestChildPrioritize w.rootReadoutNodes w.small
    w.rootReadoutSuccessor (restrictChild w.small w.child)
    w.rootReadoutSuccessor_wellFormed w.small_forest.wellFormedBool

/-- Every sink of the composed small flow is likewise a query outcome. -/
theorem HedgeWitness.smallOutcomeFlowSinks_subset_outcome
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    NodeSet.Subset
      (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor)
      q.outcome := by
  intro node sink
  have sinkData :=
    (keptSinks_iff w.smallOutcomeFlowNodes
      w.smallOutcomeFlowSuccessor node).mp sink
  cases inReadout : w.rootReadoutNodes node with
  | true =>
      exact w.rootReadoutSuccessor_none_is_outcome node
        inReadout (by
          simpa [HedgeWitness.smallOutcomeFlowSuccessor,
            forestChildPrioritize, inReadout] using sinkData.2)
  | false =>
      have inSmall : w.small node = true := by
        simpa [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union, inReadout]
          using sinkData.1
      have childNone : restrictChild w.small w.child node = none := by
        simpa [HedgeWitness.smallOutcomeFlowSuccessor,
          forestChildPrioritize, inReadout] using sinkData.2
      have inRoot := (w.small_forest.roots_exact node).mpr
        ⟨inSmall, childNone⟩
      have rootInReadout := w.root_in_rootReadoutNodes node inRoot
      rw [inReadout] at rootInReadout
      contradiction

/-- The composed large flow has exactly the canonical readout sinks.  The
forward direction rules out a non-readout sink using the c-forest's exact
root set; the reverse direction is immediate from readout priority. -/
theorem HedgeWitness.largeOutcomeFlowSinks_eq_rootReadoutSinks
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    keptSinks w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor =
      keptSinks w.rootReadoutNodes w.rootReadoutSuccessor := by
  funext node
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro combinedSink
    have combined :=
      (keptSinks_iff w.largeOutcomeFlowNodes
        w.largeOutcomeFlowSuccessor node).mp combinedSink
    have inReadout : w.rootReadoutNodes node = true := by
      cases readout : w.rootReadoutNodes node with
      | true => rfl
      | false =>
          have inLarge : w.large node = true := by
            simpa [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
              readout] using combined.1
          have childNone : w.child node = none := by
            simpa [HedgeWitness.largeOutcomeFlowSuccessor,
              forestChildPrioritize, readout] using combined.2
          have inRoot := (w.large_forest.roots_exact node).mpr
            ⟨inLarge, childNone⟩
          have rootInReadout := w.root_in_rootReadoutNodes node inRoot
          rw [readout] at rootInReadout
          contradiction
    have routeNone : w.rootReadoutSuccessor node = none := by
      simpa [HedgeWitness.largeOutcomeFlowSuccessor,
        forestChildPrioritize, inReadout] using combined.2
    exact (keptSinks_iff w.rootReadoutNodes
      w.rootReadoutSuccessor node).mpr ⟨inReadout, routeNone⟩
  · intro routeSink
    have route :=
      (keptSinks_iff w.rootReadoutNodes
        w.rootReadoutSuccessor node).mp routeSink
    have combinedNode : w.largeOutcomeFlowNodes node = true := by
      simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union, route.1]
    have combinedNone : w.largeOutcomeFlowSuccessor node = none := by
      simp [HedgeWitness.largeOutcomeFlowSuccessor,
        forestChildPrioritize, route.1, route.2]
    exact (keptSinks_iff w.largeOutcomeFlowNodes
      w.largeOutcomeFlowSuccessor node).mpr ⟨combinedNode, combinedNone⟩

/-- The composed small flow has the same canonical sink set.  Consequently
the large and small sink-parity theorems concern one common outcome event,
not merely two events that happen to lie inside the query outcome. -/
theorem HedgeWitness.smallOutcomeFlowSinks_eq_rootReadoutSinks
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor =
      keptSinks w.rootReadoutNodes w.rootReadoutSuccessor := by
  funext node
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro combinedSink
    have combined :=
      (keptSinks_iff w.smallOutcomeFlowNodes
        w.smallOutcomeFlowSuccessor node).mp combinedSink
    have inReadout : w.rootReadoutNodes node = true := by
      cases readout : w.rootReadoutNodes node with
      | true => rfl
      | false =>
          have inSmall : w.small node = true := by
            simpa [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
              readout] using combined.1
          have childNone : restrictChild w.small w.child node = none := by
            simpa [HedgeWitness.smallOutcomeFlowSuccessor,
              forestChildPrioritize, readout] using combined.2
          have inRoot := (w.small_forest.roots_exact node).mpr
            ⟨inSmall, childNone⟩
          have rootInReadout := w.root_in_rootReadoutNodes node inRoot
          rw [readout] at rootInReadout
          contradiction
    have routeNone : w.rootReadoutSuccessor node = none := by
      simpa [HedgeWitness.smallOutcomeFlowSuccessor,
        forestChildPrioritize, inReadout] using combined.2
    exact (keptSinks_iff w.rootReadoutNodes
      w.rootReadoutSuccessor node).mpr ⟨inReadout, routeNone⟩
  · intro routeSink
    have route :=
      (keptSinks_iff w.rootReadoutNodes
        w.rootReadoutSuccessor node).mp routeSink
    have combinedNode : w.smallOutcomeFlowNodes node = true := by
      simp [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union, route.1]
    have combinedNone : w.smallOutcomeFlowSuccessor node = none := by
      simp [HedgeWitness.smallOutcomeFlowSuccessor,
        forestChildPrioritize, route.1, route.2]
    exact (keptSinks_iff w.smallOutcomeFlowNodes
      w.smallOutcomeFlowSuccessor node).mpr ⟨combinedNode, combinedNone⟩

/-- Canonical action-root-to-outcome route carried by the hedge witness. -/
def HedgeWitness.parityReadoutRoute
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : List (Fin S.count) :=
  mutilatedDirectedRoute q.action w.parityReadoutOutcome S.count
    w.actionRoot w.actionRoot_reaches_parityReadoutOutcome

/-- The readout route starts at the action branch's common forest root. -/
theorem HedgeWitness.parityReadoutRoute_starts
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.parityReadoutRoute.head? = some w.actionRoot := by
  simpa [HedgeWitness.parityReadoutRoute] using
    (mutilatedDirectedRoute_spec q.action w.parityReadoutOutcome S.count
      w.actionRoot w.actionRoot_reaches_parityReadoutOutcome).1

/-- The readout route ends at the selected query outcome. -/
theorem HedgeWitness.parityReadoutRoute_finishes
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.parityReadoutRoute.getLast? = some w.parityReadoutOutcome := by
  simpa [HedgeWitness.parityReadoutRoute] using
    (mutilatedDirectedRoute_spec q.action w.parityReadoutOutcome S.count
      w.actionRoot w.actionRoot_reaches_parityReadoutOutcome).2.1

/-- Every consecutive readout pair is an edge of `G_{bar X}`. -/
theorem HedgeWitness.parityReadoutRoute_consecutive
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    PathSpecification.Consecutive
      (fun parent child =>
        mutilatedDirected S q.action parent child = true)
      w.parityReadoutRoute := by
  simpa [HedgeWitness.parityReadoutRoute] using
    (mutilatedDirectedRoute_spec q.action w.parityReadoutOutcome S.count
      w.actionRoot w.actionRoot_reaches_parityReadoutOutcome).2.2

/-- Strict topological increase prevents repeated vertices on the canonical
readout route. -/
theorem HedgeWitness.parityReadoutRoute_nodup
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.parityReadoutRoute.Nodup := by
  apply PathSpecification.Consecutive.nodup_of_fin_lt
    w.parityReadoutRoute
  exact w.parityReadoutRoute_consecutive.mono
    (fun parent child edge => mutilatedDirected_earlier S q.action edge)

/-- No vertex on the canonical readout route is intervened upon. -/
theorem HedgeWitness.parityReadoutRoute_avoids_action
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    ∀ node, node ∈ w.parityReadoutRoute → q.action node = false := by
  have rootFree := w.small_avoids_intervention w.actionRoot
    w.actionRoot_in_small
  exact consecutive_mutilatedDirected_avoids_action q.action
    w.parityReadoutRoute w.actionRoot w.parityReadoutRoute_starts rootFree
    w.parityReadoutRoute_consecutive

/-- Deterministic parent lookup along the canonical parity-readout route. -/
def HedgeWitness.parityReadoutParent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (child : Fin S.count) : Option (Fin S.count) :=
  routePredecessor w.parityReadoutRoute child

/-- Every consecutive pair of the canonical route is recorded by its global
parent lookup. -/
theorem HedgeWitness.parityReadoutParent_consecutive
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    PathSpecification.Consecutive
      (fun parent child => w.parityReadoutParent child = some parent)
      w.parityReadoutRoute := by
  simpa [HedgeWitness.parityReadoutParent] using
    routePredecessor_consecutive w.parityReadoutRoute
      w.parityReadoutRoute_nodup

/-- The action-side forest root is the first readout vertex and therefore has
no readout parent. -/
theorem HedgeWitness.parityReadoutParent_actionRoot
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.parityReadoutParent w.actionRoot = none := by
  exact routePredecessor_head_eq_none w.parityReadoutRoute w.actionRoot
    w.parityReadoutRoute_starts w.parityReadoutRoute_nodup

/-- Every parent returned by the canonical lookup is the corresponding edge
of the action-mutilated graph. -/
theorem HedgeWitness.parityReadoutParent_mutilatedDirected
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) {parent child : Fin S.count}
    (found : w.parityReadoutParent child = some parent) :
    mutilatedDirected S q.action parent child = true := by
  apply routePredecessor_rel_of_eq_some
    (fun left right => mutilatedDirected S q.action left right = true)
    w.parityReadoutRoute parent child w.parityReadoutRoute_consecutive
  simpa [HedgeWitness.parityReadoutParent] using found

/-- In particular, a returned readout parent is a genuine directed parent in
the original observed signature. -/
theorem HedgeWitness.parityReadoutParent_directed
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) {parent child : Fin S.count}
    (found : w.parityReadoutParent child = some parent) :
    S.directed parent child = true := by
  have edge := w.parityReadoutParent_mutilatedDirected found
  unfold mutilatedDirected at edge
  split at edge
  · contradiction
  · exact edge

/-- Unpack the Boolean hedge tests into the `HedgeWitness` fields. -/
def hedgeWitness_of_sets
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (sel : HedgeSelection S)
    (h : hedgeTestsHold G q sel = true) :
    HedgeWitness G q :=
  let hABC := Bool.and_eq_true_iff.mp h
  let hAB := Bool.and_eq_true_iff.mp hABC.1
  let hverts := hAB.1
  let hchildReady := hAB.2
  let hsmall := hABC.2
  let hverts_b := Bool.and_eq_true_iff.mp hverts
  let hverts_a := Bool.and_eq_true_iff.mp hverts_b.1
  let hsingleL := hverts_a.2
  let hmeets := hverts_b.2
  let hwell := (Bool.and_eq_true_iff.mp hchildReady).1
  let hreach := (Bool.and_eq_true_iff.mp hchildReady).2
  let small_e := Bool.and_eq_true_iff.mp hsmall
  let small_d := Bool.and_eq_true_iff.mp small_e.1
  let small_c := Bool.and_eq_true_iff.mp small_d.1
  let small_b := Bool.and_eq_true_iff.mp small_c.1
  let small_a := Bool.and_eq_true_iff.mp small_b.1
  let hsingleS := small_a.2
  let hsubset := small_b.2
  let havoids := small_c.2
  let hclosed := small_d.2
  let hrootsIn := small_e.2
  let large := sel.large
  let small := sel.small
  let child := sel.child
  let hsubP := (NodeSet.subsetBool_eq_true_iff small large).mp hsubset
  let hwellS := childWellFormed_restrict large small child hwell hsubP hclosed
  let sameRoots :
      keptSinks small (restrictChild small child) =
        keptSinks large child :=
    keptSinks_restrict_eq large small child hsubP hclosed
      ((NodeSet.subsetBool_eq_true_iff (keptSinks large child) small).mp
        hrootsIn)
  let actionSeed := NodeSet.getMeeting large q.action hmeets
  let hstart := NodeSet.getMeeting_left hmeets
  let sink := forestSink large child hwell actionSeed hstart
  let hroot : keptSinks large child sink = true :=
    forestSink_kept large child hwell actionSeed hstart
  let rootMem : sink ∈ NodeSet.members (keptSinks large child) :=
    (NodeSet.mem_members_iff (keptSinks large child) sink).mpr hroot
  let anyY :
      (NodeSet.members q.outcome).any (fun y =>
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (mutilatedDirected S q.action) S.count sink y) = true :=
    (List.all_eq_true.mp hreach) sink rootMem
  let outcomeSeed :=
    listFirstAny (NodeSet.members q.outcome)
      (fun y =>
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (mutilatedDirected S q.action) S.count sink y)
      anyY
  {
    large := large
    small := small
    roots := keptSinks large child
    child := child
    large_forest := cForest_of_child G large child hsingleL hwell
    small_forest := by
      have F := cForest_of_child G small (restrictChild small child)
        hsingleS hwellS
      exact sameRoots ▸ F
    small_subset_large := hsubP
    large_meets_intervention :=
      (NodeSet.meetsBool_eq_true_iff large q.action).mp hmeets
    small_avoids_intervention :=
      (NodeSet.disjointBool_eq_true_iff small q.action).mp havoids
    roots_reach_outcome :=
      rootsReachOutcome_of_bool q (keptSinks large child) hreach
    actionSeed := actionSeed
    actionSeed_in_large := hstart
    actionSeed_in_action := NodeSet.getMeeting_right hmeets
    outcomeSeed := outcomeSeed
    outcomeSeed_in_outcome :=
      (NodeSet.mem_members_iff q.outcome outcomeSeed).mp
        (listFirstAny_mem (NodeSet.members q.outcome)
          (fun y =>
            FiniteReachability.within finBeq (NodeSet.enumerated S)
              (mutilatedDirected S q.action) S.count sink y)
          anyY)
  }

/--
Executable extraction of a hedge from ID-failure data by finite search over
vertex selections and kept directed children.  Greedy thinning remains
available as lemmas; it is not the extractor.  Returning `none` means no
enumerated selection passed the Boolean tests — search completeness, not
an absence of hedges in the abstract.
-/
def hedgeWitness? (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) : Option (HedgeWitness G q) :=
  match hfound : findHedgeWitnessSets G q fail with
  | none => none
  | some sel =>
      some (hedgeWitness_of_sets G q sel
        (findHedgeWitnessSets_tests G q fail hfound))

/--
The extractor returns a witness exactly when the finite search returns a
selection.  Named-pattern matching in `hedgeWitness?` is definitionally
`Option.map` of that search, so `isSome` is preserved.
-/
theorem hedgeWitness?_isSome_iff_sets
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) :
    (hedgeWitness? G q fail).isSome =
      (findHedgeWitnessSets G q fail).isSome := by
  dsimp [hedgeWitness?]
  split
  · next heq =>
      change false = (findHedgeWitnessSets G q fail).isSome
      rw [heq]
      rfl
  · next _sel heq =>
      change true = (findHedgeWitnessSets G q fail).isSome
      rw [heq]
      rfl

/--
The extractor inhabits a `HedgeWitness` as soon as any enumerated
selection inside `fail.remaining` passes the Boolean tests.  Combined
with search completeness, the remaining ID-failure leaf is to exhibit
such a selection.
-/
theorem hedgeWitness?_eq_some_of_selection
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) (sel : HedgeSelection S)
    (hlarge : NodeSet.Subset sel.large fail.remaining)
    (htests : hedgeTestsHold G q sel = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  rcases findHedgeWitnessSets_eq_some_of_selection G q fail sel hlarge
      htests with ⟨found, hf⟩
  have hsome : (hedgeWitness? G q fail).isSome = true := by
    rw [hedgeWitness?_isSome_iff_sets, hf]
    rfl
  match h : hedgeWitness? G q fail with
  | none =>
      simp [h] at hsome
  | some witness =>
      exact ⟨witness, rfl⟩

theorem hedgeWitness?_eq_some_of_thinned
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S)
    (htests :
      hedgeTestsHold G q (thinnedHedgeSelection G q fail) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_selection G q fail
    (thinnedHedgeSelection G q fail)
    (thinnedHedgeSelection_subset_remaining G q fail) htests

theorem hedgeWitness?_eq_some_of_failed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S)
    (htests : hedgeTestsHold G q (failedHedgeSelection fail) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_selection G q fail
    (failedHedgeSelection fail)
    (failedHedgeSelection_subset_remaining fail) htests

/--
Top-level ID failure with a remaining-local original action yields a
`HedgeWitness` by search completeness.
-/
theorem hedgeWitness?_eq_some_of_failed_local_action
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed G q fail
    (failedHedgeSelection_tests_of_local_action G q hfail hfree hanc)

/--
When the failing site's local outcome and action agree with the original
query on the recorded remaining vertices, the local-action hedge tests
apply to `q` itself.  Product-nested sites typically fail this agreement;
shrink and 4.3 restriction keep it.
-/
theorem failedHedgeSelection_tests_of_site_agrees
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (localOutcome localAction : NodeSet S)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter localAction fail.remaining)) = true)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter localOutcome fail.remaining))
        fail.remaining = true)
    (hYeq :
      NodeSet.equal
        (NodeSet.inter localOutcome fail.remaining)
        (NodeSet.inter q.outcome fail.remaining) = true)
    (hXeq :
      NodeSet.equal
        (NodeSet.inter localAction fail.remaining)
        (NodeSet.inter q.action fail.remaining) = true) :
    hedgeTestsHold G q (failedHedgeSelection fail) = true := by
  have hX :
      NodeSet.inter localAction fail.remaining =
        NodeSet.inter q.action fail.remaining :=
    (NodeSet.equal_eq_true_iff _ _).mp hXeq
  have hY :
      NodeSet.inter localOutcome fail.remaining =
        NodeSet.inter q.outcome fail.remaining :=
    (NodeSet.equal_eq_true_iff _ _).mp hYeq
  have hfreeQ :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true := by
    simpa [hX] using hfree
  have hancQ :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true := by
    simpa [hY] using hanc
  exact failedHedgeSelection_tests_of_local_action G q hfail hfreeQ hancQ

theorem hedgeWitness?_eq_some_of_failed_site_agrees
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (localOutcome localAction : NodeSet S)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter localAction fail.remaining)) = true)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter localOutcome fail.remaining))
        fail.remaining = true)
    (hYeq :
      NodeSet.equal
        (NodeSet.inter localOutcome fail.remaining)
        (NodeSet.inter q.outcome fail.remaining) = true)
    (hXeq :
      NodeSet.equal
        (NodeSet.inter localAction fail.remaining)
        (NodeSet.inter q.action fail.remaining) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed G q fail
    (failedHedgeSelection_tests_of_site_agrees G q hfail localOutcome
      localAction hfree hanc hYeq hXeq)

/--
A product-free structural failure trace yields a hedge for the original
top-level query, regardless of how many ancestral-shrink and 4.3-restriction
frames precede its terminal 4.1 failure.

The trace induction in `IdentificationInduction` proves that those two frame
kinds preserve the outcome and action after restriction to `fail.remaining`.
The terminal site's generic 4.1 facts can therefore be transported directly
to `q` and discharged by the common hedge-search theorem above.  Product
frames are excluded explicitly: they replace the local query by a factor and
require the separate free-component ancestry argument developed below.
-/
theorem hedgeWitness?_eq_some_of_productFree_failureTrace
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (trace : JointIdentificationFailureTrace G q fail)
    (productFree : trace.hasNoProductFrame = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness := by
  have hfail :
      Legacy.identifyJoint G q = IdentificationOutcome.failed fail := by
    simpa [Legacy.identifyJoint, JointIdentificationFailureTrace] using
      trace.eq_failed
  let site : IdentificationImmediateFailureSite G fail := trace.immediateSite
  have localFacts := site.local_query_site
  have queryAgreement :=
    trace.immediateSite_query_agrees_of_hasNoProductFrame productFree
  exact hedgeWitness?_eq_some_of_failed_site_agrees G q hfail site.outcome
    site.action localFacts.1 localFacts.2 queryAgreement.1 queryAgreement.2

/--
Hedge tests for the original query when the failure-record forest points
at the recorded free component (the nested 4.1 target) rather than at
`Y` itself.  The remaining set still has to meet `X`, the free side has
to avoid `X`, and vertices of the remaining set still have to reach `Y`
in `G_{\overline{X}}`.  Product-nested 4.1 fails inhabit the free-side
ancestry from `identifyJoint_eq_failed_site` once the local outcome is
that free component.
-/
theorem failedHedgeSelection_tests_of_free_ancestral
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    hedgeTestsHold G q (failedHedgeSelection fail) = true :=
  failedHedgeSelection_tests_of G q hfail hmeets
    (failedHedgeSelection_rootsReach_of_ancestral G q hfail hancY)
    (failedHedgeSelection_smallForestReady_of G q hfail hdisj
      (failedHedgeSelection_keptSinks_of_free_ancestral G q hfail
        hancFree))

theorem hedgeWitness?_eq_some_of_failed_free_ancestral
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (hmeets :
      NodeSet.meetsBool (failedHedgeSelection fail).large q.action = true)
    (hdisj :
      NodeSet.disjointBool (failedHedgeSelection fail).small q.action =
        true)
    (hancFree :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true)
    (hancY :
      NodeSet.equal
        (G.ancestralSet fail.remaining (GraphMutilation.bar q.action)
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed G q fail
    (failedHedgeSelection_tests_of_free_ancestral G q hfail hmeets hdisj
      hancFree hancY)

/--
When the failing site's local outcome is the recorded free component,
site ancestry is free-component ancestry.
-/
theorem failedHedgeSelection_free_ancestral_of_site
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (_hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (localOutcome _localAction : NodeSet S)
    (_hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter _localAction fail.remaining)) = true)
    (hanc :
      NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter localOutcome fail.remaining))
        fail.remaining = true)
    (hEq :
      NodeSet.equal (NodeSet.inter localOutcome fail.remaining)
        (NodeSet.inter fail.free fail.remaining) = true) :
    NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter fail.free fail.remaining))
        fail.remaining = true := by
  have heq :
      NodeSet.inter localOutcome fail.remaining =
        NodeSet.inter fail.free fail.remaining :=
    (NodeSet.equal_eq_true_iff _ _).mp hEq
  simpa [heq] using hanc

/--
Top-level ID failure whose recorded remaining set is still the full
graph, with free side `V \ X`, is ancestral of `Y` in `G_{\overline{X}}`.
-/
theorem identifyJoint_eq_failed_query_of_full
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining NodeSet.full = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true) :
    NodeSet.equal
        (G.ancestralSet fail.remaining
          (GraphMutilation.bar
            (NodeSet.diff fail.remaining fail.free))
          (NodeSet.inter q.outcome fail.remaining))
        fail.remaining = true :=
  identifyFuel_eq_failed_query_of_remaining_eq (identificationFuel S) G
    NodeSet.full q.outcome q.action (observationalJointTerm S) hfail heq
    hfree

theorem hedgeWitness?_eq_some_of_failed_remaining_eq
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    (heq : NodeSet.equal fail.remaining NodeSet.full = true)
    (hfree :
      NodeSet.equal fail.free
        (NodeSet.diff fail.remaining
          (NodeSet.inter q.action fail.remaining)) = true) :
    Exists fun witness => hedgeWitness? G q fail = some witness :=
  hedgeWitness?_eq_some_of_failed_local_action G q hfail hfree
    (identifyJoint_eq_failed_query_of_full G q hfail heq hfree)


end Causality
end Thesis
