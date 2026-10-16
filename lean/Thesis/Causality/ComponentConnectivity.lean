import Thesis.Causality.IdentificationSearch

namespace Thesis
namespace Causality

open Probability

/-!
# Executable c-components and inductive bidirected connectivity

These are graph-only facts shared by the current identification engine and
the historical completeness development. The finite search agrees with
inductive connectivity; components are connected in their own host, partition
their host, and embed in containing components under host inclusion.

Keeping these proofs below the causal transport layer lets structural
progress and separation clients import them without importing countermodel
constructions or legacy recursion proofs. Public theorem names and statements
are retained. In particular, the historically named missing-host impossibility
lemma has a graph-only type: it takes no unfinished trace or semantic premise.

The forest constructors and historical trace inductions stay in Completeness;
this module imports only the intrinsic finite search and its existing proofs.
-/

/-! ## Executable c-components agree with inductive bidirected connectivity -/

namespace FiniteReachability

/-- Append one Boolean edge at the end of an exact walk. -/
def exactWalk_snoc {edge : α -> α -> Bool}
    {length : Nat} {source middle target : α}
    (walk : ExactWalk edge length source middle)
    (last : edge middle target = true) :
    ExactWalk edge (length + 1) source target :=
  match walk with
  | .refl _node => .step last (.refl target)
  | .step first rest => .step first (exactWalk_snoc rest last)

/-- A walk on a stronger edge relation is a walk on a weaker one. -/
def exactWalk_mono {e1 e2 : α -> α -> Bool}
    (hle : forall i j, e1 i j = true -> e2 i j = true)
    {length : Nat} {source target : α}
    (walk : ExactWalk e1 length source target) :
    ExactWalk e2 length source target :=
  match walk with
  | .refl node => .refl node
  | .step first rest => .step (hle _ _ first) (exactWalk_mono hle rest)

end FiniteReachability

/-- One inductive tail step is a Boolean gated bidirected edge. -/
theorem bidirectedEdgeWithin_of_step
    {G : ObservedGraph S} {nodes : NodeSet S} {i j k : Fin S.count}
    (prev : BidirectedConnectedWithin G nodes i j)
    (selected : nodes k = true)
    (edge : G.bidirected j k = true) :
    (nodes j && nodes k && G.bidirected j k) = true :=
  Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr
      ⟨BidirectedConnectedWithin.mem_right prev, selected⟩, edge⟩

/-- Bidirected connectivity produces some finite exact walk on the gated edges. -/
theorem exists_exactWalk_of_bidirectedConnected
    {G : ObservedGraph S} {nodes : NodeSet S} {source target : Fin S.count}
    (connected : BidirectedConnectedWithin G nodes source target) :
    Exists fun length =>
      Nonempty
        (FiniteReachability.ExactWalk
          (fun i j => nodes i && nodes j && G.bidirected i j)
          length source target) := by
  induction connected with
  | refl _selected => exact ⟨0, ⟨.refl source⟩⟩
  | tail prev selected edge ih =>
      rcases ih with ⟨length, ⟨walk⟩⟩
      exact ⟨length + 1,
        ⟨FiniteReachability.exactWalk_snoc walk
          (bidirectedEdgeWithin_of_step prev selected edge)⟩⟩

/-- An exact walk on gated bidirected edges is an inductive connection. -/
theorem bidirectedConnected_of_exactWalk
    {G : ObservedGraph S} {nodes : NodeSet S}
    {length : Nat} {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk
      (fun i j => nodes i && nodes j && G.bidirected i j)
      length source target)
    (hsrc : nodes source = true) :
    BidirectedConnectedWithin G nodes source target :=
  match walk with
  | .refl _node => .refl hsrc
  | .step first rest =>
      let joined := Bool.and_eq_true_iff.mp first
      let both := Bool.and_eq_true_iff.mp joined.1
      BidirectedConnectedWithin.trans
        (.tail (.refl hsrc) both.2 joined.2)
        (bidirectedConnected_of_exactWalk rest both.2)

/-- Gated bidirected edge used by the executable c-component search. -/
def bidirectedEdgeWithin (G : ObservedGraph S) (nodes : NodeSet S)
    (i j : Fin S.count) : Bool :=
  nodes i && nodes j && G.bidirected i j

theorem bidirectedReachableWithin_eq_true_iff
    (G : ObservedGraph S) (nodes : NodeSet S)
    {source target : Fin S.count}
    (hsrc : nodes source = true) (htgt : nodes target = true) :
    G.bidirectedReachableWithin nodes source target = true <->
      BidirectedConnectedWithin G nodes source target := by
  have complete : forall node, node ∈ NodeSet.enumerated S :=
    NodeSet.mem_enumerated S
  have same_iff := finBeq_eq_true_iff (n := S.count)
  constructor
  · intro reached
    have withinTrue :
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (bidirectedEdgeWithin G nodes) S.count source target = true := by
      simpa [ObservedGraph.bidirectedReachableWithin, bidirectedEdgeWithin,
        hsrc, htgt] using reached
    have bounded :
        FiniteReachability.BoundedWalk (bidirectedEdgeWithin G nodes)
          S.count source target :=
      (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
        (NodeSet.enumerated S) (bidirectedEdgeWithin G nodes) same_iff
        complete S.count source target).mp withinTrue
    rcases bounded with ⟨_length, _bound, ⟨walk⟩⟩
    exact bidirectedConnected_of_exactWalk walk hsrc
  · intro connected
    rcases exists_exactWalk_of_bidirectedConnected connected with
      ⟨_length, walk⟩
    have reachable :
        FiniteReachability.Reachable (bidirectedEdgeWithin G nodes)
          source target :=
      ⟨_length, walk⟩
    have bounded :
        FiniteReachability.BoundedWalk (bidirectedEdgeWithin G nodes)
          (NodeSet.enumerated S).length source target :=
      FiniteReachability.boundedWalk_of_reachable finBeq
        (NodeSet.enumerated S) (bidirectedEdgeWithin G nodes) same_iff
        complete reachable
    have boundedCount :
        FiniteReachability.BoundedWalk (bidirectedEdgeWithin G nodes)
          S.count source target := by
      simpa [NodeSet.length_enumerated] using bounded
    have withinTrue :
        FiniteReachability.within finBeq (NodeSet.enumerated S)
          (bidirectedEdgeWithin G nodes) S.count source target = true :=
      (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
        (NodeSet.enumerated S) (bidirectedEdgeWithin G nodes) same_iff
        complete S.count source target).mpr boundedCount
    simpa [ObservedGraph.bidirectedReachableWithin, bidirectedEdgeWithin,
      hsrc, htgt] using withinTrue

theorem bidirectedReachableWithin_refl
    (G : ObservedGraph S) (nodes : NodeSet S) {source : Fin S.count}
    (hsrc : nodes source = true) :
    G.bidirectedReachableWithin nodes source source = true :=
  (bidirectedReachableWithin_eq_true_iff G nodes hsrc hsrc).mpr
    (.refl hsrc)

/-- Membership in the executable c-component is inductive bidirected reachability. -/
theorem cComponentOf_eq_true_iff
    (G : ObservedGraph S) (nodes : NodeSet S) {root i : Fin S.count}
    (hroot : nodes root = true) :
    G.cComponentOf nodes root i = true <->
      BidirectedConnectedWithin G nodes root i := by
  constructor
  · intro member
    have hi : nodes i = true := by
      have reached : G.bidirectedReachableWithin nodes root i = true := by
        simpa [ObservedGraph.cComponentOf] using member
      have outer :
          (nodes root && nodes i) = true ∧
            FiniteReachability.within finBeq (NodeSet.enumerated S)
              (fun a b => nodes a && nodes b && G.bidirected a b)
              S.count root i = true :=
        Bool.and_eq_true_iff.mp (by
          simpa [ObservedGraph.bidirectedReachableWithin] using reached)
      exact (Bool.and_eq_true_iff.mp outer.1).2
    exact (bidirectedReachableWithin_eq_true_iff G nodes hroot hi).mp
      (by simpa [ObservedGraph.cComponentOf] using member)
  · intro connected
    have hi := BidirectedConnectedWithin.mem_right connected
    simpa [ObservedGraph.cComponentOf] using
      (bidirectedReachableWithin_eq_true_iff G nodes hroot hi).mpr connected

/--
A bidirected walk that starts in a c-component stays inside it: every later
vertex is still bidirected-reachable from the component root.
-/
theorem bidirectedConnected_within_cComponent
    (G : ObservedGraph S) (nodes : NodeSet S) {root i j : Fin S.count}
    (hroot : nodes root = true)
    (walk : BidirectedConnectedWithin G nodes i j)
    (hi : G.cComponentOf nodes root i = true) :
    BidirectedConnectedWithin G (G.cComponentOf nodes root) i j := by
  induction walk with
  | refl _selected => exact .refl hi
  | tail prev selected edge ih =>
      refine .tail ih ?hk edge
      exact (cComponentOf_eq_true_iff G nodes hroot).mpr
        (BidirectedConnectedWithin.trans
          ((cComponentOf_eq_true_iff G nodes hroot).mp hi)
          (.tail prev selected edge))

/--
The executable c-component of a selected root is a bidirected component in
the sense of `BidirectedComponent`.
-/
theorem cComponentOf_is_component
    (G : ObservedGraph S) (nodes : NodeSet S) {root : Fin S.count}
    (hroot : nodes root = true) :
    BidirectedComponent G (G.cComponentOf nodes root) := by
  constructor
  · exact ⟨root, (cComponentOf_eq_true_iff G nodes hroot).mpr (.refl hroot)⟩
  · intro i j hi hj
    have hiConn : BidirectedConnectedWithin G nodes root i :=
      (cComponentOf_eq_true_iff G nodes hroot).mp hi
    have hjConn : BidirectedConnectedWithin G nodes root j :=
      (cComponentOf_eq_true_iff G nodes hroot).mp hj
    have ij : BidirectedConnectedWithin G nodes i j :=
      BidirectedConnectedWithin.trans (BidirectedConnectedWithin.symm hiConn)
        hjConn
    exact bidirectedConnected_within_cComponent G nodes hroot ij hi

/-- A connected host equals the executable c-component of any of its members. -/
theorem cComponentOf_eq_of_component
    (G : ObservedGraph S) (nodes : NodeSet S) {seed : Fin S.count}
    (hseed : nodes seed = true)
    (comp : BidirectedComponent G nodes) :
    G.cComponentOf nodes seed = nodes := by
  funext i
  cases hi : nodes i
  · cases hc : G.cComponentOf nodes seed i
    · rfl
    · have selected : nodes i = true := cComponentOf_subset G nodes hc
      exact False.elim (Bool.false_ne_true (hi.symm.trans selected))
  · exact (cComponentOf_eq_true_iff G nodes hseed).mpr
      (comp.2 seed i hseed hi)

theorem cComponentOf_idempotent
    (G : ObservedGraph S) (nodes : NodeSet S) {seed : Fin S.count}
    (hseed : nodes seed = true) :
    G.cComponentOf (G.cComponentOf nodes seed) seed =
      G.cComponentOf nodes seed :=
  cComponentOf_eq_of_component G (G.cComponentOf nodes seed)
    ((cComponentOf_eq_true_iff G nodes hseed).mpr (.refl hseed))
    (cComponentOf_is_component G nodes hseed)

/--
Every executable c-component of an induced subset is contained in some
executable c-component of the host.  Consequently, the ID engine's
`containingCComponent` search cannot return `none` for such a component.

The proof is constructive.  A root of the smaller component is also in the
host, whose computed c-component partition supplies a concrete larger piece.
Bidirected connectivity is monotone under the subset inclusion, so every
vertex of the smaller piece lies in that larger piece; the Boolean `find?`
therefore has a witnessed successful predicate.
-/
theorem containingCComponent_ne_none_of_mem_of_subset
    (G : ObservedGraph S) (smaller larger : NodeSet S)
    {component : NodeSet S}
    (componentMem : component ∈ G.cComponents smaller)
    (subset : NodeSet.Subset smaller larger) :
    G.containingCComponent larger component ≠ none := by
  rcases cComponents_mem G smaller componentMem with
    ⟨root, rootInSmaller, componentEq⟩
  have rootInLarger : larger root = true := subset root rootInSmaller
  rcases cComponents_covers G larger rootInLarger with
    ⟨hostComponent, hostComponentMem, rootInHostComponent⟩
  rcases cComponents_mem G larger hostComponentMem with
    ⟨hostRoot, hostRootInLarger, hostComponentEq⟩
  have componentSubset : NodeSet.Subset component hostComponent := by
    intro i iInComponent
    have rootToIInSmaller :
        BidirectedConnectedWithin G smaller root i :=
      (cComponentOf_eq_true_iff G smaller rootInSmaller).mp (by
        rw [← componentEq]
        exact iInComponent)
    have rootToIInLarger :
        BidirectedConnectedWithin G larger root i :=
      rootToIInSmaller.mono subset
    have hostRootToRoot :
        BidirectedConnectedWithin G larger hostRoot root :=
      (cComponentOf_eq_true_iff G larger hostRootInLarger).mp (by
        rw [← hostComponentEq]
        exact rootInHostComponent)
    have hostRootToI :
        BidirectedConnectedWithin G larger hostRoot i :=
      BidirectedConnectedWithin.trans hostRootToRoot rootToIInLarger
    have iInHostClass : G.cComponentOf larger hostRoot i = true :=
      (cComponentOf_eq_true_iff G larger hostRootInLarger).mpr hostRootToI
    rw [hostComponentEq]
    exact iInHostClass
  have predicateTrue :
      NodeSet.subsetBool component hostComponent = true :=
    (NodeSet.subsetBool_eq_true_iff component hostComponent).mpr
      componentSubset
  intro noContainingComponent
  have findNone :
      (G.cComponents larger).find? (fun candidate =>
        NodeSet.subsetBool component candidate) = none := by
    simpa [ObservedGraph.containingCComponent] using noContainingComponent
  exact (List.find?_eq_none.mp findNone hostComponent hostComponentMem)
    predicateTrue

/--
The unmatched-host terminal of an unfinished ID trace is unreachable: its
unique free component is listed inside `remaining \ action`, hence the host
containment theorem above supplies a containing c-component of `remaining`.
-/
theorem identificationUnfinished_missingHost_impossible
    (G : ObservedGraph S)
    (remaining action component : NodeSet S)
    (oneFreeComponent :
      G.cComponents
        (NodeSet.diff remaining (NodeSet.inter action remaining)) =
        [component])
    (noContainingComponent :
      G.containingCComponent remaining component = none) : False := by
  have componentMem :
      component ∈
        G.cComponents
          (NodeSet.diff remaining (NodeSet.inter action remaining)) := by
    simp [oneFreeComponent]
  exact containingCComponent_ne_none_of_mem_of_subset G
    (NodeSet.diff remaining (NodeSet.inter action remaining)) remaining
    componentMem (NodeSet.diff_subset_left _ _) noContainingComponent

/--
If a node set equals the c-component of one of its members, every other
member has the same c-component — the host is one bidirected piece.
-/
theorem cComponentOf_eq_of_self
    (G : ObservedGraph S) (nodes : NodeSet S) {seed root : Fin S.count}
    (hseed : nodes seed = true)
    (hEq : nodes = G.cComponentOf nodes seed)
    (hroot : nodes root = true) :
    G.cComponentOf nodes root = nodes :=
  cComponentOf_eq_of_component G nodes hroot
    (by
      rw [hEq]
      exact cComponentOf_is_component G nodes hseed)

/--
A connected host, once discovered, is the unique accumulated component.
The empty-accumulator scan of `pending` therefore returns `[nodes]` as
soon as any member of `nodes` appears in `pending`.
-/
theorem cComponentsCollect_eq_singleton
    (G : ObservedGraph S) (nodes : NodeSet S) {seed : Fin S.count}
    (hseed : nodes seed = true)
    (hEq : nodes = G.cComponentOf nodes seed)
    (pending : List (Fin S.count)) (acc : List (NodeSet S))
    (hacc : acc = [] ∨ acc = [nodes])
    (hpending : acc = [nodes] ∨ seed ∈ pending) :
    ObservedGraph.cComponentsCollect G nodes pending acc = [nodes] := by
  induction pending generalizing acc with
  | nil =>
      cases hacc with
      | inl hnil =>
          cases hpending with
          | inl hsing =>
              exact False.elim
                (List.cons_ne_nil _ _ (hsing.symm.trans hnil))
          | inr hmem =>
              cases hmem
      | inr hsing =>
          simp [ObservedGraph.cComponentsCollect, hsing]
  | cons root rest ih =>
      cases hacc with
      | inr hsing =>
          have covered :=
            cComponentsCollect_covered G nodes (root :: rest) [nodes]
              (by
                intro r hr
                simp [hr])
          simpa [hsing] using covered
      | inl hnil =>
          subst hnil
          cases hnode : nodes root with
          | false =>
              have hseedRest : seed ∈ rest := by
                cases hpending with
                | inl hsing =>
                    exact False.elim (List.cons_ne_nil _ _ hsing.symm)
                | inr hmem =>
                    rcases List.mem_cons.mp hmem with hEqRoot | hRest
                    · subst hEqRoot
                      exact False.elim (Bool.false_ne_true
                        (hnode.symm.trans hseed))
                    · exact hRest
              simpa [ObservedGraph.cComponentsCollect, hnode] using
                ih [] (Or.inl rfl) (Or.inr hseedRest)
          | true =>
              have hEqRoot : G.cComponentOf nodes root = nodes :=
                cComponentOf_eq_of_self G nodes hseed hEq hnode
              have hany :
                  ([] : List (NodeSet S)).any (fun c => c root) = false :=
                rfl
              simpa [ObservedGraph.cComponentsCollect, hnode, hany,
                hEqRoot] using
                ih [nodes] (Or.inr rfl) (Or.inl rfl)

theorem cComponents_eq_singleton
    (G : ObservedGraph S) (nodes : NodeSet S) {seed : Fin S.count}
    (hseed : nodes seed = true)
    (hEq : nodes = G.cComponentOf nodes seed) :
    G.cComponents nodes = [nodes] :=
  cComponentsCollect_eq_singleton G nodes hseed hEq
    (NodeSet.enumerated S) [] (Or.inl rfl)
    (Or.inr (NodeSet.mem_enumerated S seed))

/-- A listed component equal to its host is the unique partition cell. -/
theorem cComponents_eq_of_mem_host
    (G : ObservedGraph S) (nodes : NodeSet S) {c : NodeSet S}
    (hmem : c ∈ G.cComponents nodes) (heq : c = nodes) :
    G.cComponents nodes = [nodes] := by
  rcases cComponents_mem G nodes hmem with ⟨root, hroot, hdef⟩
  exact cComponents_eq_singleton G nodes hroot (heq.symm.trans hdef)

/--
A cell of an executable c-component partition is connected when viewed as
its own host, so repartitioning that cell returns the singleton list.  This is
the fact that prevents two product frames from occurring consecutively in an
ID trace.
-/
theorem cComponents_self_of_mem
    (G : ObservedGraph S) (nodes : NodeSet S) {component : NodeSet S}
    (componentMem : component ∈ G.cComponents nodes) :
    G.cComponents component = [component] := by
  rcases cComponents_mem G nodes componentMem with
    ⟨root, rootInNodes, componentEq⟩
  have rootInComponent : component root = true := by
    rw [componentEq]
    exact cComponentOf_root_mem G nodes rootInNodes
  have componentSelf : component = G.cComponentOf component root := by
    rw [componentEq]
    exact (cComponentOf_idempotent G nodes rootInNodes).symm
  exact cComponents_eq_singleton G component rootInComponent componentSelf

end Causality
end Thesis
