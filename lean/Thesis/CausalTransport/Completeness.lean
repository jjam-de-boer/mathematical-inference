import Thesis.CausalTransport.Correspondence
import Thesis.CausalTransport.DSeparationCorrectness
import Thesis.Causality.IdentificationSearch

namespace Thesis
namespace Causality

open Probability

/-!
Constructive completeness of finite identification, specialized to the
classical model class.

`PublishedCompleteness` is indexed by a `GraphModelClass`.  The Shpitser–Pearl
/ Huang–Valtorta theorem is the inhabitant for `GraphModelClass.positive`
once the signature supplies `ValueRich` (two enumerated distinct values at
every node).  The unrestricted class `GraphModelClass.all` remains the home
of soundness: certificates that work with zeros.

This module currently records the executable ID engine, positivity of
observational cylinders, the empty-action certificate (already action-free),
agreement of executable c-components with inductive bidirected connectivity,
and extraction of a `HedgeWitness` from ID failure by finite search over
vertex selections and kept directed children inside the failing
c-component.  Successful ID runs are action-free observational formulae.
The remaining inhabitants are:

* success of `identifyJoint` implies a `DoCalculusDerivation` to the query
  kernel, hence a support-carrying `IdentificationCertificate`;
* Boolean hedge tests on some enumerated selection inside an ID failure
  (the thinned candidate is the intended one); search completeness already
  lifts any such selection to `hedgeWitness? = some _`;
* a `HedgeWitness` plus `ValueRich` yields a `CounterexampleIn` of the
  positive class, hence non-identifiability;
* therefore identifiability in the positive class implies ID success, which
  is `PublishedCompleteness (GraphModelClass.positive G)`.

No axiom of choice or excluded middle is used in the engine; the hedge
countermodel will pick the two `ValueRich` values by structure projection,
not by search through a `Prop`.
-/

/--
Observational cylinders used as ID denominators are strictly positive in
every member of the classical class.
-/
theorem positive_class_cylinder_positive {G : ObservedGraph S}
    (model : ExactModel S)
    (member : (GraphModelClass.positive G).Mem model)
    (nodes : NodeSet S) (reference : S.Assignment) :
    0 <
      (model.observationalDist.probVal
        (Kernel.agreesOn nodes reference)).num :=
  ObservationallyPositive.cylinder_positive member.2 nodes reference

/--
Empty-action joint queries are solved by ID in one step.  Combined with
soundness of that base case (the observational marginal equals the empty-do
kernel), they are identifiable in every class.
-/
theorem identifyJoint_empty_action_succeeds (G : ObservedGraph S)
    (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    identifyJoint G q =
      IdentificationOutcome.identified
        (.marginalize (NodeSet.diff NodeSet.full q.outcome)
          (observationalJointTerm S)) :=
  identifyJoint_of_empty_action G q emptyAction

/-- Successful ID returns an observational (action-free) formula. -/
theorem identifyJoint_success_actionFree
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {term : ProbabilityTerm S}
    (h : identifyJoint G q = IdentificationOutcome.identified term) :
    term.ActionFree :=
  identifyJoint_identified_actionFree G q h

/-- An empty-action kernel is already an action-free observational formula. -/
theorem JointKernelQuery.empty_action_free (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    q.sourceTerm.ActionFree := by
  intro i
  exact (NodeSet.isEmpty_eq_true_iff q.action).mp emptyAction i

/--
Empty-action queries are identifiable in every model class: observational
equivalence of action-free kernels is `actionFree_invariant`.
-/
def empty_action_identifiable {G : ObservedGraph S}
    (C : GraphModelClass G) (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    C.identifiable q := by
  intro left right _leftMem _rightMem observational assignment
  exact ⟨ProbabilityTerm.actionFree_invariant left right observational
    q.sourceTerm (q.empty_action_free emptyAction) assignment⟩

/--
The published certificate for an empty-action query is the reflexive
derivation of the source kernel.  No do-rule side condition is required.
-/
def emptyActionPublishedCertificate {G : ObservedGraph S}
    {C : GraphModelClass G} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    PublishedJointCertificate C correct q where
  formula := q.sourceTerm
  actionFree := q.empty_action_free emptyAction
  derivation :=
    @DoCalculusDerivation.refl S G (pathRuleSeparation G) q.sourceTerm
  supported := fun _model _member _assignment sourceSupported =>
    ⟨sourceSupported, ⟨sourceSupported, ()⟩⟩

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

/--
A bidirected component with a well-formed kept-child map is a `CForest`
on its kept-edge sinks.
-/
theorem cForest_of_component_child
    (G : ObservedGraph S) (nodes : NodeSet S) (child : ForestChild S)
    (hcomp : BidirectedComponent G nodes)
    (hwell : childWellFormedBool nodes child = true) :
    CForest G nodes (keptSinks nodes child) child where
  component := hcomp
  child_off_set := fun _ hp => childWellFormed_off nodes child hwell hp
  child_edge := fun _ _ hc => childWellFormed_edge nodes child hwell hc
  roots_exact := fun i => keptSinks_iff nodes child i

/--
A Boolean-connected node set with a well-formed kept-child map is a
`CForest` on its kept-edge sinks.
-/
theorem cForest_of_child
    (G : ObservedGraph S) (nodes : NodeSet S) (child : ForestChild S)
    (hsingle : G.isSingleCComponent nodes = true)
    (hwell : childWellFormedBool nodes child = true) :
    CForest G nodes (keptSinks nodes child) child := by
  rcases isSingleCComponent_spec G nodes hsingle with ⟨root, hroot, hEq⟩
  exact cForest_of_component_child G nodes child
    (by
      rw [hEq]
      exact cComponentOf_is_component G nodes hroot)
    hwell

/--
The executable c-component of a seed, with its induced child map, is a
`CForest`.  Extra induced directed edges are dropped by `inducedChild`.
-/
theorem cForest_of_thinned_component
    (G : ObservedGraph S) (nodes : NodeSet S) {seed : Fin S.count}
    (hseed : nodes seed = true) :
    CForest G (G.cComponentOf nodes seed)
      (keptSinks (G.cComponentOf nodes seed)
        (inducedChild (G.cComponentOf nodes seed)))
      (inducedChild (G.cComponentOf nodes seed)) :=
  cForest_of_component_child G (G.cComponentOf nodes seed)
    (inducedChild (G.cComponentOf nodes seed))
    (cComponentOf_is_component G nodes hseed)
    (inducedChild_wellFormed _)

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

theorem thinTowardForest_eq_cComponent_self
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep : Fin S.count) (fuel : Nat)
    (hY : nodes seedY = true) :
    thinTowardForest G nodes seedY seedKeep fuel =
      G.cComponentOf (thinTowardForest G nodes seedY seedKeep fuel) seedY := by
  rcases thinTowardForest_exists_host G nodes seedY seedKeep fuel hY with
    ⟨host, hHost, hEq⟩
  rw [hEq]
  exact (cComponentOf_idempotent G host hHost).symm

/--
When an outcome seed exists in the remaining set, the extracted large side
is the c-component of itself at that seed, so it is a legitimate forest host.
-/
theorem hedgeLargeOf_eq_cComponent_self
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seedY : Fin S.count}
    (hY : forestSeed q.outcome fail.remaining = some seedY) :
    hedgeLargeOf G q fail seedY = true ∧
      hedgeLargeOf G q fail =
        G.cComponentOf (hedgeLargeOf G q fail) seedY := by
  have hYmem : fail.remaining seedY = true :=
    forestSeed_mem q.outcome fail.remaining hY
  cases hX : NodeSet.firstMember (NodeSet.inter fail.remaining q.action) with
  | none =>
      constructor
      · simp [hedgeLargeOf, hY, hX]
        exact thinTowardForest_seed_mem G fail.remaining seedY seedY
          (NodeSet.members fail.remaining).length hYmem
      · simp [hedgeLargeOf, hY, hX]
        exact thinTowardForest_eq_cComponent_self G fail.remaining seedY seedY
          (NodeSet.members fail.remaining).length hYmem
  | some seedX =>
      constructor
      · simp [hedgeLargeOf, hY, hX]
        exact thinTowardForest_seed_mem G fail.remaining seedY seedX
          (NodeSet.members fail.remaining).length hYmem
      · simp [hedgeLargeOf, hY, hX]
        exact thinTowardForest_eq_cComponent_self G fail.remaining seedY seedX
          (NodeSet.members fail.remaining).length hYmem

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

/--
Top-level ID failure, when the extractor succeeds, is a `HedgeWitness`.
Success of ID still needs a derivation-to-certificate map; this is the
failure half of the joint completeness diagram.
-/
def hedgeWitnessOfJoint (G : ObservedGraph S) (q : JointKernelQuery S) :
    Option (HedgeWitness G q) :=
  match identifyJoint G q with
  | .failed fail => hedgeWitness? G q fail
  | _ => none

end Causality
end Thesis
