import Thesis.Causality.IdentificationSearch
import Thesis.Causality.ComponentConnectivity
import Thesis.Causality.ReachabilityCorrectness

namespace Thesis
namespace Causality

open Probability

/-!
# Constructive hedge routes and outcome readout geometry

A hedge records propositional root-to-outcome reachability. Countermodel
mechanisms need actual finite routes and typed parent/child lookups. This
layer reflects those walks into Boolean bounded search, then computes routes
using the supplied node enumeration. It never eliminates a bare existence
proof into chosen data or assumes a choice principle.

The readout routes avoid the original intervention. Their strict topological
order gives duplicate-free routes and terminating successor forests. The
priority composition keeps a stream on its action-free route once it enters
that route, rather than splitting it between the original forest and readout.
The common outcome-sink theorems retain precisely their original hypotheses.

These are graph and routing facts, not observational-law equality, positivity
of a model or a semantic completeness theorem. They contain no legacy engine
trace. `CompletenessFailureExtraction` retains its historical failure results
and reexports this shared geometry for import compatibility.

Consecutive-walk implication comes directly from the generic reachability
foundation. No active-path or moral-graph correctness theorem is needed by
these routes; in particular this layer does not import `DSeparationCorrectness`.
-/

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

end Causality
end Thesis
