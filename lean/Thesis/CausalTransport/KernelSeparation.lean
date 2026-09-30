import Thesis.CausalTransport.Completeness

namespace Thesis
namespace Causality

/-!
# Graph side conditions for current-kernel component compilation

The topological chain compiler handles probability algebra.  Extracting a
c-component additionally needs graph-derived do-rule side conditions.  These
arguments must apply to arbitrary finite hosts, rather than accepting another
Boolean separation premise for each engine branch.

This module starts with the rule-3 half of the component-factor argument:
actions strictly later than a factor's vertex cannot affect that factor or
its earlier conditioner.  Incoming cuts make the later action vertices
isolated in the relevant ancestral moral graph.  The proof follows finite
directed and moral walks, so it does not select a path from a proposition or
use semantic soundness to establish a graph side condition.

The rule-2 exchange of earlier vertices outside a c-component is a distinct
graph step.  Its proof retains the host's external-action parent closure,
established for the initial host and preserved by both kinds of recursive
restriction.  These side conditions are prerequisites for the supported
component derivation, not the complete ID success compiler itself.
-/

namespace ObservedGraph

/-! ## The recursive host has no uncontrolled directed parent -/

/-- A kernel host is parent-closed after its external actions are fixed.

This is weaker than asking the external action to be the entire host
complement: ordinary ancestral pruning marginalizes discarded vertices
instead of intervening on them.  Every remaining directed parent must either
remain random in the host or be one of the already fixed external actions.
The full observational host satisfies the condition without any assumption. -/
structure KernelHostClosed (G : ObservedGraph S)
    (remaining externalAction : NodeSet S) : Prop where
  action_disjoint : NodeSet.Disjoint externalAction remaining
  parent_closed : forall {parent child : Fin S.count},
    remaining child = true -> S.directed parent child = true ->
      remaining parent = true ∨ externalAction parent = true

/-- The initial full host with no external intervention is closed. -/
theorem KernelHostClosed.full (G : ObservedGraph S) :
    KernelHostClosed G NodeSet.full NodeSet.empty where
  action_disjoint := NodeSet.disjoint_empty_left _
  parent_closed := fun _ _ => Or.inl rfl

/-- Component restriction fixes precisely the discarded host vertices in
addition to the previous external actions.  Closure holds for *any* host
subset, so no extra component-specific parent hypothesis is smuggled into
the recursive success compiler. -/
theorem KernelHostClosed.restrict
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : KernelHostClosed G remaining externalAction)
    (kept : NodeSet S) (keptSubset : NodeSet.Subset kept remaining) :
    KernelHostClosed G kept
      (NodeSet.union externalAction (NodeSet.diff remaining kept)) where
  action_disjoint := by
    intro node selected
    cases (NodeSet.union_eq_true externalAction (NodeSet.diff remaining kept) node).mp
        selected with
    | inl external =>
        exact NodeSet.disjoint_of_subset_right closed.action_disjoint keptSubset
          node external
    | inr removed =>
        cases included : kept node with
        | false => rfl
        | true =>
            have excluded := (Bool.and_eq_true_iff.mp removed).2
            rw [included] at excluded
            cases excluded
  parent_closed := by
    intro parent child childKept edge
    cases closed.parent_closed (keptSubset child childKept) edge with
    | inr external =>
        exact Or.inr ((NodeSet.union_eq_true externalAction
          (NodeSet.diff remaining kept) parent).mpr (Or.inl external))
    | inl parentRemaining =>
        cases parentKept : kept parent with
        | true => exact Or.inl rfl
        | false =>
            exact Or.inr ((NodeSet.union_eq_true externalAction
              (NodeSet.diff remaining kept) parent).mpr (Or.inr
                (Bool.and_eq_true_iff.mpr ⟨parentRemaining, by simp [parentKept]⟩)))

/-- Prepending an induced directed edge preserves the executable ancestral
selection.  Rebounding the concatenated walk uses the finite vertex list;
one does not assume that prepending happens to fit the old fuel bound. -/
theorem ancestorOfWithin_prepend
    (G : ObservedGraph S) (remaining : NodeSet S)
    (mutilation : GraphMutilation S) (targets : NodeSet S)
    {parent child : Fin S.count}
    (edge : G.directedEdgeWithin remaining mutilation parent child = true)
    (childAncestor : G.ancestorOfWithin remaining mutilation targets child = true) :
    G.ancestorOfWithin remaining mutilation targets parent = true := by
  have parentRemaining := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp edge).1).1
  rcases List.any_eq_true.mp (Bool.and_eq_true_iff.mp childAncestor).2 with
    ⟨target, member, reached⟩
  have bounded := (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
    (NodeSet.enumerated S) (G.directedEdgeWithin remaining mutilation)
    finBeq_eq_true_iff (NodeSet.mem_enumerated S) S.count child target).mp reached
  have reachable := FiniteReachability.Reachable.prepend edge
    (FiniteReachability.Reachable.of_bounded bounded)
  have rebound := FiniteReachability.boundedWalk_of_reachable finBeq
    (NodeSet.enumerated S) (G.directedEdgeWithin remaining mutilation)
    finBeq_eq_true_iff (NodeSet.mem_enumerated S) reachable
  have reboundCount : FiniteReachability.BoundedWalk
      (G.directedEdgeWithin remaining mutilation) S.count parent target := by
    simpa only [NodeSet.length_enumerated] using rebound
  exact Bool.and_eq_true_iff.mpr ⟨parentRemaining,
    List.any_eq_true.mpr ⟨target, member,
      (FiniteReachability.within_eq_true_iff_boundedWalk finBeq
        (NodeSet.enumerated S) (G.directedEdgeWithin remaining mutilation)
        finBeq_eq_true_iff (NodeSet.mem_enumerated S) S.count parent target).mpr
          reboundCount⟩⟩

/-- Uncut ancestral pruning preserves closure while keeping the same
external actions.  This is the replacement engine's actual pruning branch,
not the legacy incoming-cut pruning operation. -/
theorem KernelHostClosed.ancestral
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : KernelHostClosed G remaining externalAction) (targets : NodeSet S) :
    KernelHostClosed G
      (G.ancestralSet remaining (GraphMutilation.none S) targets) externalAction where
  action_disjoint := NodeSet.disjoint_of_subset_right closed.action_disjoint
    (ancestralSet_subset G remaining (GraphMutilation.none S) targets)
  parent_closed := by
    intro parent child childAncestor directed
    have childRemaining := ancestralSet_subset G remaining
      (GraphMutilation.none S) targets child childAncestor
    cases closed.parent_closed childRemaining directed with
    | inr external => exact Or.inr external
    | inl parentRemaining =>
        apply Or.inl
        apply G.ancestorOfWithin_prepend remaining (GraphMutilation.none S) targets
          (childAncestor := childAncestor)
        simp only [directedEdgeWithin, observedDirectedEdge, GraphMutilation.none,
          NodeSet.empty, Bool.not_false, Bool.and_true]
        exact Bool.and_eq_true_iff.mpr
          ⟨Bool.and_eq_true_iff.mpr ⟨parentRemaining, childRemaining⟩, directed⟩

/-! ## Topological bounds on finite ancestry -/

/-- A directed walk between observed vertices never decreases their
topological indices.  Only the declared strict ordering of each directed
edge is used; incoming and outgoing graph cuts can remove edges, not reverse
their order. -/
theorem observedDirectedWalk_val_le (G : ObservedGraph S)
    (mutilation : GraphMutilation S) {length : Nat}
    {source target : Fin S.count}
    (walk : FiniteReachability.ExactWalk (G.observedDirectedEdge mutilation)
      length source target) : source.val ≤ target.val := by
  induction walk with
  | refl => exact Nat.le_refl _
  | step first _rest inductionHypothesis =>
      have directed := (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp first).1).1
      exact Nat.le_trans (Nat.le_of_lt (S.directed_earlier directed))
        inductionHypothesis

/-- A vertex strictly beyond a numeric bound is not an ancestor of a family
entirely at or before that bound, in any mutilated observed DAG. -/
theorem observedAncestorOf_false_of_late
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets : NodeSet S) (bound : Nat)
    (targetsBefore : forall target, targets target = true -> target.val ≤ bound)
    (source : Fin S.count) (late : bound < source.val) :
    G.observedAncestorOf mutilation targets source = false := by
  cases ancestor : G.observedAncestorOf mutilation targets source with
  | false => rfl
  | true =>
      rcases (G.observedAncestorOf_eq_true_iff mutilation targets source).mp
        ancestor with ⟨target, selected, length, _lengthBound, walk⟩
      rcases walk with ⟨walk⟩
      have ordered := G.observedDirectedWalk_val_le mutilation walk
      have before := targetsBefore target selected
      omega

/-- No expanded-DAG arrow enters an observed vertex whose incoming arrows
have been cut.  This includes the arrow from a projected latent-pair root. -/
theorem expandedMutilatedEdge_into_cut_false
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (parent : SeparationNode S) (child : Fin S.count)
    (cut : mutilation.removeIncoming child = true) :
    G.expandedMutilatedEdge mutilation parent (.observed child) = false := by
  cases parent <;> simp [expandedMutilatedEdge, cut]

/-- The target family contains only early vertices and incoming-cut
vertices.  Every observed ancestor is therefore also early or incoming-cut.

A backward step into a cut vertex is impossible; a backward step into an
early vertex strictly lowers the observed index.  Latent roots impose no
numeric bound, since the conclusion is about observed ancestors only. -/
theorem ancestorOf_observed_cut_or_before
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets : NodeSet S) (bound : Nat)
    (targetsBefore : forall target, targets target = true ->
      mutilation.removeIncoming target = true ∨ target.val ≤ bound)
    (source : Fin S.count)
    (ancestor : G.ancestorOf mutilation targets (.observed source) = true) :
    mutilation.removeIncoming source = true ∨ source.val ≤ bound := by
  let property : SeparationNode S -> Prop := fun vertex =>
    match vertex with
    | .observed node => mutilation.removeIncoming node = true ∨ node.val ≤ bound
    | .latentPair _ _ => True
  have backwards : forall {parent child},
      G.expandedMutilatedEdge mutilation parent child = true ->
        property child -> property parent := by
    intro parent child edge childProperty
    cases parent with
    | latentPair _ _ => trivial
    | observed parent =>
        cases child with
        | latentPair _ _ => cases edge
        | observed child =>
            have parts := Bool.and_eq_true_iff.mp edge
            have directed := (Bool.and_eq_true_iff.mp parts.1).1
            cases childProperty with
            | inl cut =>
                rw [G.expandedMutilatedEdge_into_cut_false mutilation
                  (.observed parent) child cut] at edge
                cases edge
            | inr before =>
                exact Or.inr (Nat.le_trans
                  (Nat.le_of_lt (S.directed_earlier directed)) before)
  rcases (G.ancestorOf_eq_true_iff mutilation targets (.observed source)).mp
    ancestor with ⟨target, selected, length, _lengthBound, walk⟩
  rcases walk with ⟨walk⟩
  have backwardsWalk {length : Nat} {parent child : SeparationNode S}
      (walk : FiniteReachability.ExactWalk (G.expandedMutilatedEdge mutilation)
        length parent child) (childProperty : property child) : property parent := by
    induction walk with
    | refl => exact childProperty
    | step first _rest inductionHypothesis =>
        exact backwards first (inductionHypothesis childProperty)
  exact backwardsWalk walk (targetsBefore target selected)

/-! ## Later incoming-cut vertices are morally isolated -/

/-- A late observed vertex has no outgoing edge to an ancestor of an
early-or-cut target family.  An early child contradicts topological order;
an incoming-cut child cannot receive the edge at all. -/
theorem expandedMutilatedEdge_from_late_to_ancestor_false
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets : NodeSet S) (bound : Nat)
    (targetsBefore : forall target, targets target = true ->
      mutilation.removeIncoming target = true ∨ target.val ≤ bound)
    (source : Fin S.count) (late : bound < source.val)
    (child : SeparationNode S)
    (ancestor : G.ancestorOf mutilation targets child = true) :
    G.expandedMutilatedEdge mutilation (.observed source) child = false := by
  cases child with
  | latentPair _ _ => rfl
  | observed child =>
      cases G.ancestorOf_observed_cut_or_before mutilation targets bound
        targetsBefore child ancestor with
      | inl cut =>
          exact G.expandedMutilatedEdge_into_cut_false mutilation
            (.observed source) child cut
      | inr before =>
          cases edge : G.expandedMutilatedEdge mutilation
              (.observed source) (.observed child) with
          | false => rfl
          | true =>
              have directed := (Bool.and_eq_true_iff.mp
                (Bool.and_eq_true_iff.mp edge).1).1
              have earlier := S.directed_earlier directed
              omega

/-- A later incoming-cut action vertex is isolated in the ancestral moral
graph of an early-or-cut target family.  Besides direct arrows, the proof
also rules out moral edges introduced by a shared ancestral child. -/
theorem ancestralMoralEdge_from_late_cut_false
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (targets : NodeSet S) (bound : Nat)
    (targetsBefore : forall target, targets target = true ->
      mutilation.removeIncoming target = true ∨ target.val ≤ bound)
    (source : Fin S.count) (late : bound < source.val)
    (cut : mutilation.removeIncoming source = true) (other : SeparationNode S) :
    G.ancestralMoralEdge mutilation targets (.observed source) other = false := by
  cases moral : G.ancestralMoralEdge mutilation targets (.observed source) other with
  | false => rfl
  | true =>
      have otherAncestor :=
        (G.ancestorOf_of_ancestralMoralEdge mutilation targets moral).2
      cases G.ancestralMoralEdge_cases mutilation targets moral with
      | inl adjacent =>
          cases adjacent with
          | inl forward =>
              rw [G.expandedMutilatedEdge_from_late_to_ancestor_false
                mutilation targets bound targetsBefore source late other
                otherAncestor] at forward
              cases forward
          | inr reverse =>
              rw [G.expandedMutilatedEdge_into_cut_false mutilation other source cut]
                at reverse
              cases reverse
      | inr common =>
          rcases common with ⟨child, childAncestor, forward, _otherParent⟩
          rw [G.expandedMutilatedEdge_from_late_to_ancestor_false
            mutilation targets bound targetsBefore source late child childAncestor]
            at forward
          cases forward

/-- A walk terminating at a vertex with no incoming edge can only start
at that same vertex.  This direct finite-walk induction avoids extracting
a last edge or choosing a shortest path. -/
private theorem exactWalk_to_isolated_eq
    {edge : α -> α -> Bool} {length : Nat} {source target : α}
    (walk : FiniteReachability.ExactWalk edge length source target)
    (isolated : forall other, edge other target = false) : source = target := by
  induction walk with
  | refl => rfl
  | @step _ _ middle _ first _rest inductionHypothesis =>
      have same := inductionHypothesis isolated
      rw [same, isolated _] at first
      cases first

/-- Disjoint left endpoints are separated from a family of right vertices
isolated in the relevant ancestral moral graph.  Both later-action deletion
and non-ancestor deletion use this same finite-walk argument; their distinct
graph proofs supply the isolation premise rather than assuming separation. -/
theorem dSeparated_of_ancestrally_isolated_right
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S) (disjoint : NodeSet.Disjoint left right)
    (rightIsolated : forall target, right target = true -> forall other,
      G.ancestralMoralEdge mutilation
        (NodeSet.union left (NodeSet.union right conditioned))
        (.observed target) other = false) :
    G.dSeparated mutilation left right conditioned = true := by
  apply (G.dSeparated_eq_true_iff_no_moralReachable mutilation left right conditioned).mpr
  rintro ⟨source, target, sourceSelected, _sourceOpen,
    targetSelected, _targetOpen, reachable⟩
  let targets := NodeSet.union left (NodeSet.union right conditioned)
  have isolated : forall other,
      G.MoralOpenEdge mutilation targets conditioned other (.observed target) = false := by
    intro other
    cases edge : G.MoralOpenEdge mutilation targets conditioned other (.observed target) with
    | false => rfl
    | true =>
        have reverse := G.moralOpenEdge_symmetric mutilation targets conditioned edge
        have moral := (MoralOpenEdge.unpacked G mutilation targets conditioned reverse).2.2
        rw [rightIsolated target targetSelected other] at moral
        cases moral
  rcases (G.moralReachable_eq_true_iff mutilation targets conditioned
    (.observed source) (.observed target)).mp reachable with
    ⟨_length, _lengthBound, walk⟩
  rcases walk with ⟨walk⟩
  have same := exactWalk_to_isolated_eq walk isolated
  have sameIndex : source = target := by injection same
  have notRight := disjoint source sourceSelected
  rw [sameIndex, targetSelected] at notRight
  cases notRight

/-- General separation of early left endpoints from later incoming-cut
right endpoints.  All other target vertices must be early or incoming-cut;
conditioned action vertices can therefore have arbitrary topological indices.
This is an executable separation theorem, not a supplied Boolean premise. -/
theorem dSeparated_of_late_cut_right
    (G : ObservedGraph S) (mutilation : GraphMutilation S)
    (left right conditioned : NodeSet S) (bound : Nat)
    (leftBefore : forall node, left node = true -> node.val ≤ bound)
    (rightLateCut : forall node, right node = true ->
      bound < node.val ∧ mutilation.removeIncoming node = true)
    (targetsBefore : forall node,
      NodeSet.union left (NodeSet.union right conditioned) node = true ->
        mutilation.removeIncoming node = true ∨ node.val ≤ bound) :
    G.dSeparated mutilation left right conditioned = true := by
  apply G.dSeparated_of_ancestrally_isolated_right mutilation left right conditioned
  · intro node selected
    cases alsoRight : right node with
    | false => rfl
    | true =>
        have before := leftBefore node selected
        have after := (rightLateCut node alsoRight).1
        omega
  · intro target selected other
    have data := rightLateCut target selected
    exact G.ancestralMoralEdge_from_late_cut_false mutilation
      (NodeSet.union left (NodeSet.union right conditioned)) bound
      targetsBefore target data.1 data.2 other

/-! ## Rule 3 removes every later action from a topological factor -/

/-- Later action vertices cannot ancestor an earlier conditioner, so the
published rule-3 removable set `Z(W)` is exactly the whole later block. -/
theorem nonAncestorsOf_eq_of_late_actions
    (G : ObservedGraph S) (baseAction later condition : NodeSet S) (bound : Nat)
    (laterAfter : forall node, later node = true -> bound < node.val)
    (conditionBefore : forall node, condition node = true -> node.val ≤ bound) :
    G.nonAncestorsOf (GraphMutilation.bar baseAction) later condition = later := by
  funext node
  cases selected : later node with
  | false => simp [nonAncestorsOf, selected]
  | true =>
      have notAncestor := G.observedAncestorOf_false_of_late
        (GraphMutilation.bar baseAction) condition bound conditionBefore node
        (laterAfter node selected)
      simp [nonAncestorsOf, selected, notAncestor]

/-- The incoming-cut graph for deleting later actions d-separates a
topological factor from the entire later action block, given its base actions
and an earlier conditioner.  Base actions need no numeric bound. -/
theorem dSeparated_factor_late_actions
    (G : ObservedGraph S) (baseAction later condition : NodeSet S)
    (node : Fin S.count)
    (laterAfter : forall selected, later selected = true -> node.val < selected.val)
    (conditionBefore : forall selected, condition selected = true -> selected.val ≤ node.val) :
    G.dSeparated (GraphMutilation.bar (NodeSet.union baseAction later))
      (NodeSet.singleton node) later (NodeSet.union baseAction condition) = true := by
  apply G.dSeparated_of_late_cut_right
    (GraphMutilation.bar (NodeSet.union baseAction later))
    (NodeSet.singleton node) later (NodeSet.union baseAction condition) node.val
  · intro selected member
    have same := (NodeSet.singleton_eq_true_iff node selected).mp member
    subst selected
    exact Nat.le_refl _
  · intro selected member
    exact ⟨laterAfter selected member,
      (NodeSet.union_eq_true baseAction later selected).mpr (Or.inr member)⟩
  · intro selected member
    cases (NodeSet.union_eq_true (NodeSet.singleton node)
        (NodeSet.union later (NodeSet.union baseAction condition)) selected).mp member with
    | inl singleton =>
        have same := (NodeSet.singleton_eq_true_iff node selected).mp singleton
        subst selected
        exact Or.inr (Nat.le_refl _)
    | inr others =>
        cases (NodeSet.union_eq_true later (NodeSet.union baseAction condition) selected).mp
            others with
        | inl selectedLater =>
            exact Or.inl ((NodeSet.union_eq_true baseAction later selected).mpr
              (Or.inr selectedLater))
        | inr selectedConditioned =>
            cases (NodeSet.union_eq_true baseAction condition selected).mp
                selectedConditioned with
            | inl selectedAction =>
                exact Or.inl ((NodeSet.union_eq_true baseAction later selected).mpr
                  (Or.inl selectedAction))
            | inr selectedCondition =>
                exact Or.inr (conditionBefore selected selectedCondition)

/-- The actual path-based rule-3 side condition follows from topological
order alone.  In particular, the removable block is *proved* equal to `later`;
it is not replaced by all of `Z` without checking the conditioner ancestors. -/
theorem pathDSeparated_rule3_late_actions
    (G : ObservedGraph S) (baseAction later condition : NodeSet S)
    (node : Fin S.count)
    (laterAfter : forall selected, later selected = true -> node.val < selected.val)
    (conditionBefore : forall selected, condition selected = true -> selected.val ≤ node.val) :
    let base := GraphMutilation.bar baseAction
    let removable := G.nonAncestorsOf base later condition
    PathSpecification.PathDSeparated G
      { removeIncoming := NodeSet.union baseAction removable,
        removeOutgoing := NodeSet.empty }
      (NodeSet.singleton node) later (NodeSet.union baseAction condition) := by
  dsimp
  rw [G.nonAncestorsOf_eq_of_late_actions baseAction later condition node.val
    laterAfter conditionBefore]
  exact G.dSeparationCorrectness.pathDSeparated_of_dSeparated
    (G.dSeparated_factor_late_actions baseAction later condition node
      laterAfter conditionBefore)

/-! ## Earlier outside-component actions can become observations -/

/-- Incoming cuts on the external actions make a parent-closed kernel host
closed under observed ancestry.  Targets may be host variables or external
actions; a directed path cannot enter an external action from another vertex.
The result concerns the full expanded ancestry search, not only host-local
paths, so an uncontrolled outside parent cannot be hidden by induced search. -/
theorem KernelHostClosed.ancestorOf_in_host
    {G : ObservedGraph S} {remaining externalAction : NodeSet S}
    (closed : KernelHostClosed G remaining externalAction)
    (mutilation : GraphMutilation S)
    (cutsExternal : NodeSet.Subset externalAction mutilation.removeIncoming)
    (targets : NodeSet S)
    (targetsInside : forall target, targets target = true ->
      remaining target = true ∨ externalAction target = true)
    (source : Fin S.count)
    (ancestor : G.ancestorOf mutilation targets (.observed source) = true) :
    remaining source = true ∨ externalAction source = true := by
  let property : SeparationNode S -> Prop := fun vertex =>
    match vertex with
    | .observed node => remaining node = true ∨ externalAction node = true
    | .latentPair _ _ => True
  have backwards : forall {parent child},
      G.expandedMutilatedEdge mutilation parent child = true ->
        property child -> property parent := by
    intro parent child edge childProperty
    cases parent with
    | latentPair _ _ => trivial
    | observed parent =>
        cases child with
        | latentPair _ _ => cases edge
        | observed child =>
            cases childProperty with
            | inl inside =>
                exact closed.parent_closed inside
                  ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp edge).1).1)
            | inr external =>
                rw [G.expandedMutilatedEdge_into_cut_false mutilation
                  (.observed parent) child (cutsExternal child external)] at edge
                cases edge
  rcases (G.ancestorOf_eq_true_iff mutilation targets (.observed source)).mp
    ancestor with ⟨target, selected, _length, _lengthBound, walk⟩
  rcases walk with ⟨walk⟩
  have backwardsWalk {length : Nat} {parent child : SeparationNode S}
      (walk : FiniteReachability.ExactWalk (G.expandedMutilatedEdge mutilation)
        length parent child) (childProperty : property child) : property parent := by
    induction walk with
    | refl => exact childProperty
    | step first _rest inductionHypothesis =>
        exact backwards first (inductionHypothesis childProperty)
  exact backwardsWalk walk (targetsInside target selected)

/-- Every listed c-component is closed across bidirected edges within its
host.  Membership in the actual executable partition supplies this property;
connectedness alone would not rule out an edge leaving a nonmaximal subset. -/
theorem cComponents_bidirected_closed
    (G : ObservedGraph S) (remaining : NodeSet S) {component : NodeSet S}
    (listed : component ∈ G.cComponents remaining)
    {source target : Fin S.count} (sourceInside : component source = true)
    (targetRemaining : remaining target = true)
    (edge : G.bidirected source target = true) : component target = true := by
  rcases cComponents_mem G remaining listed with ⟨root, rootSelected, rfl⟩
  have rootToSource := (cComponentOf_eq_true_iff G remaining rootSelected).mp sourceInside
  exact (cComponentOf_eq_true_iff G remaining rootSelected).mpr
    (.tail rootToSource targetRemaining edge)

/-- Observed component vertices and every latent-pair root incident to one
of them form the Boolean side used in the rule-2 moral-graph proof.  No root
is selected from an existence proposition: the two endpoints are explicit. -/
def kernelComponentSide (component : NodeSet S) : SeparationNode S -> Bool
  | .observed node => component node
  | .latentPair left right => component left || component right

/-- Exchange all earlier host vertices outside a bidirected-closed component
from actions to observations in one rule-2 application.

The theorem admits any union of complete host components: connectivity and
nonemptiness are unnecessary for separation.  For a listed component,
`cComponents_subset` and `cComponents_bidirected_closed` supply the two
component hypotheses directly.

After the outgoing cut on the exchanged predecessors, an open ancestral
moral edge cannot leave `kernelComponentSide component`.  Directed parents
outside the component are precisely the cut earlier vertices; later children
cannot be ancestral; and latent roots cannot cross the host's bidirected
component boundary.  The shared-child moral edges are checked as well. -/
theorem dSeparated_factor_outside_predecessors
    (G : ObservedGraph S) (remaining externalAction component : NodeSet S)
    (closed : KernelHostClosed G remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true ->
      remaining target = true -> G.bidirected source target = true ->
        component target = true)
    (node : Fin S.count) (nodeInside : component node = true) :
    G.dSeparated
      (GraphMutilation.barUnderline externalAction
        (NodeSet.diff (chainCondition remaining node) component))
      (NodeSet.singleton node)
      (NodeSet.diff (chainCondition remaining node) component)
      (NodeSet.union externalAction (chainCondition component node)) = true := by
  let earlier := chainCondition component node
  let exchanged := NodeSet.diff (chainCondition remaining node) component
  let mutilation := GraphMutilation.barUnderline externalAction exchanged
  let conditioned := NodeSet.union externalAction earlier
  let targets := NodeSet.union (NodeSet.singleton node)
    (NodeSet.union exchanged conditioned)
  let side := kernelComponentSide component
  -- Every observed search target belongs to the host or its external
  -- action.  External targets may be later than the factor, but their
  -- incoming cuts prevent them from acquiring uncontrolled ancestors.
  have targetsInside : forall target, targets target = true ->
      remaining target = true ∨ externalAction target = true := by
    intro target selected
    cases (NodeSet.union_eq_true (NodeSet.singleton node)
        (NodeSet.union exchanged conditioned) target).mp selected with
    | inl singleton =>
        have same := (NodeSet.singleton_eq_true_iff node target).mp singleton
        subst target
        exact Or.inl (componentSubset node nodeInside)
    | inr others =>
        cases (NodeSet.union_eq_true exchanged conditioned target).mp others with
        | inl outside =>
            exact Or.inl ((Bool.and_eq_true_iff.mp
              (Bool.and_eq_true_iff.mp outside).1).1)
        | inr conditioning =>
            cases (NodeSet.union_eq_true externalAction earlier target).mp conditioning with
            | inl external => exact Or.inr external
            | inr inside =>
                exact Or.inl (componentSubset target (Bool.and_eq_true_iff.mp inside).1)
  have targetsBefore : forall target, targets target = true ->
      mutilation.removeIncoming target = true ∨ target.val ≤ node.val := by
    intro target selected
    cases (NodeSet.union_eq_true (NodeSet.singleton node)
        (NodeSet.union exchanged conditioned) target).mp selected with
    | inl singleton =>
        have same := (NodeSet.singleton_eq_true_iff node target).mp singleton
        subst target
        exact Or.inr (Nat.le_refl _)
    | inr others =>
        cases (NodeSet.union_eq_true exchanged conditioned target).mp others with
        | inl outside =>
            have before := of_decide_eq_true
              (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp outside).1).2
            exact Or.inr (Nat.le_of_lt before)
        | inr conditioning =>
            cases (NodeSet.union_eq_true externalAction earlier target).mp conditioning with
            | inl external => exact Or.inl external
            | inr inside =>
                exact Or.inr (Nat.le_of_lt
                  (of_decide_eq_true (Bool.and_eq_true_iff.mp inside).2))
  have externalFalse {vertex : Fin S.count} (openVertex : conditioned vertex = false) :
      externalAction vertex = false := by
    cases selected : externalAction vertex with
    | false => rfl
    | true =>
        have blocked := (NodeSet.union_eq_true externalAction earlier vertex).mpr
          (Or.inl selected)
        change conditioned vertex = true at blocked
        rw [openVertex] at blocked
        cases blocked
  -- An open observed ancestor cannot be an external action: those vertices
  -- are conditioned.  Parent closure therefore puts it back in the host,
  -- and the early-or-cut ancestry bound puts it at or before this factor.
  have openAncestor {vertex : Fin S.count}
      (ancestor : G.ancestorOf mutilation targets (.observed vertex) = true)
      (openVertex : conditioned vertex = false) :
      remaining vertex = true ∧ vertex.val ≤ node.val := by
    have notExternal := externalFalse openVertex
    have host := closed.ancestorOf_in_host mutilation (fun _ selected => selected)
      targets targetsInside vertex ancestor
    have before := G.ancestorOf_observed_cut_or_before mutilation targets node.val
      targetsBefore vertex ancestor
    constructor
    · cases host with
      | inl inside => exact inside
      | inr external => rw [notExternal] at external; cases external
    · cases before with
      | inr earlier => exact earlier
      | inl cut =>
          change externalAction vertex = true at cut
          rw [notExternal] at cut
          cases cut
  -- All strictly earlier component vertices are conditioned too.  Hence
  -- the factor vertex is the only open observed vertex on the component
  -- side; latent roots can still lie on that side and must be handled below.
  have openComponent_eq_node {vertex : Fin S.count}
      (inside : component vertex = true)
      (ancestor : G.ancestorOf mutilation targets (.observed vertex) = true)
      (openVertex : conditioned vertex = false) : vertex = node := by
    have bound := (openAncestor ancestor openVertex).2
    cases Nat.lt_or_eq_of_le bound with
    | inr equal => exact Fin.ext equal
    | inl before =>
        have earlierSelected : earlier vertex = true :=
          Bool.and_eq_true_iff.mpr ⟨inside, decide_eq_true before⟩
        have blocked := (NodeSet.union_eq_true externalAction earlier vertex).mpr
          (Or.inr earlierSelected)
        change conditioned vertex = true at blocked
        rw [openVertex] at blocked
        cases blocked
  -- An outgoing edge from the factor cannot reach an ancestral child:
  -- topological order excludes an early child, and an incoming-cut child
  -- cannot receive the edge.  This also eliminates its shared-child moral
  -- edges, not just its ordinary directed adjacencies.
  have noForward {vertex : Fin S.count} (inside : component vertex = true)
      (ancestor : G.ancestorOf mutilation targets (.observed vertex) = true)
      (openVertex : conditioned vertex = false) (child : SeparationNode S)
      (childAncestor : G.ancestorOf mutilation targets child = true) :
      G.expandedMutilatedEdge mutilation (.observed vertex) child = false := by
    have same := openComponent_eq_node inside ancestor openVertex
    subst vertex
    cases child with
    | latentPair _ _ => rfl
    | observed child =>
        cases G.ancestorOf_observed_cut_or_before mutilation targets node.val
            targetsBefore child childAncestor with
        | inl cut =>
            exact G.expandedMutilatedEdge_into_cut_false mutilation
              (.observed node) child cut
        | inr before =>
            cases edge : G.expandedMutilatedEdge mutilation (.observed node) (.observed child) with
            | false => rfl
            | true =>
                have directed := (Bool.and_eq_true_iff.mp
                  (Bool.and_eq_true_iff.mp edge).1).1
                have ordered := S.directed_earlier directed
                omega
  -- An open observed parent of a component child is an earlier host vertex.
  -- If it were outside the component it would belong to `exchanged`, whose
  -- outgoing cut forbids exactly this edge.  Conditioned external parents
  -- have already been excluded by `openAncestor`.
  have observedParentInside {parent child : Fin S.count}
      (parentAncestor : G.ancestorOf mutilation targets (.observed parent) = true)
      (parentOpen : conditioned parent = false)
      (childInside : component child = true)
      (childAncestor : G.ancestorOf mutilation targets (.observed child) = true)
      (edge : G.expandedMutilatedEdge mutilation (.observed parent) (.observed child) = true) :
      component parent = true := by
    have parentHost := (openAncestor parentAncestor parentOpen).1
    have childNotExternal : externalAction child = false :=
      closed.action_disjoint.symm child (componentSubset child childInside)
    have childBefore : child.val ≤ node.val := by
      cases G.ancestorOf_observed_cut_or_before mutilation targets node.val
          targetsBefore child childAncestor with
      | inr before => exact before
      | inl cut =>
          change externalAction child = true at cut
          rw [childNotExternal] at cut
          cases cut
    have parts := Bool.and_eq_true_iff.mp edge
    have parentParts := Bool.and_eq_true_iff.mp parts.1
    have ordered := S.directed_earlier parentParts.1
    have parentBefore : parent.val < node.val := Nat.lt_of_lt_of_le ordered childBefore
    cases selected : component parent with
    | true => rfl
    | false =>
        have exchangedParent : exchanged parent = true :=
          Bool.and_eq_true_iff.mpr
            ⟨Bool.and_eq_true_iff.mpr ⟨parentHost, decide_eq_true parentBefore⟩,
              by simp [selected]⟩
        have notExchanged := parentParts.2
        change Bool.not (exchanged parent) = true at notExchanged
        rw [exchangedParent] at notExchanged
        cases notExchanged
  -- A latent parent is incident to its component child by definition of the
  -- expanded pair-root graph; its explicit endpoints determine side membership.
  have latentParentInside {left right child : Fin S.count}
      (childInside : component child = true)
      (edge : G.expandedMutilatedEdge mutilation (.latentPair left right) (.observed child) = true) :
      side (.latentPair left right) = true := by
    have endpoints := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp edge).1).2
    cases Bool.or_eq_true_iff.mp endpoints with
    | inl atLeft =>
        have same := (finBeq_eq_true_iff _ _).mp atLeft
        subst child
        exact Bool.or_eq_true_iff.mpr (Or.inl childInside)
    | inr atRight =>
        have same := (finBeq_eq_true_iff _ _).mp atRight
        subst child
        exact Bool.or_eq_true_iff.mpr (Or.inr childInside)
  -- In the other direction, host closure places an ancestral child back in
  -- the host.  Bidirected closure then prevents a root incident to a component
  -- vertex from reaching an outside-component host vertex.
  have latentChildInside {left right child : Fin S.count}
      (rootInside : side (.latentPair left right) = true)
      (childAncestor : G.ancestorOf mutilation targets (.observed child) = true)
      (edge : G.expandedMutilatedEdge mutilation (.latentPair left right) (.observed child) = true) :
      component child = true := by
    have parts := Bool.and_eq_true_iff.mp edge
    have rootParts := Bool.and_eq_true_iff.mp parts.1
    have childNotExternal : externalAction child = false := by simpa using parts.2
    have childHost : remaining child = true := by
      cases closed.ancestorOf_in_host mutilation (fun _ selected => selected)
          targets targetsInside child childAncestor with
      | inl inside => exact inside
      | inr external => rw [childNotExternal] at external; cases external
    cases Bool.or_eq_true_iff.mp rootInside with
    | inl leftInside =>
        cases Bool.or_eq_true_iff.mp rootParts.2 with
        | inl atLeft =>
            have same := (finBeq_eq_true_iff _ _).mp atLeft
            subst child
            exact leftInside
        | inr atRight =>
            have same := (finBeq_eq_true_iff _ _).mp atRight
            subst child
            exact bidirectedClosed leftInside childHost rootParts.1
    | inr rightInside =>
        cases Bool.or_eq_true_iff.mp rootParts.2 with
        | inl atLeft =>
            have same := (finBeq_eq_true_iff _ _).mp atLeft
            subst child
            exact bidirectedClosed rightInside childHost (G.bidirected_symmetric rootParts.1)
        | inr atRight =>
            have same := (finBeq_eq_true_iff _ _).mp atRight
            subst child
            exact rightInside
  -- Check all ancestral moral edges, including co-parent edges introduced
  -- by an ancestral child.  Ignoring that last case would not establish
  -- d-separation: moralization can connect parents that are not adjacent.
  have moralClosed {source target : SeparationNode S}
      (sourceInside : side source = true)
      (edge : G.MoralOpenEdge mutilation targets conditioned source target = true) :
      side target = true := by
    have openEnds := MoralOpenEdge.unpacked G mutilation targets conditioned edge
    have ancestors := G.ancestorOf_of_ancestralMoralEdge mutilation targets openEnds.2.2
    cases source with
    | observed source =>
        cases G.ancestralMoralEdge_cases mutilation targets openEnds.2.2 with
        | inl adjacent =>
            cases adjacent with
            | inl forward =>
                rw [noForward sourceInside ancestors.1 openEnds.1 target ancestors.2] at forward
                cases forward
            | inr reverse =>
                cases target with
                | observed parent =>
                    exact observedParentInside ancestors.2 openEnds.2.1
                      sourceInside ancestors.1 reverse
                | latentPair left right => exact latentParentInside sourceInside reverse
        | inr common =>
            rcases common with ⟨child, childAncestor, forward, _otherParent⟩
            rw [noForward sourceInside ancestors.1 openEnds.1 child childAncestor] at forward
            cases forward
    | latentPair left right =>
        cases G.ancestralMoralEdge_cases mutilation targets openEnds.2.2 with
        | inl adjacent =>
            cases adjacent with
            | inl forward =>
                cases target with
                | latentPair _ _ => cases forward
                | observed child => exact latentChildInside sourceInside ancestors.2 forward
            | inr reverse => cases target <;> cases reverse
        | inr common =>
            rcases common with ⟨child, childAncestor, rootParent, otherParent⟩
            cases child with
            | latentPair _ _ => cases rootParent
            | observed child =>
                have childInside := latentChildInside sourceInside childAncestor rootParent
                cases target with
                | observed parent =>
                    exact observedParentInside ancestors.2 openEnds.2.1
                      childInside childAncestor otherParent
                | latentPair first second => exact latentParentInside childInside otherParent
  -- A moral walk starting at the factor stays on the Boolean component side.
  -- Its supposed exchanged endpoint is outside that side, a direct finite
  -- Boolean contradiction; no shortest-path selection is involved.
  apply (G.dSeparated_eq_true_iff_no_moralReachable mutilation
    (NodeSet.singleton node) exchanged conditioned).mpr
  rintro ⟨source, target, sourceSelected, _sourceOpen, targetSelected, _targetOpen, reachable⟩
  have sourceSame := (NodeSet.singleton_eq_true_iff node source).mp sourceSelected
  subst source
  rcases (G.moralReachable_eq_true_iff mutilation targets conditioned
    (.observed node) (.observed target)).mp reachable with ⟨_length, _bound, walk⟩
  rcases walk with ⟨walk⟩
  have preserves {length : Nat} {source target : SeparationNode S}
      (walk : FiniteReachability.ExactWalk (G.MoralOpenEdge mutilation targets conditioned)
        length source target) (sourceInside : side source = true) : side target = true := by
    induction walk with
    | refl => exact sourceInside
    | step first _rest inductionHypothesis =>
        exact inductionHypothesis (moralClosed sourceInside first)
  have targetInside := preserves walk nodeInside
  have targetOutside := (Bool.and_eq_true_iff.mp targetSelected).2
  change Bool.not (component target) = true at targetOutside
  change component target = true at targetInside
  rw [targetInside] at targetOutside
  cases targetOutside

/-- The executable partition supplies all component premises of the
predecessor-exchange theorem.  In particular, callers do not need to prove
a fresh separation Boolean for each recursive ID branch. -/
theorem dSeparated_factor_outside_predecessors_of_mem
    (G : ObservedGraph S) (remaining externalAction : NodeSet S)
    (closed : KernelHostClosed G remaining externalAction)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining)
    (node : Fin S.count) (nodeInside : component node = true) :
    G.dSeparated
      (GraphMutilation.barUnderline externalAction
        (NodeSet.diff (chainCondition remaining node) component))
      (NodeSet.singleton node)
      (NodeSet.diff (chainCondition remaining node) component)
      (NodeSet.union externalAction (chainCondition component node)) = true :=
  G.dSeparated_factor_outside_predecessors remaining externalAction component
    closed (cComponents_subset G remaining listed)
    (G.cComponents_bidirected_closed remaining listed) node nodeInside

/-- The graph-derived rule-2 condition in the published active-path syntax.
It applies equally to a listed component or to a union of whole components;
only closure across host bidirected edges, not connectivity, is needed. -/
theorem pathDSeparated_rule2_outside_predecessors
    (G : ObservedGraph S) (remaining externalAction component : NodeSet S)
    (closed : KernelHostClosed G remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true ->
      remaining target = true -> G.bidirected source target = true ->
        component target = true)
    (node : Fin S.count) (nodeInside : component node = true) :
    PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline externalAction
        (NodeSet.diff (chainCondition remaining node) component))
      (NodeSet.singleton node)
      (NodeSet.diff (chainCondition remaining node) component)
      (NodeSet.union externalAction (chainCondition component node)) :=
  G.dSeparationCorrectness.pathDSeparated_of_dSeparated
    (G.dSeparated_factor_outside_predecessors remaining externalAction component
      closed componentSubset bidirectedClosed node nodeInside)

end ObservedGraph

end Causality
end Thesis
