import Thesis.CausalTransport.HedgeConditionalColliderRoute

namespace Thesis
namespace Causality
namespace Examples
namespace ConditionalReadoutRegression

open Probability

/-!
# Graph data for the conditional collider/readout regression

The topological order is `U,A,R,M,Y,E`, with `U -> R <- A`, `A <-> R`,
and the route `U -> M -> Y`.  The original query is `P(Y,E | do(A), R)`
and all observed alphabets have three labels.  Neither `U` nor `M` is queried.

This module certifies a hedge on the original numerator and the finite
root-specific incoming-route availability test.  The parent and path are
constructed by the general searches, not supplied as unrelated path data.
`ConditionalReadout` checks the actual positive countermodels.  Separate
companions retain the semantic IDC-failure bridge and exact forced-data
comparisons; neither is needed for the graph availability proof here.

Keeping graph computation separate from semantic checking lets each use a
fresh compiler process with the same resource limits; no statement is weakened.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signature : ObservedSignature where
  count := 6
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val < 2 ∧ child.val = 2) ∨ (parent.val = 0 ∧ child.val = 3) ∨
      (parent.val = 3 ∧ child.val = 4))
  directed_earlier := by intro parent child edge; have selected := of_decide_eq_true edge; omega

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right ∧ 1 ≤ left.val ∧ left.val < 3 ∧ 1 ≤ right.val ∧ right.val < 3)
  bidirected_symmetric := by
    intro left right edge
    have parts := of_decide_eq_true edge
    exact decide_eq_true ⟨Ne.symm parts.1, parts.2.2.2.1, parts.2.2.2.2, parts.2.1, parts.2.2.1⟩
  bidirected_irreflexive := by intro node; simp only [ne_eq, not_true_eq_false, false_and, decide_false]

def parent : Fin signature.count := ⟨0, by decide⟩
def actionNode : Fin signature.count := ⟨1, by decide⟩
def root : Fin signature.count := ⟨2, by decide⟩
def middle : Fin signature.count := ⟨3, by decide⟩
def outcome : Fin signature.count := ⟨4, by decide⟩
def extraOutcome : Fin signature.count := ⟨5, by decide⟩

def target : ConditionalKernelQuery signature where
  outcome := NodeSet.union (NodeSet.singleton outcome) (NodeSet.singleton extraOutcome)
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton root
  action_outcome_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := by intro _ same; have values := congrArg Fin.val same; cases values

def large : NodeSet signature := fun node => decide (1 ≤ node.val ∧ node.val < 3)
def small : NodeSet signature := NodeSet.singleton root
def child : ForestChild signature := fun node => if node = actionNode then some root else none
def selection : HedgeSelection signature := ⟨large, small, child⟩

theorem hedge_tests : hedgeTestsHold graph target.jointNumerator selection = true := by decide +kernel

def witness : HedgeWitness graph target.jointNumerator :=
  hedgeWitness_of_sets graph target.jointNumerator selection hedge_tests

theorem roots_are_root : witness.roots = NodeSet.singleton root :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

/-! ## The actual graph-selected auxiliary route -/

/-- Only the root fixed by the original conditioner needs this graph test.
Its parent and path are nevertheless returned by the general finite searches,
not asserted by the fixture as independent Type-level data. -/
theorem routes_available (node : Fin signature.count) (selected : witness.roots node = true) :
    NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.incomingRouteParentMask witness node) = true := by
  have same : node = root := (NodeSet.singleton_eq_true_iff root node).mp
    ((congrFun roots_are_root node).symm.trans selected)
  subst node
  decide +kernel

def geometry : HedgeConditionalRoot.IncomingRoute witness root :=
  HedgeConditionalRoot.incomingRoute witness roots_are_root root (routes_available root (by decide +kernel))

end ConditionalReadoutRegression
end Examples
end Causality
end Thesis
