import Thesis.CausalTransport.ConditionalFailureFlow
import Thesis.Examples.ConditionalFailurePivot

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureFlow

open Probability HedgeChannelInstallation

/-!
# Whole-route balance and the exhaustive conditional-flow split

The first fixture has two small-forest roots whose readouts merge before the
queried outcome.  Its selected action root travels along `R -> M -> Y`, while
the other root also points into `M` but is off that displayed path.  The flow
sink `Y` is outside Small, so the older singleton-small-sink constructor cannot
be used.  The new path indicator makes `R` the only odd source and keeps the
actual merged background row even.  An isolated original conditioner remains
fixed, and the generic construction supplies a positive original-label pair.

Only graph paths, bits, and the outer finite classification are reduced here.
The complete likelihood and original-alphabet model prior are not enumerated.
A separate negative check inspects the intermediate `M`: the endpoint is still
omitted, but the path direction no longer fixes that inspected set.  This guards
against replacing whole-path freedom by an endpoint-only assumption.

The existing genuine collider failure exercises the other classification
branch, which returns a latest reachable conditioner.  That branch still
requires the universal graph-to-parity countermodel argument.
-/

/-! ## A non-singleton small forest with genuinely merging readouts -/

/-- `A(0) -> R(1)`, `R,S(2) -> M(3) -> Y(4)`, isolated `E(5)`.
The two genuine bidirected edges are `A <-> R` and `R <-> S`. -/
def signature : ObservedSignature where
  count := 6
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 1) ∨
      (1 ≤ parent.val ∧ parent.val ≤ 2 ∧ child.val = 3) ∨
      (parent.val = 3 ∧ child.val = 4))
  directed_earlier := by
    intro parent child edge
    have endpoints := of_decide_eq_true edge
    omega

def actionNode : Fin signature.count := ⟨0, by decide⟩
def sourceNode : Fin signature.count := ⟨1, by decide⟩
def otherRoot : Fin signature.count := ⟨2, by decide⟩
def mergeNode : Fin signature.count := ⟨3, by decide⟩
def outcomeNode : Fin signature.count := ⟨4, by decide⟩
def conditionNode : Fin signature.count := ⟨5, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun left right => decide
    ((left.val = 1 ∧ (right.val = 0 ∨ right.val = 2)) ∨
      (right.val = 1 ∧ (left.val = 0 ∨ left.val = 2)))
  bidirected_symmetric := by
    intro left right edge
    have selected := of_decide_eq_true edge
    exact decide_eq_true (selected.elim Or.inr Or.inl)
  bidirected_irreflexive := by
    intro node
    apply decide_eq_false
    intro selected
    omega

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton conditionNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def selection : HedgeSelection signature where
  large := fun node => decide (node.val ≤ 2)
  small := fun node => decide (1 ≤ node.val ∧ node.val ≤ 2)
  child := fun node => if node = actionNode then some sourceNode else none

def witness : HedgeWitness graph query.jointNumerator :=
  hedgeWitness_of_sets graph query.jointNumerator selection (by decide +kernel)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := by intro _ equal; have values := congrArg Fin.val equal; cases values

def flowPath := witness.sourceOutcomeFlowPath

theorem actual_route_codes : flowPath.nodes.map Fin.val = [1, 3, 4] := by decide +kernel

/-- The other genuine root merges at `M` but is not on the selected source's
path.  Its false bit is retained in the actual incoming XOR, not deleted from
the successor map or treated as a duplicated source. -/
theorem actual_merge_and_outside_small_sink :
    witness.smallOutcomeFlowSuccessor otherRoot = some mergeNode ∧
    otherRoot ∉ flowPath.nodes ∧ witness.small flowPath.endpoint = false := by
  decide +kernel

private theorem route_condition_free : forall node, node ∈ flowPath.nodes -> query.condition node = false := by
  decide +kernel

def direction : OutcomeFlowBalanceDirection witness query.condition :=
  .ofPath witness query.condition witness.actionRoot witness.actionRoot_in_small flowPath route_condition_free

/-- The original root, intermediate background and actual queried outcome
are all flipped; the off-path small root is false.  The action and isolated
original conditioner remain fixed. -/
theorem actual_direction_bits :
    direction.bits actionNode = false ∧ direction.bits sourceNode = true ∧
    direction.bits otherRoot = false ∧ direction.bits mergeNode = true ∧
    direction.bits outcomeNode = true ∧ direction.bits conditionNode = false := by
  decide +kernel

theorem actual_local_sources (node : Fin signature.count) :
    hedgeRoutingLocalSource witness.smallOutcomeFlowSuccessor direction.bits node = decide (node = witness.actionRoot) :=
  flowPath.bits_localSource node

/-- A positive three-valued countermodel pair from whole-route balance.
The generic constructor proves complete conditioning-marginal equality and
the original query gap; no concrete likelihood cells are supplied. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfBalanceDirection query witness rich direction

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

/-- Inspecting the intermediate vertex invalidates this direction even
though the path's endpoint remains omitted.  This is a boundary check on the
path constructor, not a claim of identifiability for another conditional. -/
theorem endpoint_omission_does_not_fix_the_whole_route :
    NodeSet.singleton mergeNode flowPath.endpoint = false ∧ direction.bits mergeNode = true := by
  decide +kernel

/-! ## Both outer classification branches are genuinely exercised -/

private def counterexampleCase {left : Type _} {right : Type _} : Sum left right -> Bool
  | .inl _ => true
  | .inr _ => false

/-- Only the outer finite tag is computed; the returned model pair is not
evaluated.  This branch is backed by the semantic countermodel above. -/
theorem free_route_returns_counterexample :
    counterexampleCase (witness.conditionalCounterexampleOrLatestPivot rich) = true := by
  decide +kernel

/-- The real irreducible collider's source is already conditioned, so the
same general classifier returns normalized graph data, not a falsely claimed
balance direction.  No all-sinks-inspected premise is passed to the classifier. -/
theorem conditioned_route_returns_latest_pivot :
    counterexampleCase (ConditionalColliderRegression.witness.conditionalCounterexampleOrLatestPivot
      ConditionalColliderRegression.rich) = false := by
  decide +kernel

end CurrentConditionalFailureFlow
end Examples
end Causality
end Thesis
