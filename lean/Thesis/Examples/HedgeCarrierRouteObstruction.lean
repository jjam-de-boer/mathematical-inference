import Thesis.CausalTransport.HedgeCountermodelSearch
import Thesis.CausalTransport.HedgeOutcomeNormalization
import Thesis.Causality.IdentificationKernel

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeCarrierRouteObstruction

/-!
# Route-ready alternative hedges do not cover every valid hedge

The topological order is `A,R,U,V,B,Q,Y`.  The directed graph contains
`A → V → B → Q → Y`, `R → U → V`, and `V → Y`; the bidirected graph
contains `A ↔ R ↔ Q` and `A ↔ B ↔ V`.  The query is `P(Y | do(A,B))`.
Both `U` and `Y` are isolated in the bidirected graph.

There is a valid hedge with large side `{A,R,V,B,Q}`, small side `{R,Q}`,
and kept chain `A → V → B → Q`.  Its common roots are `R,Q`.  The root
`R` reaches the outcome along the incoming-cut path `R → U → V → Y`,
which visits outer-only `V` after leaving the large forest through `U`.
The new normalization's small side `{R,V,Q}` is disconnected.

More importantly, the complete full-graph alternative-hedge scan returns
`none`, even with the more permissive test that allows arbitrary directed
routes instead of the canonical ones.  Its candidate-completeness theorem therefore refutes
`CarrierRouteHedgeCoverage` for this graph, including all other large and
small selections and kept maps.  The corrected joint engine also fails on
the same query.  This is a limitation of the compensated routing family,
not proof that the query is identifiable or a refutation of the published
hedge non-identifiability theorem.

Keeping this negative regression prevents an impossible universal route-
coverage lemma from becoming the next completeness milestone.  It points
to the genuine remaining requirement: a positive countermodel construction
that can handle this outer-only re-entry, or a different complete family.
The observed alphabets are three-valued, as in the positive regressions;
the obstruction itself is purely finite graph data.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signature : ObservedSignature where
  count := 7
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 3) ∨ (parent.val = 1 ∧ child.val = 2) ∨
      (parent.val = 2 ∧ child.val = 3) ∨ (parent.val = 3 ∧ (child.val = 4 ∨ child.val = 6)) ∨
      (parent.val = 4 ∧ child.val = 5) ∨ (parent.val = 5 ∧ child.val = 6))
  directed_earlier := by
    intro parent child edge
    have selected := of_decide_eq_true edge
    omega

def graph : ObservedGraph signature where
  bidirected := fun left right => decide
    ((left.val = 0 ∧ (right.val = 1 ∨ right.val = 4)) ∨
      (right.val = 0 ∧ (left.val = 1 ∨ left.val = 4)) ∨
      (left.val = 1 ∧ right.val = 5) ∨ (right.val = 1 ∧ left.val = 5) ∨
      (left.val = 4 ∧ right.val = 3) ∨ (right.val = 4 ∧ left.val = 3))
  bidirected_symmetric := by
    intro left right edge
    simpa only [and_comm, or_comm, or_left_comm, or_assoc] using edge
  bidirected_irreflexive := by
    intro node
    apply decide_eq_false
    omega

def firstAction : Fin signature.count := ⟨0, by decide⟩
def firstRoot : Fin signature.count := ⟨1, by decide⟩
def outsideRelay : Fin signature.count := ⟨2, by decide⟩
def outerReentry : Fin signature.count := ⟨3, by decide⟩
def secondAction : Fin signature.count := ⟨4, by decide⟩
def lastRoot : Fin signature.count := ⟨5, by decide⟩
def outcome : Fin signature.count := ⟨6, by decide⟩

def action : NodeSet signature := fun node => decide (node.val = 0 ∨ node.val = 4)
def query : JointKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := action
  action_outcome_disjoint := (NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel)

def large : NodeSet signature := fun node => decide (node.val ≠ 2 ∧ node.val ≠ 6)
def small : NodeSet signature := fun node => decide (node.val = 1 ∨ node.val = 5)
def child : ForestChild signature := fun parent => match parent.val with
  | 0 => some outerReentry
  | 3 => some secondAction
  | 4 => some lastRoot
  | _ => none
def selection : HedgeSelection signature := ⟨large, small, child⟩

/-- All forest, action, child-closure, and original-outcome reachability
requirements hold.  In particular this is not malformed hedge data rejected
before the routing question even arises. -/
theorem hedge_tests : hedgeTestsHold graph query selection = true := by decide +kernel

def witness : HedgeWitness graph query := hedgeWitness_of_sets graph query selection hedge_tests

/-- The readout actually visits `V`, which is in the large but not the
small forest.  It does so after the unconfounded relay `U`. -/
theorem outer_only_reentry :
    witness.rootReadoutNodes outerReentry = true ∧ witness.large outerReentry = true ∧
      witness.small outerReentry = false := by decide +kernel

theorem normalization_small_disconnected :
    graph.isSingleCComponent witness.outcomeAncestralSmall = false := by decide +kernel

/-- This is the complete finite scan over the full seven-node graph.  The
kernel checks its Boolean result; no native reduction axiom or classical
function equality is used to compare the returned forest data. -/
theorem full_selection_scan_is_empty :
    (findCarrierRouteHedgeSelection graph query NodeSet.full).isSome = false := by decide +kernel

/-- Recover the Option equation from its checked Boolean test by cases.
No decidable equality on function-valued forest records is needed. -/
theorem full_selection_scan_returns_none :
    findCarrierRouteHedgeSelection graph query NodeSet.full = none := by
  cases found : findCarrierRouteHedgeSelection graph query NodeSet.full with
  | none => rfl
  | some selected =>
      have impossible := full_selection_scan_is_empty
      rw [found] at impossible
      cases impossible

/-- Universal route-ready coverage is false even though a valid hedge
exists.  Search completeness, not a heuristic failure, supplies the refutation. -/
theorem no_carrier_route_coverage : Not (CarrierRouteHedgeCoverage graph) :=
  not_carrierRouteHedgeCoverage_of_search_none graph query witness full_selection_scan_returns_none

/-- Allow every possible incoming-cut route rather than the canonical
first-outcome, first-successor policy.  The complete scan still has no result,
so route tie-breaking alone cannot repair this example. -/
theorem arbitrary_route_selection_scan_is_empty :
    (findHedgeSelectionWhere graph query NodeSet.full (hedgeCarrierRoutesPossible query)).isSome = false :=
  by decide +kernel

private theorem arbitrary_route_selection_scan_returns_none :
    findHedgeSelectionWhere graph query NodeSet.full (hedgeCarrierRoutesPossible query) = none := by
  cases found : findHedgeSelectionWhere graph query NodeSet.full (hedgeCarrierRoutesPossible query) with
  | none => rfl
  | some selected =>
      have impossible := arbitrary_route_selection_scan_is_empty
      rw [found] at impossible
      cases impossible

/-- Every valid alternative hedge lacks an all-root family of paths that
avoids its outer-only vertices.  This is a policy-independent graph theorem,
not just failure of one implementation's canonical route selection. -/
theorem no_outer_avoiding_routes_for_any_hedge_selection
    (candidate : HedgeSelection signature) (valid : hedgeTestsHold graph query candidate = true) :
    Not (forall root, keptSinks candidate.large candidate.child root = true ->
      Exists fun target => query.outcome target = true ∧
        DirectedReachableBy signature
          (fun parent child => mutilatedDirected signature
            (NodeSet.union query.action (NodeSet.diff candidate.large candidate.small)) parent child = true)
          root target) := by
  intro paths
  have possible := (hedgeCarrierRoutesPossible_iff query candidate).mpr paths
  have impossible := findHedgeSelectionWhere_none_excludes_selection graph query NodeSet.full
    (hedgeCarrierRoutesPossible query) arbitrary_route_selection_scan_returns_none candidate
    (fun _node _selected => rfl) valid
  rw [possible] at impossible
  cases impossible

private def failureTest (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed _ => true
  | _ => false

/-- The corrected ID program has a real failure on the same query.  This
does not replace the still-needed positive semantic countermodel argument. -/
theorem original_joint_program_fails :
    failureTest (identifyJointKernel graph query) = true := by decide +kernel

end HedgeCarrierRouteObstruction
end Examples
end Causality
end Thesis
