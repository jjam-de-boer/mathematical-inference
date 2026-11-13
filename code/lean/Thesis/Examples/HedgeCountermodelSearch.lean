import Thesis.CausalTransport.HedgeCountermodelSearch
import Thesis.Examples.HedgeOutcomeNormalization

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeAlternativeSelection

open HedgeAncestralRerooting

/-!
# Alternative hedge search repairs disconnected ancestral normalization

Reuse the six-node, three-value fixture with actions `A,C`, outcome `Y`,
and bidirected edges `A ↔ R`, `A ↔ O`, `A ↔ C`, `R ↔ Q`.  Its original
hedge has small side `{R,Q}`, but its outcome-ancestral enlargement
`{R,O,Q}` is disconnected.  That failed normalization was not evidence
against every other hedge for this query.

A sufficient alternative has large side `{A,R,O}`, small side `{O}`,
and kept edges `A → R → O`.  Its only common root is `O`, whose canonical
readout `O → Y` leaves the large forest immediately.  Both forest tests and
the carrier-routing test are checked below.  Notice that even this smaller
large forest has disconnected full outcome-ancestral small side `{R,O}`:
the repair genuinely needs a smaller small side, not just large-set pruning.

The countermodel is obtained from the *search's* returned witness, not from
the supplied candidate.  The candidate proves that the finite search cannot
return `none`; an earlier accepted alternative is allowed.  The resulting
pair has all semantic fields for the original composite-action query and
the full three-value alphabets.  No conclusion about universal geometric
coverage is drawn from this regression.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- A bidirected-connected large forest ending at the former outer route
vertex.  The second intervened vertex is outside this hedge, but remains
in the original query's action set throughout the construction. -/
def prunedLarge : NodeSet signature := fun node => decide (node.val < 3)

/-- Select only `O`, not all action-free large ancestors of `Y`. -/
def prunedSmall : NodeSet signature := NodeSet.singleton outerRouteNode

/-- Change the old `R` sink into a kept parent of `O`; remove the old
`O → C` edge altogether.  Off-large entries remain `none`. -/
def prunedChild : ForestChild signature := fun parent => match parent.val with
  | 0 => some oldFirstRoot
  | 1 => some outerRouteNode
  | _ => none

def prunedSelection : HedgeSelection signature := ⟨prunedLarge, prunedSmall, prunedChild⟩

theorem pruned_hedge_tests : hedgeTestsHold connectivityObstructedGraph query prunedSelection = true :=
  by decide +kernel

theorem pruned_carrier_routes_ready :
    hedgeCarrierRoutesReady connectivityObstructedGraph query prunedSelection = true :=
  by decide +kernel

/-- The earlier normalization still fails even after shrinking this large
side.  Therefore the search must permit proper subsets of the computed
outcome-ancestral small set. -/
theorem pruned_full_ancestral_small_still_disconnected :
    connectivityObstructedGraph.isSingleCComponent
      (hedgeWitness_of_sets connectivityObstructedGraph query prunedSelection pruned_hedge_tests).outcomeAncestralSmall = false :=
  by decide +kernel

/-- The original forest map really fails the compensated routing test.
It routes its root `R` through outer-only `O`. -/
theorem original_selection_not_route_ready :
    hedgeCarrierRoutesReady connectivityObstructedGraph query (⟨large, small, child⟩ : HedgeSelection signature) = false :=
  by decide +kernel

/-- In this fixture the first ordinary extracted selection is unusable by
the carrier construction.  Checking readiness only *after* that search has
stopped would miss the alternative, which the filtered search can find. -/
theorem first_unfiltered_selection_not_route_ready :
    (match findHedgePair connectivityObstructedGraph query (NodeSet.members large) NodeSet.empty with
      | none => false
      | some selection => !hedgeCarrierRoutesReady connectivityObstructedGraph query selection) = true :=
  by decide +kernel

private theorem pruned_contained : NodeSet.Subset prunedSelection.large large := by
  intro node selected
  have beforeOutcome : node.val < 3 := of_decide_eq_true selected
  exact decide_eq_true (by omega : node.val ≠ 5)

/-- This follows from search completeness for all finite forest selections,
not from reducing one enormous concrete search expression. -/
theorem alternative_search_succeeds :
    Exists fun selected => carrierRouteHedgeWitness? connectivityObstructedGraph query large = some selected :=
  carrierRouteHedgeWitness?_eq_some_of_selection connectivityObstructedGraph query large
    prunedSelection pruned_contained pruned_hedge_tests pruned_carrier_routes_ready

/-- Concrete forest data comes from the finite Option result.  Existential
coverage is used only to eliminate the impossible `none` branch, without
extracting the candidate from `Prop` by choice. -/
def selectedWitness : CarrierRouteHedgeWitness connectivityObstructedGraph query :=
  carrierRouteHedgeWitnessOfSelectionExists connectivityObstructedGraph query large
    ⟨prunedSelection, pruned_contained, pruned_hedge_tests, pruned_carrier_routes_ready⟩

/-- The actual original-query positive pair is built from whatever usable
hedge the search returns.  Its action is still `{A,C}` and its outcome `Y`. -/
noncomputable def counterexample : CounterexampleIn (GraphModelClass.positive connectivityObstructedGraph) query :=
  selectedWitness.positiveCounterexample rich

theorem original_query_not_identifiable :
    Not ((GraphModelClass.positive connectivityObstructedGraph).identifiable query) :=
  counterexample.not_identifiable

private def failureTest (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed _ => true
  | _ => false

/-- The corrected joint engine also fails for this unchanged query.  This
checks the algorithmic side separately; the failure alone is not used as
an assumed semantic non-identifiability theorem. -/
theorem original_joint_program_fails :
    failureTest (identifyJointKernel connectivityObstructedGraph query) = true :=
  by decide +kernel

end HedgeAlternativeSelection
end Examples
end Causality
end Thesis
