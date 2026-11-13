import Thesis.CausalTransport.HedgeInterventionalSupport
import Thesis.Examples.HedgeReadoutPullback

namespace Thesis
namespace Causality
namespace Examples
namespace HedgePartialInterventionalSupport

open Probability
open HedgeMergedReadout

/-!
# Partial incidence and fixed-defect support on an actual two-root hedge

The existing merging fixture extracts a hedge with large vertices
`X,R₁,R₂`, small vertices `R₁,R₂`, and original queried outcome `Y`.
These checks retain that extracted witness rather than manually replacing
it by a one-root forest.

The ordinary partial test inspects only `R₁`; the action vertex absorbs its
odd requested incidence.  The nested test inspects both `X` and `R₁`, so it
includes an outer vertex as well as an inner one.  Its missing inner vertex
`R₂` absorbs the inner parity constraint.  In both maps the uncorrected
target has odd incidence on the respective complete component: the old
complete-target solver cannot be invoked on it without a correction.

Finally, under the original `do(X = second)` intervention the large carrier
has positive mass at the complete all-second target jointly with either
private defect bit.  That target has even common-root parity, so the true
defect stratum would be impossible in the observational small root-parity
construction.  These checks exercise the new interventional section, not
the old observational one.  They assert neither a common conditional
denominator nor a completed original-outcome countermodel theorem.
The final pointwise check also compensates a defect flip at arbitrary pair
and background coordinates, retaining equality of the entire evaluated
assignment under the original action rather than merely its root bits.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def firstRootTest : NodeSet signature := NodeSet.singleton firstRoot
def outerAndFirstRootTest : NodeSet signature := fun node => decide (node.val = 0 ∨ node.val = 1)
def oddIncidence : Fin signature.count -> Bool := fun node => decide (node = firstRoot)

private theorem firstRootTest_subset : NodeSet.Subset firstRootTest extraction.witness.large := by
  rw [extraction.large_eq]
  change forall node : Fin signature.count, firstRootTest node = true -> forestHost node = true
  decide +kernel

private theorem outerAndFirstRootTest_subset :
    NodeSet.Subset outerAndFirstRootTest extraction.witness.large := by
  rw [extraction.large_eq]
  change forall node : Fin signature.count, outerAndFirstRootTest node = true -> forestHost node = true
  decide +kernel

private theorem action_in_large : extraction.witness.large actionNode = true := by
  rw [extraction.large_eq]
  decide +kernel

private theorem secondRoot_in_small : extraction.witness.small secondRoot = true := by
  rw [extraction.small_eq]
  decide +kernel

/-- The raw target violates the full large-component parity condition;
the omitted action equation is therefore a genuine source of extra freedom. -/
theorem odd_large_incidence :
    (hedgeTrueVertices extraction.witness.large oddIncidence).length % 2 = 1 := by
  rw [extraction.large_eq]
  decide +kernel

theorem odd_inner_incidence :
    (hedgeTrueVertices extraction.witness.small oddIncidence).length % 2 = 1 := by
  rw [extraction.small_eq]
  decide +kernel

noncomputable def ordinaryPairBits := extraction.witness.large_forest.component.partialTargetPairBits
  graph extraction.witness.large actionNode action_in_large oddIncidence

theorem ordinary_realizes :
    hedgePartialPairBitsRealizes graph extraction.witness.large firstRootTest oddIncidence ordinaryPairBits = true :=
  hedgePartialPairBitsRealizes_of graph extraction.witness.large firstRootTest oddIncidence ordinaryPairBits
    (extraction.witness.large_forest.component.partialTargetPairBits_spec graph extraction.witness.large
      firstRootTest firstRootTest_subset actionNode action_in_large (by decide +kernel) oddIncidence)

/-- An odd partial pattern and the zero pattern have exactly equal fibre
sizes.  No numerical cardinality or evenness premise is passed to the theorem. -/
theorem ordinary_fibres_equal :
    ((hedgePairBitEnum graph).filter
      (hedgePartialPairBitsRealizes graph extraction.witness.large firstRootTest oddIncidence)).length =
      ((hedgePairBitEnum graph).filter
        (hedgePartialPairBitsRealizes graph extraction.witness.large firstRootTest (fun _ => false))).length :=
  extraction.witness.large_forest.component.partialPairBitRealizers_length_eq graph extraction.witness.large
    firstRootTest firstRootTest_subset actionNode action_in_large (by decide +kernel) oddIncidence (fun _ => false)

noncomputable def nestedPairBits := extraction.witness.large_forest.component.partialNestedTargetPairBits
  graph extraction.witness.large extraction.witness.small extraction.witness.small_forest.component
  extraction.witness.small_subset_large secondRoot secondRoot_in_small oddIncidence

/-- The nested test retains a real outer equation at `X`; it does not
reduce the tested set to a subset of the small forest. -/
theorem nested_realizes :
    hedgePartialNestedPairBitsRealizes graph extraction.witness.large extraction.witness.small
      outerAndFirstRootTest oddIncidence nestedPairBits = true :=
  hedgePartialNestedPairBitsRealizes_of graph extraction.witness.large extraction.witness.small
    outerAndFirstRootTest oddIncidence nestedPairBits
    (extraction.witness.large_forest.component.partialNestedTargetPairBits_spec graph
      extraction.witness.large extraction.witness.small outerAndFirstRootTest
      extraction.witness.small_forest.component extraction.witness.small_subset_large outerAndFirstRootTest_subset
      secondRoot secondRoot_in_small (by decide +kernel) oddIncidence)

theorem nested_fibres_equal :
    ((hedgePairBitEnum graph).filter (hedgePartialNestedPairBitsRealizes graph extraction.witness.large
      extraction.witness.small outerAndFirstRootTest oddIncidence)).length =
      ((hedgePairBitEnum graph).filter (hedgePartialNestedPairBitsRealizes graph extraction.witness.large
        extraction.witness.small outerAndFirstRootTest (fun _ => false))).length :=
  extraction.witness.large_forest.component.partialNestedPairBitRealizers_length_eq graph
    extraction.witness.large extraction.witness.small outerAndFirstRootTest
    extraction.witness.small_forest.component extraction.witness.small_subset_large outerAndFirstRootTest_subset
    secondRoot secondRoot_in_small (by decide +kernel) oddIncidence (fun _ => false)

/-- One consistent complete target, including the original action value
and all non-forest private labels. -/
def target : signature.Assignment := rich.second

theorem target_root_parity_even : hedgeRootParityEvent rich extraction.witness.roots target = false := by
  rw [extracted_roots]
  decide +kernel

/-- Both defect strata have genuine positive mass under the original
intervention.  This theorem is not obtained by mixing defect values after
selecting the observational target's parity. -/
theorem target_each_defect_positive (defect : Bool) :
    (extraction.witness.largeCarrierDefectParityModel rich).prior.EventPositive (fun unit =>
      (hedgeDefectBitOf graph unit == defect) && FiniteProbRecord.singletonEvent target
        ((extraction.witness.largeCarrierDefectParityModel rich).evalUnder
          (hedgeDoSecond rich query.action) unit)) :=
  extraction.witness.largeCarrierDefectParityModel_doSecond_target_defect_positive rich target
    (fun _node _selected => rfl) defect

/-- The compensation theorem applies to the complete original-action
evaluation at every pair-root vector and every private-background vector.
No target-specific realization or equality of observed laws is passed in. -/
theorem original_action_defect_compensation
    (pairBits : Fin (pairRootCount graph) -> Bool) (backgrounds : HedgePrivateCoordinates signature)
    (defect : Bool) :
    (extraction.witness.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich query.action)
        (hedgeDefectAssignment graph (hedgeLatentOfCoordinates graph pairBits backgrounds) defect) =
      (extraction.witness.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich query.action)
        (hedgeDefectAssignment graph (hedgeLatentOfCoordinates graph
          (hedgePairBitsXor graph pairBits
            (extraction.witness.largeCarrierDefectCompensation extraction.witness.actionSeed
              extraction.witness.actionSeed_in_large)) backgrounds) (!defect)) := by
  apply extraction.witness.largeCarrierDefectParityModel_evalUnder_compensate_defect rich
    extraction.witness.actionSeed extraction.witness.actionSeed_in_large
  rw [hedgeDoSecond_of_true rich query.action extraction.witness.actionSeed_in_action]
  exact Option.some_ne_none _

end HedgePartialInterventionalSupport
end Examples
end Causality
end Thesis
