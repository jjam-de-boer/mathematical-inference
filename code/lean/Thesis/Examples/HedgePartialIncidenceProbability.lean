import Thesis.CausalTransport.HedgePartialIncidenceProbability
import Thesis.Examples.HedgeInterventionalSupport
import Thesis.Examples.HedgeInterventionalProbability

namespace Thesis
namespace Causality
namespace Examples

open Probability

/-!
# Cross-map partial fibres and their actual weighted prior masses

The merging fixture retains an outer action row and one inner root row while
omitting the other inner root.  We compare different ordinary/nested targets,
not just two targets of the same incidence map.  A weighted check allows both
targets and an arbitrary common private-background predicate to depend on the
defect.  Its probabilities use the original augmented prior.

A negative boundary check retains every forest row instead.  Incidence one
only at the outer action has odd complete outer parity but even inner parity:
the ordinary map cannot realize it, whereas the nested map can.  Thus the
missing-inner-row hypothesis cannot be silently dropped from the cross-map
theorem.  This is a mathematical boundary check, not a failure-depth unpacker.

The final check uses the extracted three-value fixture's actual private
coordinate enumeration.  Requiring the first and last backgrounds both to
be the third label leaves exactly three choices for the middle background.
The product-count theorem retains that multiplicity under either defect
weight; it does not collapse the private block to Boolean labels.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace HedgeWeightedPartialMerged

open HedgeMergedReadout
open HedgePartialInterventionalSupport

private theorem tested_subset : NodeSet.Subset outerAndFirstRootTest extraction.witness.large := by
  rw [extraction.large_eq]
  change forall node : Fin signature.count, outerAndFirstRootTest node = true -> forestHost node = true
  decide +kernel

private theorem balance_inside : extraction.witness.small secondRoot = true := by
  rw [extraction.small_eq]
  decide +kernel

/-- The tested rows include both the outer action and an inner root.  An
odd ordinary target and a zero nested target have exactly equal fibre sizes. -/
theorem different_partial_map_fibres_equal :
    ((hedgePairBitEnum graph).filter (hedgePartialPairBitsRealizes graph extraction.witness.large
      outerAndFirstRootTest oddIncidence)).length =
      ((hedgePairBitEnum graph).filter (hedgePartialNestedPairBitsRealizes graph extraction.witness.large
        extraction.witness.small outerAndFirstRootTest (fun _ => false))).length :=
  extraction.witness.large_forest.component.partialPairBitRealizers_length_eq_nested graph
    extraction.witness.large extraction.witness.small outerAndFirstRootTest extraction.witness.small_forest.component
    extraction.witness.small_subset_large tested_subset secondRoot balance_inside (by decide +kernel)
    oddIncidence (fun _ => false)

/-- Exact weighted comparison, with no supplied support cardinality or
singleton-mass equivalence.  The private predicate may couple arbitrary old
background coordinates; only its use on both sides must be identical. -/
theorem weighted_partial_incidence_probabilities_equal
    (largeTarget nestedTarget : Bool -> Fin signature.count -> Bool)
    (privateTest : Bool -> HedgePrivateCoordinates signature -> Bool) :
    QProb.Equiv
      ((hedgeDefectPrior graph).probVal (hedgePartialIncidenceLatentEvent graph extraction.witness.large
        outerAndFirstRootTest largeTarget privateTest))
      ((hedgeDefectPrior graph).probVal (hedgePartialNestedIncidenceLatentEvent graph extraction.witness.large
        extraction.witness.small outerAndFirstRootTest nestedTarget privateTest)) :=
  extraction.witness.large_forest.component.partialIncidence_probVal_equiv_nested graph
    extraction.witness.large extraction.witness.small outerAndFirstRootTest extraction.witness.small_forest.component
    extraction.witness.small_subset_large tested_subset secondRoot balance_inside (by decide +kernel)
    largeTarget nestedTarget privateTest

def actionOnlyIncidence (node : Fin signature.count) : Bool := decide (node = actionNode)

private theorem action_only_outer_odd :
    (hedgeTrueVertices extraction.witness.large actionOnlyIncidence).length % 2 = 1 := by
  rw [extraction.large_eq]
  decide +kernel

private theorem action_only_inner_even :
    (hedgeTrueVertices extraction.witness.small actionOnlyIncidence).length % 2 = 0 := by
  rw [extraction.small_eq]
  decide +kernel

/-- Keeping every outer equation makes this ordinary target impossible. -/
theorem complete_ordinary_target_impossible (pairBits : Fin (pairRootCount graph) -> Bool) :
    hedgePartialPairBitsRealizes graph extraction.witness.large extraction.witness.large
      actionOnlyIncidence pairBits = false := by
  apply Bool.eq_false_iff.mpr
  intro selected
  have full := hedgePairBitsRealizes_of graph extraction.witness.large actionOnlyIncidence pairBits
    (hedgePartialPairBitsRealizes_spec graph extraction.witness.large extraction.witness.large
      actionOnlyIncidence pairBits selected)
  have even := hedgePairBitsRealizes_even graph extraction.witness.large actionOnlyIncidence pairBits full
  have odd := action_only_outer_odd
  omega

noncomputable def completeNestedPairBits := extraction.witness.large_forest.component.nestedEvenTargetPairBits
  graph extraction.witness.large extraction.witness.small extraction.witness.small_forest.component
  extraction.witness.small_subset_large actionOnlyIncidence action_only_inner_even

/-- The same complete target is realizable in the nested map.  Together
with the preceding theorem this checks why the omitted inner row is essential. -/
theorem complete_nested_target_realized :
    hedgePartialNestedPairBitsRealizes graph extraction.witness.large extraction.witness.small
      extraction.witness.large actionOnlyIncidence completeNestedPairBits = true :=
  hedgePartialNestedPairBitsRealizes_of graph extraction.witness.large extraction.witness.small
    extraction.witness.large actionOnlyIncidence completeNestedPairBits
    (extraction.witness.large_forest.component.nestedEvenTargetPairBits_spec graph
      extraction.witness.large extraction.witness.small extraction.witness.small_forest.component
      extraction.witness.small_subset_large actionOnlyIncidence action_only_inner_even)

end HedgeWeightedPartialMerged

namespace HedgeWeightedPartialTernary

open HedgeWeightedTernaryIntervention

/-- A coupled private test involving a genuine nonbinary background label.
The middle coordinate is unrestricted, so all of its three labels remain. -/
def privateTest (backgrounds : HedgePrivateCoordinates signature) : Bool :=
  (backgrounds balance).val == 2 && (backgrounds balance).val == (backgrounds outcome).val

theorem private_test_multiplicity :
    ((hedgePrivateCoordinateEnum signature).filter privateTest).length = 3 := by decide +kernel

/-- The exact old-assignment count retains the three allowed private
background vectors for every member of an arbitrary pair-root event. -/
theorem old_count_retains_nonbinary_multiplicity
    (pairTest : (Fin (pairRootCount graph) -> Bool) -> Bool) :
    ((hedgeLatentAssignmentEnum graph).filter (fun old =>
      pairTest (hedgePairBitsOf graph old) && privateTest (hedgePrivateCoordinatesOf graph old))).length =
      ((hedgePairBitEnum graph).filter pairTest).length * 3 := by
  rw [hedgeLatentAssignmentEnum_filter_pair_private_length, private_test_multiplicity]

end HedgeWeightedPartialTernary
end Examples
end Causality
end Thesis
