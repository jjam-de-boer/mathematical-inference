import Thesis.CausalTransport.HedgePartialIncidenceComparison
import Thesis.CausalTransport.HedgeInterventionalProbability

namespace Thesis
namespace Causality

open Probability

/-!
# Weighted probability comparison of partial incidence events

The ordinary/nested fibre comparison concerns pair bits, whereas the real
carrier prior also contains dependent private background coordinates and a
biased defect.  This module lifts the comparison to that unchanged prior.

First we factor the number of old assignments satisfying separate pair and
private tests.  Both tests may be arbitrary Boolean predicates on their whole
coordinate blocks; in particular the private test need not be rectangular or
restricted to the two parity labels.  The explicit Cartesian enumeration and
coordinate recovery give the exact product count.  The fixed-defect mass
formula from `HedgeInterventionalProbability` then includes the actual weight
two or one.  Applying the cross-map pair-fibre theorem in each defect stratum
and summing the disjoint strata proves an equality of natural event masses.

The incidence targets and common private test may themselves depend on the
defect, as required when a structural equation XORs that defect at a root.
This is an equality under the original weighted prior, not an unweighted
analogue substituted for it.  The final events are still *incidence* events:
a countermodel denominator must additionally be shown to pull back to these
tests through actual interventional SCM evaluation.
-/

/-! ## Arbitrary separate tests on the old coordinate blocks -/

/-- Actual old latent assignments satisfying one pair-block test and one
private-block test.  Both finite lists retain their constructive exhaustive
enumerations; no witness family is selected from a proposition. -/
def hedgeCoordinatePredicateSupport (G : ObservedGraph S)
    (pairTest : (Fin (pairRootCount G) -> Bool) -> Bool)
    (privateTest : HedgePrivateCoordinates S -> Bool) :
    List (hedgeLatentExtension G).Assignment :=
  (ConstructivePermutation.pairList ((hedgePairBitEnum G).filter pairTest)
    ((hedgePrivateCoordinateEnum S).filter privateTest)).map (hedgeLatentOfCoordinatePair G)

/-- Filtered coordinate enumerations are duplicate-free, and recovery of
both blocks makes their reassembly injective.  Each actual old assignment is
therefore counted once, not once for each presentation of its coordinates. -/
theorem hedgeCoordinatePredicateSupport_nodup (G : ObservedGraph S)
    (pairTest : (Fin (pairRootCount G) -> Bool) -> Bool)
    (privateTest : HedgePrivateCoordinates S -> Bool) :
    (hedgeCoordinatePredicateSupport G pairTest privateTest).Nodup := by
  unfold hedgeCoordinatePredicateSupport
  apply nodup_map_of_injective
  · intro left right equal
    exact hedgeLatentOfCoordinatePair_injective G equal
  · exact ConstructivePermutation.pairList_nodup _ _
      (List.Sublist.nodup List.filter_sublist (hedgePairBitEnum_nodup G))
      (List.Sublist.nodup List.filter_sublist (hedgePrivateCoordinateEnum_nodup S))

/-- Coordinate reconstruction gives an exact support description, including
private predicates that couple several background labels to each other. -/
theorem hedgeCoordinatePredicateSupport_mem_iff (G : ObservedGraph S)
    (pairTest : (Fin (pairRootCount G) -> Bool) -> Bool)
    (privateTest : HedgePrivateCoordinates S -> Bool)
    (old : (hedgeLatentExtension G).Assignment) :
    old ∈ hedgeCoordinatePredicateSupport G pairTest privateTest ↔
      pairTest (hedgePairBitsOf G old) = true ∧
        privateTest (hedgePrivateCoordinatesOf G old) = true := by
  constructor
  · intro listed
    rcases List.mem_map.mp listed with ⟨coordinates, coordinatesListed, equal⟩
    have parts := (ConstructivePermutation.mem_pairList coordinates.1 coordinates.2 _ _).mp coordinatesListed
    have pairSelected := (List.mem_filter.mp parts.1).2
    have privateSelected := (List.mem_filter.mp parts.2).2
    rw [← equal]
    simpa only [hedgeLatentOfCoordinatePair, hedgePairBitsOf_latentOfCoordinates,
      hedgePrivateCoordinatesOf_latentOfCoordinates] using And.intro pairSelected privateSelected
  · intro selected
    apply List.mem_map.mpr
    refine ⟨(hedgePairBitsOf G old, hedgePrivateCoordinatesOf G old), ?_, hedgeLatentOfCoordinates_recover G old⟩
    apply (ConstructivePermutation.mem_pairList _ _ _ _).mpr
    exact ⟨List.mem_filter.mpr ⟨hedgePairBitEnum_complete G _, selected.1⟩,
      List.mem_filter.mpr ⟨hedgePrivateCoordinateEnum_complete S _, selected.2⟩⟩

/-- The old product coordinates factor at the level of exact finite support
counts.  This theorem does not presume a probability independence law: the
Cartesian support and its duplicate-free reassembly prove the count directly. -/
theorem hedgeLatentAssignmentEnum_filter_pair_private_length (G : ObservedGraph S)
    (pairTest : (Fin (pairRootCount G) -> Bool) -> Bool)
    (privateTest : HedgePrivateCoordinates S -> Bool) :
    ((hedgeLatentAssignmentEnum G).filter
        (fun old => pairTest (hedgePairBitsOf G old) && privateTest (hedgePrivateCoordinatesOf G old))).length =
      ((hedgePairBitEnum G).filter pairTest).length *
        ((hedgePrivateCoordinateEnum S).filter privateTest).length := by
  let support := hedgeCoordinatePredicateSupport G pairTest privateTest
  have permutation : ((hedgeLatentAssignmentEnum G).filter
      (fun old => pairTest (hedgePairBitsOf G old) && privateTest (hedgePrivateCoordinatesOf G old))).Perm support := by
    apply ConstructivePermutation.perm_of_nodup_mem_iff
    · exact List.Sublist.nodup List.filter_sublist (hedgeLatentAssignmentEnum_nodup G)
    · exact hedgeCoordinatePredicateSupport_nodup G pairTest privateTest
    · intro old
      rw [hedgeCoordinatePredicateSupport_mem_iff]
      constructor
      · intro listed
        exact Bool.and_eq_true_iff.mp (List.mem_filter.mp listed).2
      · intro selected
        exact List.mem_filter.mpr ⟨hedgeLatentAssignmentEnum_complete G old, Bool.and_eq_true_iff.mpr selected⟩
  exact permutation.length_eq.trans (by
    simp only [support, hedgeCoordinatePredicateSupport, List.length_map, ConstructivePermutation.pairList_length])

/-- Exact weighted numerator with an independently specified defect and
arbitrary separate pair/private predicates.  Empty supports are included,
and all private-coordinate multiplicities are retained. -/
theorem hedgeDefectPrior_eventMass_stratum_pair_private (G : ObservedGraph S) (defect : Bool)
    (pairTest : (Fin (pairRootCount G) -> Bool) -> Bool)
    (privateTest : HedgePrivateCoordinates S -> Bool) :
    FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms (fun unit =>
        hedgeDefectStratum G defect unit &&
          (pairTest (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) &&
            privateTest (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)))) =
      (if defect then 1 else 2) * (((hedgePairBitEnum G).filter pairTest).length *
        ((hedgePrivateCoordinateEnum S).filter privateTest).length) := by
  rw [hedgeDefectPrior_eventMass_stratum]
  simp only [hedgeDefectOldAssignment_assignment]
  rw [hedgeLatentAssignmentEnum_filter_pair_private_length]

/-! ## Comparison under the unchanged augmented carrier prior -/

/-- Ordinary partial incidence at a defect-dependent target, together with
a common private-background test.  Only `tested` rows are inspected. -/
def hedgePartialIncidenceLatentEvent (G : ObservedGraph S) (outer tested : NodeSet S)
    (target : Bool -> Fin S.count -> Bool) (privateTest : Bool -> HedgePrivateCoordinates S -> Bool) :
    Event ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) :=
  fun unit => hedgePartialPairBitsRealizes G outer tested (target (hedgeDefectBitOf G unit))
    (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) &&
      privateTest (hedgeDefectBitOf G unit) (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit))

/-- The corresponding nested incidence event retains exactly the same
private test and the same prior, but may have its own defect-dependent target. -/
def hedgePartialNestedIncidenceLatentEvent (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (target : Bool -> Fin S.count -> Bool) (privateTest : Bool -> HedgePrivateCoordinates S -> Bool) :
    Event ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) :=
  fun unit => hedgePartialNestedPairBitsRealizes G outer inner tested (target (hedgeDefectBitOf G unit))
    (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) &&
      privateTest (hedgeDefectBitOf G unit) (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit))

/-- The ordinary and nested partial-incidence events have identical natural
mass under the actual biased carrier prior.  A missing inner row is the only
parity-release hypothesis; no complete evenness condition is imposed on
either target.  Private predicates may depend on the defect and couple any
number of full-alphabet background coordinates, but are the same on both sides.

This supplies the weighted cross-map step absent from a merely within-map
uniform-fibre argument.  It does not silently identify a query's denominator
event with an incidence predicate; that semantic pullback remains required. -/
theorem BidirectedComponent.partialIncidence_eventMass_eq_nested
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (outerComponent : BidirectedComponent G outer) (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer) (testedSubset : NodeSet.Subset tested outer)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (largeTarget nestedTarget : Bool -> Fin S.count -> Bool)
    (privateTest : Bool -> HedgePrivateCoordinates S -> Bool) :
    FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
        (hedgePartialIncidenceLatentEvent G outer tested largeTarget privateTest) =
      FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
        (hedgePartialNestedIncidenceLatentEvent G outer inner tested nestedTarget privateTest) := by
  conv =>
    lhs
    rw [hedgeDefectPrior_eventMass_eq_sum_strata]
  conv =>
    rhs
    rw [hedgeDefectPrior_eventMass_eq_sum_strata]
  congr 1
  all_goals
    rw [hedgeDefectPrior_eventMass_stratum, hedgeDefectPrior_eventMass_stratum]
    simp only [hedgePartialIncidenceLatentEvent, hedgePartialNestedIncidenceLatentEvent,
      hedgeDefectBitOf_assignment, hedgeDefectOldAssignment_assignment]
    rw [hedgeLatentAssignmentEnum_filter_pair_private_length,
      hedgeLatentAssignmentEnum_filter_pair_private_length,
      outerComponent.partialPairBitRealizers_length_eq_nested G outer inner tested innerComponent subset
        testedSubset balance inside untested]

/-- Common-denominator rational probabilities agree as well.  Both events
use the original augmented product record, so equality of natural numerators
is enough; no alternate normalization or prior transport is assumed. -/
theorem BidirectedComponent.partialIncidence_probVal_equiv_nested
    (G : ObservedGraph S) (outer inner tested : NodeSet S)
    (outerComponent : BidirectedComponent G outer) (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer) (testedSubset : NodeSet.Subset tested outer)
    (balance : Fin S.count) (inside : inner balance = true) (untested : tested balance = false)
    (largeTarget nestedTarget : Bool -> Fin S.count -> Bool)
    (privateTest : Bool -> HedgePrivateCoordinates S -> Bool) :
    QProb.Equiv
      ((hedgeDefectPrior G).probVal (hedgePartialIncidenceLatentEvent G outer tested largeTarget privateTest))
      ((hedgeDefectPrior G).probVal
        (hedgePartialNestedIncidenceLatentEvent G outer inner tested nestedTarget privateTest)) := by
  unfold QProb.Equiv FiniteProbRecord.probVal
  rw [outerComponent.partialIncidence_eventMass_eq_nested G outer inner tested innerComponent subset
    testedSubset balance inside untested largeTarget nestedTarget privateTest]

end Causality
end Thesis
