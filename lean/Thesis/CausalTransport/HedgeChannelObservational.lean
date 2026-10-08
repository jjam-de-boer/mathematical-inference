import Thesis.CausalTransport.HedgeChannelFullCoefficients

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Complete observed-law equality of the installed hedge channel pair

A left full term is indexed by an outer mask and a separate background
mask outside the large forest.  A right full term has just one background
mask outside the small forest.  Their integrated terms already match under
the explicit disjoint union of the two left masks.  Equality of the complete
sums additionally requires that this correspondence have no omissions or
duplicate descriptions.

The inverse masks are computed by intersection with the original outer
set and difference from the original large forest.  Their reconstruction
and uniqueness give a permutation of the two literal finite enumerations.
All existential index elimination stays in proofs of list membership; no
inverse function is selected from an existential proposition.  The actual
SCMs remain the already installed graph-compatible, positive models.

This module proves complete observational equality, not just a full-cell
example, equality of observed marginals, or equality of proposed polynomial
coefficients.  A separating original-query intervention and general
conditional countermodels remain distinct completeness obligations.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## Computed decomposition of a right background mask -/

/-- The outer part of a right term's background mask.  It is read from
the mask itself, in the original coordinates of the supplied hedge. -/
def outerBackgroundPart (w : HedgeWitness G q) (mask : NodeSet S) : NodeSet S :=
  NodeSet.inter mask (outer w)

/-- The remaining background mask, on vertices outside the large forest. -/
def outsideLargeBackgroundPart (w : HedgeWitness G q) (mask : NodeSet S) : NodeSet S :=
  NodeSet.diff mask w.large

/-- The computed outer part is a permitted outer selection for every
input mask, even before legality of the complete right mask is established. -/
theorem outerBackgroundPart_subset (w : HedgeWitness G q) (mask : NodeSet S) :
    NodeSet.Subset (outerBackgroundPart w mask) (outer w) :=
  NodeSet.inter_subset_right _ _

/-- Removing the large forest leaves only permitted outside-large rows;
the construction does not need a separate emptiness or inclusion decision. -/
theorem outsideLargeBackgroundPart_subset (w : HedgeWitness G q) (mask : NodeSet S) :
    NodeSet.Subset (outsideLargeBackgroundPart w mask) (outside w.large) := by
  intro child selected
  exact Bool.and_eq_true_iff.mpr ⟨rfl, (Bool.and_eq_true_iff.mp selected).2⟩

private theorem subset_bit_off (smaller larger : NodeSet S) (subset : NodeSet.Subset smaller larger)
    (child : Fin S.count) (absent : larger child = false) : smaller child = false := by
  cases selected : smaller child with
  | false => rfl
  | true => exact False.elim (Bool.false_ne_true (absent.symm.trans (subset child selected)))

/-- Splitting any legal right mask into its two original-coordinate parts
and joining those parts restores every bit.  The mask avoids the small
forest; that fact is used at vertices inside both forests. -/
theorem backgroundParts_reconstruct (w : HedgeWitness G q) (mask : NodeSet S)
    (subset : NodeSet.Subset mask (outside w.small)) :
    NodeSet.union (outerBackgroundPart w mask) (outsideLargeBackgroundPart w mask) = mask := by
  funext child
  cases large : w.large child with
  | false => simp only [outerBackgroundPart, outsideLargeBackgroundPart, outer,
      NodeSet.union, NodeSet.inter, NodeSet.diff, large, Bool.false_and,
      Bool.and_false, Bool.not_false, Bool.and_true, Bool.false_or]
  | true =>
      cases small : w.small child with
      | false => simp only [outerBackgroundPart, outsideLargeBackgroundPart, outer,
          NodeSet.union, NodeSet.inter, NodeSet.diff, large, small, Bool.not_false,
          Bool.not_true, Bool.and_true, Bool.and_false, Bool.or_false]
      | true =>
          have absent := NodeSet.disjoint_of_subset_right
            (NodeSet.disjoint_diff NodeSet.full w.small) subset child small
          simp only [outerBackgroundPart, outsideLargeBackgroundPart, outer,
            NodeSet.union, NodeSet.inter, NodeSet.diff, absent, Bool.false_and, Bool.false_or]

/-- Reading the outer part of a joined legal left mask recovers its exact
listed outer selection; outside-large backgrounds cannot add an outer bit. -/
theorem combinedBackgroundMask_outerPart (w : HedgeWitness G q)
    (index : Fin (masks (outer w)).length) (mask : NodeSet S)
    (subset : NodeSet.Subset mask (outside w.large)) :
    outerBackgroundPart w (combinedBackgroundMask w index mask) = selected w index := by
  funext child
  cases inside : outer w child with
  | false =>
      have absent := subset_bit_off (selected w index) (outer w) (selected_subset w index) child inside
      simp only [outerBackgroundPart, NodeSet.inter, inside, Bool.and_false, absent]
  | true =>
      have inLarge := NodeSet.diff_subset_left w.large w.small child inside
      have absent := NodeSet.disjoint_of_subset_right
        (NodeSet.disjoint_diff NodeSet.full w.large) subset child inLarge
      simp only [outerBackgroundPart, combinedBackgroundMask, NodeSet.inter, NodeSet.union,
        inside, absent, Bool.and_true, Bool.or_false]

/-- Reading the outside-large part recovers the other left mask, with no
retained bit at a row already consumed by its full main channel. -/
theorem combinedBackgroundMask_outsideLargePart (w : HedgeWitness G q)
    (index : Fin (masks (outer w)).length) (mask : NodeSet S)
    (subset : NodeSet.Subset mask (outside w.large)) :
    outsideLargeBackgroundPart w (combinedBackgroundMask w index mask) = mask := by
  funext child
  cases inside : w.large child with
  | true =>
      have absent := NodeSet.disjoint_of_subset_right
        (NodeSet.disjoint_diff NodeSet.full w.large) subset child inside
      simp only [outsideLargeBackgroundPart, NodeSet.diff, inside, Bool.not_true, Bool.and_false, absent]
  | false =>
      have absent := subset_bit_off (selected w index) w.large
        ((selected_subset w index).trans (NodeSet.diff_subset_left w.large w.small)) child inside
      simp only [outsideLargeBackgroundPart, combinedBackgroundMask, NodeSet.diff, NodeSet.union,
        inside, absent, Bool.not_false, Bool.and_true, Bool.false_or]

private theorem selected_injective (w : HedgeWitness G q) : Function.Injective (selected w) := by
  intro first second same
  apply Fin.ext
  exact (List.getElem_inj (masks_nodup (outer w))).mp same

private theorem combinedBackgroundMask_injective (w : HedgeWitness G q)
    (first second : Fin (masks (outer w)).length) (left right : NodeSet S)
    (leftSubset : NodeSet.Subset left (outside w.large))
    (rightSubset : NodeSet.Subset right (outside w.large))
    (same : combinedBackgroundMask w first left = combinedBackgroundMask w second right) :
    first = second ∧ left = right := by
  have outerEqual := congrArg (outerBackgroundPart w) same
  rw [combinedBackgroundMask_outerPart w first left leftSubset,
    combinedBackgroundMask_outerPart w second right rightSubset] at outerEqual
  have outsideEqual := congrArg (outsideLargeBackgroundPart w) same
  rw [combinedBackgroundMask_outsideLargePart w first left leftSubset,
    combinedBackgroundMask_outsideLargePart w second right rightSubset] at outsideEqual
  exact ⟨selected_injective w outerEqual, outsideEqual⟩

/-! ## A repetition-free permutation of complete mask lists -/

private instance maskDecidableEq : DecidableEq (NodeSet S) :=
  FiniteProduct.assignmentDecidableEq S.count (fun _ => Bool) (fun _ => inferInstance)

/-- All left outer slots and outside-large masks, listed in their actual
two-level order but read as the corresponding right background masks. -/
def joinedBackgroundMasks (w : HedgeWitness G q) : List (NodeSet S) :=
  (List.finRange (masks (outer w)).length).flatMap (fun index =>
    (masks (outside w.large)).map (combinedBackgroundMask w index))

/-- Every legal outside-small mask occurs in the joined list, and no
illegal one does.  The reverse direction uses only membership in the
already complete outer-mask list; its index existential stays in Prop. -/
theorem joinedBackgroundMasks_member_iff (w : HedgeWitness G q) (mask : NodeSet S) :
    mask ∈ joinedBackgroundMasks w ↔ mask ∈ masks (outside w.small) := by
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with ⟨index, _indexMember, mapped⟩
    rcases List.mem_map.mp mapped with ⟨part, partMember, same⟩
    rw [← same]
    exact (masks_member_iff _ _).mpr
      (combinedBackgroundMask_subset w index part ((masks_member_iff _ _).mp partMember))
  · intro member
    have subset := (masks_member_iff _ _).mp member
    have outerMember := (masks_member_iff _ _).mpr (outerBackgroundPart_subset w mask)
    rcases List.mem_iff_get.mp outerMember with ⟨index, same⟩
    have outsideMember := (masks_member_iff _ _).mpr (outsideLargeBackgroundPart_subset w mask)
    apply List.mem_flatMap.mpr
    refine ⟨index, List.mem_finRange index, List.mem_map.mpr ⟨outsideLargeBackgroundPart w mask, outsideMember, ?_⟩⟩
    change NodeSet.union (selected w index) (outsideLargeBackgroundPart w mask) = mask
    change selected w index = outerBackgroundPart w mask at same
    rw [same]
    exact backgroundParts_reconstruct w mask subset

/-- The joined enumeration has no duplicate masks.  A repeated combined
mask would repeat both its outer slot and its outside-large background part. -/
theorem joinedBackgroundMasks_nodup (w : HedgeWitness G q) : (joinedBackgroundMasks w).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro index _member
    apply ConstructivePermutation.nodup_map_of_injective_on _ _
      (fun left leftMember right rightMember same =>
        (combinedBackgroundMask_injective w index index left right
          ((masks_member_iff _ _).mp leftMember) ((masks_member_iff _ _).mp rightMember) same).2)
      (masks_nodup _)
  · apply (nodup_finRange (masks (outer w)).length).imp
    intro first second different left leftMember right rightMember same
    rcases List.mem_map.mp leftMember with ⟨leftMask, leftMaskMember, leftEq⟩
    rcases List.mem_map.mp rightMember with ⟨rightMask, rightMaskMember, rightEq⟩
    exact different (combinedBackgroundMask_injective w first second leftMask rightMask
      ((masks_member_iff _ _).mp leftMaskMember) ((masks_member_iff _ _).mp rightMaskMember)
      (leftEq.trans (same.trans rightEq.symm))).1

/-- The actual complete mask enumerations differ only in order.  The
constructive permutation theorem uses finite Boolean function equality,
not a chosen inverse or an equality decision for semantic propositions. -/
theorem joinedBackgroundMasks_perm (w : HedgeWitness G q) :
    (joinedBackgroundMasks w).Perm (masks (outside w.small)) :=
  ConstructivePermutation.perm_of_nodup_mem_iff _ _ (joinedBackgroundMasks_nodup w)
    (masks_nodup _) (joinedBackgroundMasks_member_iff w)

/-! ## Complete actual expansions and observed events -/

/-- Match every full-channel contribution exactly once.  The term identity
is applied only to legal listed outside-large masks, and the constructive
permutation retains the entire right sum rather than just one mask or cell. -/
theorem fullTermSums_equal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) :
    ((leftFullChoices w).map (leftTermIntegral w rich smallSignal backgroundSignal sample)).sum =
      ((rightFullChoices w).map (rightTermIntegral w smallSignal backgroundSignal sample)).sum := by
  have termLists : (leftFullChoices w).map (leftTermIntegral w rich smallSignal backgroundSignal sample) =
      (joinedBackgroundMasks w).map (fun mask =>
        rightTermIntegral w smallSignal backgroundSignal sample (fullChoice w w.small (smallChannel w) mask)) := by
    simp only [leftFullChoices, joinedBackgroundMasks, List.map_flatMap, List.map_map, Function.comp_def]
    apply congrArg (fun blocks : Fin (masks (outer w)).length -> List Int =>
      (List.finRange (masks (outer w)).length).flatMap blocks)
    funext index
    apply List.map_congr_left
    intro mask member
    exact fullTermIntegrals_equal w rich smallSignal backgroundSignal sample index mask
      ((masks_member_iff _ _).mp member)
  have reordered : ((joinedBackgroundMasks w).map (fun mask =>
        rightTermIntegral w smallSignal backgroundSignal sample (fullChoice w w.small (smallChannel w) mask))).sum =
      ((rightFullChoices w).map (rightTermIntegral w smallSignal backgroundSignal sample)).sum := by
    simpa only [rightFullChoices, List.map_map, Function.comp_def] using
      FiniteSupportedSum.sum_eq_of_perm ((joinedBackgroundMasks_perm w).map (fun mask =>
        rightTermIntegral w smallSignal backgroundSignal sample (fullChoice w w.small (smallChannel w) mask)))
  exact (congrArg List.sum termLists).trans reordered

/-- Equality of the complete factual expansion at every full observed
sample.  The previously proved zero-term reduction and common background
block equality are combined with the full sum, with no term left unhandled. -/
theorem expandedIntegrals_equal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) :
    HedgeChannelTable.expandedIntegral G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample =
      HedgeChannelTable.expandedIntegral G (channelCount w) (rightTables w)
        (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample :=
  (expandedIntegrals_eq_iff_fullSums w rich smallSignal backgroundSignal sample).mpr
    (fullTermSums_equal w rich smallSignal backgroundSignal sample)

/-- The actual nonnegative likelihood numerators agree, not just an
auxiliary signed expression.  The integer embedding is injective; neither
a natural subtraction nor truncation of negative expansion terms is used. -/
theorem integratedNumerators_equal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) :
    HedgeChannelTable.integratedNumerator G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample =
      HedgeChannelTable.integratedNumerator G (channelCount w) (rightTables w)
        (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample :=
  Int.ofNat_inj.mp ((HedgeChannelTable.integratedNumerator_expansion G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample).trans
    ((expandedIntegrals_equal w rich smallSignal backgroundSignal sample).trans
      (HedgeChannelTable.integratedNumerator_expansion G (channelCount w) (rightTables w)
        (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample).symm))

/-- Complete observed-law equality for every supplied hedge and every
typed small/background signal.  The two actual installed models have the
same literal row capacities, so the exact expansion bridge gives equality
of every observed event.  No replay-readiness, route-avoidance, or assumed
observational-equivalence premise is added to the hedge witness. -/
theorem models_observationallyEquivalent (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) :
    ObservationallyEquivalent (leftModel w rich smallSignal backgroundSignal)
      (rightModel w smallSignal backgroundSignal) := by
  change ObservationallyEquivalent
    (HedgeChannelTable.model G (channelCount w) (leftTables w) (leftSignals w rich smallSignal backgroundSignal))
    (HedgeChannelTable.model G (channelCount w) (rightTables w) (rightSignals w smallSignal backgroundSignal))
  exact HedgeChannelTable.model_observationallyEquivalent_of_expansion G (channelCount w)
    (leftTables w) (rightTables w) (leftSignals w rich smallSignal backgroundSignal)
    (rightSignals w smallSignal backgroundSignal) (capacities_equal w)
    (expandedIntegrals_equal w rich smallSignal backgroundSignal)

end HedgeChannelInstallation
end Causality
end Thesis
