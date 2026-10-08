import Thesis.CausalTransport.HedgeChannelFullTerms
import Thesis.Causality.NodeSetCardinality

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Actual installed coefficients of canonical full-channel choices

The full-term phase theorem retains the literal product of the installed
row coefficients.  This module evaluates that product: exactly one forest
row is the supplied anchor, every other selected row has the ordinary
amplitude, and every unselected row has the common capacity.  Background
selections are restricted to the complement of the full main forest.

The anchor is existing hedge data, not a vertex chosen from nonemptiness.
The count is the actual topological member-list length.  In particular a
background mask cannot count a consumed forest row a second time.  Natural
powers are matched before embedding in the integer expansion; no division
by a probability or amplitude is used.

Joining the selected outer mask to the outside-large background mask gives
one outside-small mask.  The last theorem matches the actual integrated
left term to that actual right term, including their common literal prior.
`HedgeChannelObservational` separately proves the complete surviving-sum
reindexing and actual observed-law equality.  A gap at the original outcome
and universal conditional countermodels remain distinct obligations.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

private theorem mask_disjoint (forest mask : NodeSet S) (subset : NodeSet.Subset mask (outside forest)) :
    NodeSet.Disjoint forest mask :=
  NodeSet.disjoint_of_subset_right (NodeSet.disjoint_diff NodeSet.full forest) subset

/-! ## From literal row products to anchored powers -/

/-- A full canonical choice has one special anchored row, ordinary
amplitudes on its other forest/background selections, and capacities on
all remaining rows.  The support family is still the actual table input;
no abstract likelihood polynomial replaces its coefficient product. -/
theorem fullChoice_coefficient (w : HedgeWitness G q)
    (nodes : Fin (channelCount w) -> NodeSet S)
    (anchors : Fin (channelCount w) -> Option (Fin S.count)) (deficits : Fin (channelCount w) -> Nat)
    (backgroundAnchors : forall child, anchors (backgroundChannel w child) = none)
    (forest : NodeSet S) (channel : Fin (channelCount w)) (anchor : Fin S.count)
    (mainAnchor : anchors channel = some anchor) (anchorInside : forest anchor = true)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside forest)) (sample : S.binary.Assignment) :
    HedgeChannelTable.choiceCoefficient
      (HedgeChannelCoefficients.tables (channelCount w) S.count nodes anchors deficits)
      (fun _ => none) sample (fullChoice w forest channel mask) =
      (HedgeChannelCoefficients.fullCoefficient (channelCount w) S.count
        ((NodeSet.members forest).length - 1) (deficits channel) *
        HedgeChannelCoefficients.outerCoefficient (channelCount w) S.count
          (S.count - (NodeSet.members forest).length) (NodeSet.members mask).length : Int) := by
  let weight := fun child =>
    if child = anchor then HedgeChannelCoefficients.anchorAmplitude (channelCount w) S.count (deficits channel)
    else if NodeSet.union forest mask child then HedgeChannelCoefficients.ordinaryAmplitude (channelCount w) S.count
    else HedgeChannelCoefficients.capacity (channelCount w) S.count
  have rows : forall child,
      (HedgeChannelCoefficients.tables (channelCount w) S.count nodes anchors deficits child).expansionCoefficientUnder
        none (sample child) (fullChoice w forest channel mask child) = (weight child : Int) := by
    intro child
    cases inside : forest child with
    | true =>
        simp only [fullChoice, inside, if_true, BooleanChannelTable.expansionCoefficientUnder]
        change (HedgeChannelCoefficients.scale (channelCount w) ^
          HedgeChannelCoefficients.rowExponent S.count anchors deficits child channel : Int) = _
        simp only [HedgeChannelCoefficients.rowExponent, mainAnchor, weight, NodeSet.union,
          inside, Bool.true_or, if_true, HedgeChannelCoefficients.anchorAmplitude,
          HedgeChannelCoefficients.ordinaryAmplitude]
        split <;> rfl
    | false =>
        have notAnchor : child ≠ anchor := by
          intro same
          exact Bool.false_ne_true (inside.symm.trans (same ▸ anchorInside))
        cases selected : mask child with
        | false =>
            simp only [fullChoice, backgroundChoice, inside, selected, Bool.false_eq_true, if_false,
              BooleanChannelTable.expansionCoefficientUnder]
            rw [HedgeChannelCoefficients.tables_capacity]
            simp only [weight, notAnchor, if_false, NodeSet.union, inside, selected, Bool.false_or,
              Bool.false_eq_true]
        | true =>
            simp only [fullChoice, backgroundChoice, inside, selected, Bool.false_eq_true, if_false,
              if_true, BooleanChannelTable.expansionCoefficientUnder]
            change (HedgeChannelCoefficients.scale (channelCount w) ^
              HedgeChannelCoefficients.rowExponent S.count anchors deficits child (backgroundChannel w child) : Int) = _
            simp only [HedgeChannelCoefficients.rowExponent, backgroundAnchors, weight, notAnchor, if_false,
              NodeSet.union, inside, selected, Bool.false_or, if_true,
              HedgeChannelCoefficients.ordinaryAmplitude, Int.natCast_pow]
  have product : HedgeChannelTable.choiceCoefficient
      (HedgeChannelCoefficients.tables (channelCount w) S.count nodes anchors deficits)
      (fun _ => none) sample (fullChoice w forest channel mask) = (FiniteProduct.natProduct S.count weight : Int) :=
    (FiniteProduct.iProduct_congr S.count _ _ rows).trans (FiniteProduct.iProduct_nat S.count weight)
  have selectedAnchor : NodeSet.union forest mask anchor = true := by
    simp only [NodeSet.union, anchorInside, Bool.true_or]
  have evaluated := FiniteProduct.natProduct_binary_mask_anchor S.count
    (HedgeChannelCoefficients.ordinaryAmplitude (channelCount w) S.count)
    (HedgeChannelCoefficients.capacity (channelCount w) S.count)
    (HedgeChannelCoefficients.anchorAmplitude (channelCount w) S.count (deficits channel))
    (NodeSet.union forest mask) anchor selectedAnchor
  rw [← NodeSet.members_length_eq_countP,
    NodeSet.members_length_union_of_disjoint forest mask (mask_disjoint forest mask subset)] at evaluated
  have positive := NodeSet.members_length_positive_of_mem forest anchor anchorInside
  have selectedExponent : (NodeSet.members forest).length + (NodeSet.members mask).length - 1 =
      ((NodeSet.members forest).length - 1) + (NodeSet.members mask).length := by omega
  have unselectedExponent : S.count - ((NodeSet.members forest).length + (NodeSet.members mask).length) =
      (S.count - (NodeSet.members forest).length) - (NodeSet.members mask).length := by omega
  have powers : FiniteProduct.natProduct S.count weight =
      HedgeChannelCoefficients.fullCoefficient (channelCount w) S.count
        ((NodeSet.members forest).length - 1) (deficits channel) *
        HedgeChannelCoefficients.outerCoefficient (channelCount w) S.count
          (S.count - (NodeSet.members forest).length) (NodeSet.members mask).length := by
    rw [evaluated, selectedExponent, unselectedExponent, Nat.pow_add]
    unfold HedgeChannelCoefficients.fullCoefficient HedgeChannelCoefficients.outerCoefficient
    ac_rfl
  exact product.trans (congrArg (fun value : Nat => (value : Int)) powers)

/-- Literal coefficient of a large installed channel.  Its deficit counts
the selected outer mask; backgrounds here are only outside the large forest. -/
theorem left_fullChoice_coefficient (w : HedgeWitness G q) (sample : S.binary.Assignment)
    (index : Fin (masks (outer w)).length) (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.large)) :
    HedgeChannelTable.choiceCoefficient (leftTables w) (fun _ => none) sample
      (fullChoice w w.large (largeChannel w index) mask) =
      (HedgeChannelCoefficients.fullCoefficient (channelCount w) S.count
        ((NodeSet.members w.large).length - 1) (NodeSet.members (selected w index)).length *
        HedgeChannelCoefficients.outerCoefficient (channelCount w) S.count
          (S.count - (NodeSet.members w.large).length) (NodeSet.members mask).length : Int) := by
  simpa only [leftTables, leftDeficits, role_largeChannel] using
    fullChoice_coefficient w (leftNodes w) (leftAnchors w) (leftDeficits w)
      (by intro child; rw [leftAnchors, role_backgroundChannel])
      w.large (largeChannel w index) w.actionSeed (by rw [leftAnchors, role_largeChannel])
      w.actionSeed_in_large mask subset sample

/-- Literal coefficient of the small installed channel.  Its backgrounds
range over the whole complement of the small forest, including outer rows. -/
theorem right_fullChoice_coefficient (w : HedgeWitness G q) (sample : S.binary.Assignment)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) :
    HedgeChannelTable.choiceCoefficient (rightTables w) (fun _ => none) sample
      (fullChoice w w.small (smallChannel w) mask) =
      (HedgeChannelCoefficients.fullCoefficient (channelCount w) S.count
        ((NodeSet.members w.small).length - 1) (NodeSet.members (outer w)).length *
        HedgeChannelCoefficients.outerCoefficient (channelCount w) S.count
          (S.count - (NodeSet.members w.small).length) (NodeSet.members mask).length : Int) := by
  simpa only [rightTables, rightDeficits, role_smallChannel] using
    fullChoice_coefficient w (rightNodes w) (rightAnchors w) (rightDeficits w)
      (by intro child; rw [rightAnchors, role_backgroundChannel])
      w.small (smallChannel w) w.actionRoot (by rw [rightAnchors, role_smallChannel])
      w.actionRoot_in_small mask subset sample

/-! ## The explicit matching background mask -/

/-- A left full term already carries an outer selection in its channel
index.  Its independent outside-large backgrounds join that selection to
form the right full term's entire outside-small background mask. -/
def combinedBackgroundMask (w : HedgeWitness G q) (index : Fin (masks (outer w)).length)
    (mask : NodeSet S) : NodeSet S := NodeSet.union (selected w index) mask

private theorem selected_mask_disjoint (w : HedgeWitness G q) (index : Fin (masks (outer w)).length)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.large)) :
    NodeSet.Disjoint (selected w index) mask :=
  NodeSet.Disjoint.of_subset_left (mask_disjoint w.large mask subset)
    ((selected_subset w index).trans (NodeSet.diff_subset_left w.large w.small))

/-- Both parts of the matching mask avoid the small forest.  This proves
that the right canonical term is legal without an additional readiness test. -/
theorem combinedBackgroundMask_subset (w : HedgeWitness G q) (index : Fin (masks (outer w)).length)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.large)) :
    NodeSet.Subset (combinedBackgroundMask w index mask) (outside w.small) := by
  apply NodeSet.union_subset
  · intro child chosen
    have off := NodeSet.disjoint_diff_right w.large w.small child (selected_subset w index child chosen)
    simp only [outside, NodeSet.diff, NodeSet.full, off, Bool.not_false, Bool.and_self]
  · intro child chosen
    have outsideLarge := subset child chosen
    have off := NodeSet.disjoint_of_subset_right
      (NodeSet.disjoint_diff_right NodeSet.full w.large) w.small_subset_large child outsideLarge
    simp only [outside, NodeSet.diff, NodeSet.full, off, Bool.not_false, Bool.and_self]

/-- The two mask parts do not overlap, so their literal member counts add. -/
theorem combinedBackgroundMask_length (w : HedgeWitness G q) (index : Fin (masks (outer w)).length)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.large)) :
    (NodeSet.members (combinedBackgroundMask w index mask)).length =
      (NodeSet.members (selected w index)).length + (NodeSet.members mask).length :=
  NodeSet.members_length_union_of_disjoint _ _ (selected_mask_disjoint w index mask subset)

/-- Joining the masks also joins their observed/parent characters; their
topological interleaving is immaterial to this finite parity identity. -/
theorem combinedBackgroundMask_phase (w : HedgeWitness G q) (index : Fin (masks (outer w)).length)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.large))
    (signal : ParentSignal S) (sample : S.binary.Assignment) :
    signalPhase (combinedBackgroundMask w index mask) signal sample =
      Bool.xor (signalPhase (selected w index) signal sample) (signalPhase mask signal sample) :=
  signalPhase_union_of_disjoint _ _ (selected_mask_disjoint w index mask subset) signal sample

/-! ## Literal coefficient and integrated-term correspondence -/

/-- The actual large row product matches the actual small row product
with the combined background mask.  Every unselected row capacity is kept;
the equality includes empty/full background masks without cancellation. -/
theorem fullChoice_coefficients_equal (w : HedgeWitness G q) (sample : S.binary.Assignment)
    (index : Fin (masks (outer w)).length) (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.large)) :
    HedgeChannelTable.choiceCoefficient (leftTables w) (fun _ => none) sample
      (fullChoice w w.large (largeChannel w index) mask) =
    HedgeChannelTable.choiceCoefficient (rightTables w) (fun _ => none) sample
      (fullChoice w w.small (smallChannel w) (combinedBackgroundMask w index mask)) := by
  rw [left_fullChoice_coefficient w sample index mask subset,
    right_fullChoice_coefficient w sample _ (combinedBackgroundMask_subset w index mask subset),
    combinedBackgroundMask_length w index mask subset]
  apply congrArg (fun value : Nat => (value : Int))
  have partition := NodeSet.members_length_split_of_subset w.small w.large w.small_subset_large
  change (NodeSet.members w.large).length = (NodeSet.members w.small).length + (NodeSet.members (outer w)).length at partition
  have positiveSmall := NodeSet.members_length_positive_of_mem w.small w.actionRoot w.actionRoot_in_small
  have boundSelected := selected_degree_bound w index
  have boundRows : (NodeSet.members w.large).length + (NodeSet.members mask).length <= S.count := by
    rw [← NodeSet.members_length_union_of_disjoint w.large mask (mask_disjoint w.large mask subset)]
    exact NodeSet.members_length_le_count _
  have largeOthers : (NodeSet.members w.large).length - 1 =
      ((NodeSet.members w.small).length - 1) + (NodeSet.members (outer w)).length := by omega
  have capacityExponent : (NodeSet.members (outer w)).length - (NodeSet.members (selected w index)).length +
      (S.count - (NodeSet.members w.large).length - (NodeSet.members mask).length) =
      (S.count - (NodeSet.members w.small).length) -
        ((NodeSet.members (selected w index)).length + (NodeSet.members mask).length) := by omega
  rw [largeOthers, mask_fullCoefficient_match w]
  unfold HedgeChannelCoefficients.outerCoefficient
  rw [Nat.pow_add, ← capacityExponent, Nat.pow_add]
  ac_rfl

/-- Term-by-term equality on the actual shared prior.  The left outer-mask
slot and its outside-large backgrounds map explicitly to one right term.
No observational-equivalence premise is used, and no sum is truncated. -/
theorem fullTermIntegrals_equal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment)
    (index : Fin (masks (outer w)).length) (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.large)) :
    leftTermIntegral w rich smallSignal backgroundSignal sample (fullChoice w w.large (largeChannel w index) mask) =
      rightTermIntegral w smallSignal backgroundSignal sample
        (fullChoice w w.small (smallChannel w) (combinedBackgroundMask w index mask)) := by
  rw [left_fullTermIntegral w rich smallSignal backgroundSignal sample index mask subset,
    right_fullTermIntegral w smallSignal backgroundSignal sample _ (combinedBackgroundMask_subset w index mask subset),
    fullChoice_coefficients_equal w sample index mask subset,
    combinedBackgroundMask_phase w index mask subset backgroundSignal sample, Bool.xor_assoc]

end HedgeChannelInstallation
end Causality
end Thesis
