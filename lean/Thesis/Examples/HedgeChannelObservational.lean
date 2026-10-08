import Thesis.CausalTransport.HedgeChannelObservational

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelObservational

open Probability

/-!
# Complete installed observed-law equality with a genuine outside background

The graph has `A -> Y -> Z` and `A <-> Y`.  Its original query is the bow
effect on `Y`; the large hedge is `{A,Y}` and the small hedge is `{Y}`.
Unlike the earlier two-node fixture, `Z` is outside the large forest, so
both the outside-large background mask and the outer mask have two choices.
Joining them gives four distinct outside-small masks.

The small signal reads its actual parent `A`, and the outside background
signal at `Z` reads its actual parent `Y`.  Complete observed equality is
proved by the new arbitrary-hedge theorem, not by assuming a replay plan or
evaluating all observed-event probabilities.  A separate literal full term
retains the actual sixty-four-vector shared prior and changes sign when only
the outside background value flips.

The finite list checks keep all twenty-four left choices and eight right
choices before integration, then display eight canonical survivors on each
side.  Four are full terms and four are background-only interactions.  Thus
the reindexing does not hide a missing outside-large mask or count a consumed
forest row a second time.  Original-query separation is not asserted here.
-/

private def signature : ObservedSignature where
  count := 3
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := fun _ => by decide
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 1) ∨ (parent.val = 1 ∧ child.val = 2))
  directed_earlier := by
    intro parent child selected
    have edge := of_decide_eq_true selected
    omega

private def graph : ObservedGraph signature where
  bidirected := fun left right => decide
    ((left.val = 0 ∧ right.val = 1) ∨ (left.val = 1 ∧ right.val = 0))
  bidirected_symmetric := by
    intro left right selected
    apply decide_eq_true
    rcases of_decide_eq_true selected with ⟨first, second⟩ | ⟨first, second⟩
    · exact Or.inr ⟨second, first⟩
    · exact Or.inl ⟨second, first⟩
  bidirected_irreflexive := by
    intro node
    apply decide_eq_false
    intro edge
    omega

private def action : Fin signature.count := ⟨0, by decide⟩
private def outcome : Fin signature.count := ⟨1, by decide⟩
private def background : Fin signature.count := ⟨2, by decide⟩
private def query : JointKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.singleton action
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
private def selection : HedgeSelection signature where
  large := NodeSet.union (NodeSet.singleton action) (NodeSet.singleton outcome)
  small := NodeSet.singleton outcome
  child := fun parent => if parent = action then some outcome else none
private def witness : HedgeWitness graph query := hedgeWitness_of_sets graph query selection (by decide +kernel)
private def rich : ObservedSignature.ValueRich signature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := fun _ => by change false ∈ [false, true]; decide
  second_enumerated := fun _ => by change true ∈ [false, true]; decide
  different := fun _ => Bool.false_ne_true

private def smallSignal (child : Fin signature.count) (parents : signature.binary.ParentValues child) : Bool :=
  if edge : signature.directed action child = true then parents action edge else false
private def backgroundSignal (child : Fin signature.count) (parents : signature.binary.ParentValues child) : Bool :=
  if edge : signature.directed outcome child = true then parents outcome edge else false

private def leftTables := Causality.HedgeChannelInstallation.leftTables witness
private def rightTables := Causality.HedgeChannelInstallation.rightTables witness
private def left := Causality.HedgeChannelInstallation.leftModel witness rich smallSignal backgroundSignal
private def right := Causality.HedgeChannelInstallation.rightModel witness smallSignal backgroundSignal
private def selectedSlot : Fin (Causality.HedgeChannelInstallation.masks
    (Causality.HedgeChannelInstallation.outer witness)).length := ⟨1, by decide +kernel⟩

/-- There are two independent mask coordinates, not one reused mask on
the consumed forest.  The complete and canonical actual choice counts differ. -/
theorem actual_choice_counts :
    (FiniteProduct.enumeration signature.count (fun _ => Option (Fin 6))
      (fun child => (leftTables child).expansionChoicesUnder none)).length = 24 ∧
    (FiniteProduct.enumeration signature.count (fun _ => Option (Fin 6))
      (fun child => (rightTables child).expansionChoicesUnder none)).length = 8 ∧
    (Causality.HedgeChannelInstallation.leftSurvivors witness).length = 8 ∧
    (Causality.HedgeChannelInstallation.rightSurvivors witness).length = 8 ∧
    (Causality.HedgeChannelInstallation.leftFullChoices witness).length = 4 ∧
    (Causality.HedgeChannelInstallation.joinedBackgroundMasks witness).length = 4 := by decide +kernel

/-- The combined mask really selects both the outer action and the
independent outside-large background, and never selects the small outcome. -/
theorem two_part_mask_bits :
    forall child, Causality.HedgeChannelInstallation.combinedBackgroundMask witness selectedSlot
      (NodeSet.singleton background) child = decide (child.val = 0 ∨ child.val = 2) := by decide +kernel

/-- The two actual installed SCMs remain compatible and fully positive.
These properties are separate from equality of their complete observed laws. -/
theorem actual_models_compatible_and_positive :
    Compatible left graph.binary ∧ Compatible right graph.binary ∧
      ObservationallyPositive left ∧ ObservationallyPositive right := by
  exact ⟨(Causality.HedgeChannelInstallation.models_compatible witness rich smallSignal backgroundSignal).1,
    (Causality.HedgeChannelInstallation.models_compatible witness rich smallSignal backgroundSignal).2,
    (Causality.HedgeChannelInstallation.models_positive witness rich smallSignal backgroundSignal).1,
    (Causality.HedgeChannelInstallation.models_positive witness rich smallSignal backgroundSignal).2⟩

/-- Equality covers every observed event, including all three coordinates
and arbitrary event unions.  No observed cell is reduced to establish it. -/
theorem actual_observational_equivalence : ObservationallyEquivalent left right :=
  Causality.HedgeChannelInstallation.models_observationallyEquivalent witness rich smallSignal backgroundSignal

/-- The exact natural likelihood numerators agree symbolically at every
sample, with the local parent-reading signals still active. -/
theorem actual_integrated_numerators_equal (sample : signature.binary.Assignment) :
    HedgeChannelTable.integratedNumerator graph 6 leftTables
      (Causality.HedgeChannelInstallation.leftSignals witness rich smallSignal backgroundSignal) (fun _ => none) sample =
    HedgeChannelTable.integratedNumerator graph 6 rightTables
      (Causality.HedgeChannelInstallation.rightSignals witness smallSignal backgroundSignal) (fun _ => none) sample :=
  Causality.HedgeChannelInstallation.integratedNumerators_equal witness rich smallSignal backgroundSignal sample

private def leftChoice := Causality.HedgeChannelInstallation.fullChoice witness witness.large
  (Causality.HedgeChannelInstallation.largeChannel witness selectedSlot) (NodeSet.singleton background)
private def rightChoice := Causality.HedgeChannelInstallation.fullChoice witness witness.small
  (Causality.HedgeChannelInstallation.smallChannel witness)
  (Causality.HedgeChannelInstallation.combinedBackgroundMask witness selectedSlot (NodeSet.singleton background))
private def firstSample : signature.binary.Assignment := fun _ => false
private def secondSample : signature.binary.Assignment := fun child => decide (child.val = 2)

/-- The selected outside background affects an individual actual signed
term on both sides.  Its size includes all sixty-four shared source vectors,
not a separately normalized channel prior. -/
theorem actual_outside_background_term :
    Causality.HedgeChannelInstallation.leftTermIntegral witness rich smallSignal backgroundSignal firstSample leftChoice = 1073741824 ∧
    Causality.HedgeChannelInstallation.rightTermIntegral witness smallSignal backgroundSignal firstSample rightChoice = 1073741824 ∧
    Causality.HedgeChannelInstallation.leftTermIntegral witness rich smallSignal backgroundSignal secondSample leftChoice = -1073741824 ∧
    Causality.HedgeChannelInstallation.rightTermIntegral witness smallSignal backgroundSignal secondSample rightChoice = -1073741824 := by decide +kernel

end HedgeChannelObservational
end Examples
end Causality
end Thesis
