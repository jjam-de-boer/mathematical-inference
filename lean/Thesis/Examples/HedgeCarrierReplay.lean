import Thesis.CausalTransport.HedgeCarrierReplay
import Thesis.CausalTransport.HedgeReadout
import Thesis.Examples.HedgeConditionalMarginal

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeInternalCarrierReplay

open Probability
open HedgeWeightedTernaryIntervention (signature graph rich outcome)
open HedgeConditionalInsideForest (witness actionNode conditioner)

/-!
# Full nonbinary replay at a genuinely internal small-forest pivot

Retain the failure-aligned three-node forests from the irreducible conditional
fixture.  `B` belongs to the small forest and its kept child is `Y`.  A noisy
copy of `A` at `B` changes that child's actual equation; the old sink-based
common-observable argument is unavailable.  The new theorem nevertheless
matches the *entire* observational laws of the two updated SCMs.

The explicit latent checks distinguish private backgrounds which the old
observed target conceals.  Both old units produce the all-second assignment.
After the readout flips `B`, the responding child flips away from `second`.
Its hidden background then matters: one unit emits `first`, while the other
emits the third label.  Thus replay cannot be justified by a map of the old
observed assignment alone, or by agreement only up to the modified pivot.

Noise support and the restoring-readout theorem separately retain strict
positivity.  This example does not assert the finite-plan routing theorem or
an arbitrary outer-only overwrite; the existing negative action-overwrite
regression remains outside the new small-pivot hypothesis.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem action_to_pivot : signature.directed actionNode conditioner = true := by decide +kernel
private theorem pivot_to_outcome : signature.directed conditioner outcome = true := by decide +kernel

def parentSignal (parents : signature.ParentValues conditioner) : Bool :=
  hedgeIsSecond rich actionNode (parents actionNode action_to_pivot)

def readout := hedgeNoisyReadout rich conditioner false parentSignal

def noise : FiniteProbRecord Bool := ⟨[(false, 2), (true, 1)], 3, by decide, rfl⟩

theorem pivot_in_small : witness.small conditioner = true := rfl
theorem pivot_has_kept_child : witness.child conditioner = some outcome := rfl

/-- The full updated law agrees despite a genuine kept child.  No sink,
other-mechanisms-ignore proof, or observed-map equation is supplied. -/
theorem updated_observationally_equivalent : ObservationallyEquivalent
    ((witness.largeCarrierDefectParityModel rich).withPrivateReadout conditioner noise readout)
    ((witness.smallCarrierDefectParityModel rich).withPrivateReadout conditioner noise readout) :=
  witness.carrierDefectParityModels_withPrivateReadout_observationally_equivalent_of_small rich
    conditioner pivot_in_small noise readout

/-- The strengthened base law permits arbitrary coupling with concealed
private backgrounds and the defect, rather than assuming their independence
from the observed target. -/
theorem retained_state_laws_equal (event : Event (HedgeCarrierObservedState signature)) :
    QProb.Equiv
      ((witness.largeCarrierDefectParityModel rich).prior.probVal (fun unit =>
        event (hedgeCarrierObservedState graph (witness.largeCarrierDefectParityModel rich).eval unit)))
      ((witness.smallCarrierDefectParityModel rich).prior.probVal (fun unit =>
        event (hedgeCarrierObservedState graph (witness.smallCarrierDefectParityModel rich).eval unit))) :=
  witness.carrierDefectParityModels_observationalState_probVal_equiv rich event

private theorem noise_positive (bit : Bool) : noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  cases bit <;> decide +kernel

theorem updated_left_positive : ObservationallyPositive
    ((witness.largeCarrierDefectParityModel rich).withPrivateReadout conditioner noise readout) :=
  (witness.largeCarrierDefectParityModel rich).withHedgeReadout_positive
    (witness.largeCarrierDefectParityModel_positive rich) rich conditioner noise noise_positive false parentSignal

theorem updated_right_positive : ObservationallyPositive
    ((witness.smallCarrierDefectParityModel rich).withPrivateReadout conditioner noise readout) :=
  (witness.smallCarrierDefectParityModel rich).withHedgeReadout_positive
    (witness.smallCarrierDefectParityModel_positive rich) rich conditioner noise noise_positive false parentSignal

theorem updated_left_compatible : Compatible
    ((witness.largeCarrierDefectParityModel rich).withPrivateReadout conditioner noise readout) graph :=
  (witness.largeCarrierDefectParityModel rich).withHedgeReadout_compatible
    (witness.largeCarrierDefectParityModel_compatible rich) rich conditioner noise false parentSignal

theorem updated_right_compatible : Compatible
    ((witness.smallCarrierDefectParityModel rich).withPrivateReadout conditioner noise readout) graph :=
  (witness.smallCarrierDefectParityModel rich).withHedgeReadout_compatible
    (witness.smallCarrierDefectParityModel_compatible rich) rich conditioner noise false parentSignal

/-! ## Old values conceal a background that a responding child later emits -/

def target : signature.Assignment := fun node => rich.second node

def backgrounds (label : signature.Value outcome) : HedgePrivateCoordinates signature :=
  fun node => hedgeIndexOfValue signature node (signature.replace target outcome label node)

noncomputable def unit (label : signature.Value outcome) : (witness.largeCarrierDefectParityModel rich).latent.Assignment :=
  hedgeDefectAssignment graph
    (hedgeLatentOfCoordinates graph (witness.largeCarrierDefectPairBits rich target) (backgrounds label))
    (witness.largeCarrierDefectBit rich target)

private theorem backgrounds_fit (label : signature.Value outcome) :
    hedgeCarrierPrivateCoordinatesFit rich witness.large target (backgrounds label) = true := by
  apply hedgeCarrierPrivateCoordinatesFit_of
  · intro node _inside
    rfl
  · intro node outside
    cases outside

theorem old_unit_evaluates (label : signature.Value outcome) :
    (witness.largeCarrierDefectParityModel rich).eval (unit label) = target := by
  apply witness.largeCarrierDefectParityModel_eval_eq_of_support rich target
  · exact hedgeDefectBitOf_assignment graph _ _
  · unfold unit
    rw [hedgeDefectOldAssignment_assignment, hedgePairBitsOf_latentOfCoordinates]
    apply hedgePairBitsRealizes_of
    exact witness.largeCarrierDefectPairBits_spec rich target
  · unfold unit
    rw [hedgeDefectOldAssignment_assignment, hedgePrivateCoordinatesOf_latentOfCoordinates]
    exact backgrounds_fit label

private theorem retained_background (label : signature.Value outcome) :
    hedgePrivateDecode signature outcome
      (hedgePrivateCoordinatesOf graph (hedgeDefectOldAssignment graph (unit label)) outcome) = label := by
  unfold unit
  rw [hedgeDefectOldAssignment_assignment, hedgePrivateCoordinatesOf_latentOfCoordinates]
  exact (hedgePrivateDecode_index signature outcome _).trans (signature.replace_at target outcome label)

private theorem parentBits_outcome (parents : signature.ParentValues outcome) :
    hedgeForestParentBitsFrom rich witness.child outcome parents =
      hedgeIsSecond rich conditioner (parents conditioner pivot_to_outcome) := by
  rw [HedgeConditionalInsideForest.witness_child]
  change Bool.xor false (hedgeIsSecond rich conditioner (parents conditioner pivot_to_outcome)) = _
  exact Bool.false_xor _

/-- The entire actual updated SCM, not an isolated readout record, emits
the concealed background after its kept parent has flipped the child's bit. -/
theorem responding_child_value (label : signature.Value outcome) :
    ((witness.largeCarrierDefectParityModel rich).withPrivateReadout conditioner noise readout).eval
        (PrivateBooleanNoise.assignment (witness.largeCarrierDefectParityModel rich).latent true (unit label)) outcome =
      hedgeParityCarrierValue rich outcome false label := by
  rw [witness.largeCarrierDefectParityModel_withPrivateReadout_eval_eq_replay rich conditioner noise readout,
    old_unit_evaluates label]
  change witness.carrierReplayNode rich target _ conditioner (rich.first conditioner) outcome = _
  rw [HedgeWitness.carrierReplayNode, if_neg (by decide +kernel : outcome ≠ conditioner)]
  simp only [show witness.large outcome = true from rfl, if_true]
  rw [parentBits_outcome, parentBits_outcome]
  rw [HedgeWitness.carrierReplayNode, if_pos rfl, signature.replace_at, retained_background]
  rfl

/-- The two old units have the same full observation, but after this one
internal readout their responding child distinguishes `first` from the third
label.  Retained-state replay is therefore materially stronger than a common
map of the old observed assignment or a prefix-only equality. -/
theorem hidden_background_changes_response :
    (witness.largeCarrierDefectParityModel rich).eval (unit (rich.second outcome)) =
        (witness.largeCarrierDefectParityModel rich).eval (unit ⟨2, by decide⟩) ∧
      ((witness.largeCarrierDefectParityModel rich).withPrivateReadout conditioner noise readout).eval
          (PrivateBooleanNoise.assignment (witness.largeCarrierDefectParityModel rich).latent true
            (unit (rich.second outcome))) outcome ≠
        ((witness.largeCarrierDefectParityModel rich).withPrivateReadout conditioner noise readout).eval
          (PrivateBooleanNoise.assignment (witness.largeCarrierDefectParityModel rich).latent true
            (unit ⟨2, by decide⟩)) outcome := by
  constructor
  · exact (old_unit_evaluates _).trans (old_unit_evaluates _).symm
  · rw [responding_child_value, responding_child_value]
    decide +kernel

end HedgeInternalCarrierReplay
end Examples
end Causality
end Thesis
