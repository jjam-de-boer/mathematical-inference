import Thesis.CausalTransport.NativeFramePreservation
import Thesis.Examples.NativeDemandFrames

namespace Thesis.Causality.Examples.NativeFramePreservation

open Probability NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping Thesis.Causality.NativeDemandEncoding

/-!
# Source-only frame preservation keeps the important null boundaries

The same checked unit expansion is lifted through all ten frame forms. The
tests compute the routed inner support and filled source support, then use
the quantified theorem to obtain target support without assuming it.

A zero weight may skip an undefined factor, including when the replacement
puts that conditional into the target. Changing a weight across two profiles
preserves their different factor demands in one common encoded frame. A
denominator replacement retains positivity. In contrast, an already null
denominator, a demanded null fixed reference, or a null marginal summand
cannot be repaired merely by support at an unrelated inner reference.

All input computations are kernel checks. No global context-closure,
normalizer, search procedure or runtime solver pilot is introduced.
-/

def requested : Demand family := atReference (reference 2)

def positiveFrames : List (ProbabilityTermFrame signature) :=
  [.marginalize NodeSet.full, .evaluateAt (reference 2),
    .addLeft unitTerm, .addRight unitTerm, .multiplyLeft unitTerm, .multiplyRight unitTerm,
    .weightedLeft unitTerm, .weightedRight unitTerm, .divideLeft unitTerm, .divideRight unitTerm]

theorem all_ten_inputs_checked : positiveFrames.all (fun frame =>
    checkDerivation family (frameDemand family frame requested) expandUnit &&
      check family (frame.fill unitTerm) requested) = true := by decide +kernel

/-- No target premise is supplied: each target is obtained from the routed
inner proof and the source of that particular frame. -/
theorem all_ten_targets_checked : positiveFrames.all (fun frame => check family (frame.fill productTerm) requested) = true := by
  apply List.all_eq_true.mpr
  intro frame listed
  have inputs := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp all_ten_inputs_checked) frame listed)
  exact Frame.right_checked_of_left family frame expandUnit requested inputs.1 inputs.2

def skipFactor : ProbabilityTermFrame signature := .weightedRight .zero

theorem zero_weight_target_supported : check family (skipFactor.fill (.kernel carrier)) requested = true :=
  Frame.right_checked_of_left family skipFactor eraseNullCondition.symm requested (by decide +kernel) (by decide +kernel)

theorem zero_weight_lift_supported : checkDerivation family requested (skipFactor.lift eraseNullCondition.symm) = true :=
  Frame.lift_checked_of_left family skipFactor eraseNullCondition.symm requested (by decide +kernel) (by decide +kernel)

theorem skipped_conditional_is_still_undefined :
    check family (.kernel carrier) requested = false ∧
      termStatus family (skipFactor.fill (.kernel carrier)) profileIndex (reference 2) = .zero := by decide +kernel

def denominatorHole : ProbabilityTermFrame signature := .divideRight .zero

theorem denominator_positivity_preserved : check family (denominatorHole.fill productTerm) requested = true :=
  Frame.right_checked_of_left family denominatorHole expandUnit requested (by decide +kernel) (by decide +kernel)

theorem null_denominator_has_no_source_witness :
    checkDerivation family requested expandUnit = true ∧
      check family ((ProbabilityTermFrame.divideLeft .zero).fill unitTerm) requested = false ∧
      check family ((ProbabilityTermFrame.divideLeft .zero).fill productTerm) requested = false := by decide +kernel

theorem null_substitutions_cannot_use_unrelated_support :
    checkDerivation family (atReference (reference 0)) eraseNullCondition = true ∧
      checkDerivation family (frameDemand family (.evaluateAt (reference 2)) (atReference (reference 0))) eraseNullCondition = false ∧
      checkDerivation family (frameDemand family (.marginalize NodeSet.full) (atReference (reference 0))) eraseNullCondition = false := by decide +kernel

def changingWeight := NativeDemandFrames.changingWeight
def weightProof := NativeDemandFrames.zeroStep.derivation
def mixedRequested : Demand conflicting := NativeDemandFrames.mixedDemand

theorem mixed_target_supported : check conflicting (changingWeight.fill NativeDemandFrames.zeroStep.right) mixedRequested = true :=
  Frame.right_checked_of_left conflicting changingWeight weightProof mixedRequested (by decide +kernel) (by decide +kernel)

/-- The encoded frame retains its one fixed conditional tree and the
profile-specific positive-factor mask. Only the source check is assumed. -/
theorem mixed_common_frame_target_checked :
    ((Frame.encode conflicting changingWeight NativeDemandFrames.zeroStep.left mixedRequested).fill
      (Term.encode conflicting NativeDemandFrames.zeroStep.right (frameDemand conflicting changingWeight mixedRequested))).check = true :=
  Frame.encoded_right_checked_of_left conflicting changingWeight weightProof mixedRequested (by decide +kernel) (by decide +kernel)

theorem mixed_full_lift_supported : checkDerivation conflicting mixedRequested (changingWeight.lift weightProof) = true :=
  Frame.lift_checked_of_left conflicting changingWeight weightProof mixedRequested (by decide +kernel) (by decide +kernel)

end Thesis.Causality.Examples.NativeFramePreservation
