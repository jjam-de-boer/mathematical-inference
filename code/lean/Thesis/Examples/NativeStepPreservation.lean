import Thesis.CausalTransport.NativeStepPreservation
import Thesis.Examples.NativeDemandSteps
import Thesis.Examples.NativeFramePreservation

namespace Thesis.Causality.Examples.NativeStepPreservation

open Probability ProbabilityCode NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping Thesis.Causality.NativeDemandEncoding

/-!
# Local certificates preserve valid sources through literal nested frames

The steps below are assembled directly from individually checked primitive
leaves and frame data. Their constructors receive no whole-step support or
target-validity proof. For each whole step, kernel computations establish
only its source checks; the general theorem supplies target validity and
the full check.

All ten frames are exercised, followed by reversal under a zero weight at a
fixed null reference, strict multiplication AC, and one changing-weight step
across conflicting profiles. Wrong reference masks, malformed annotations and
zero denominators remain rejected. In particular, raw source support alone
does not excuse a primitive certificate at an unrelated reference.

These are small kernel computations and applications of quantified theorems,
not a causal execution pilot, ground rewrite search or a stopping argument.
-/

def requested : Demand family := atReference (reference 2)
def outerRequested : Demand family := atReference (reference 0)

/-- Only the local primitive is checked here. The enclosing frame is
literal step data; neither its target nor its full support is an input. -/
def framedUnit? (frame : ProbabilityTermFrame signature) : Option (Step family) :=
  (TypedPrimitive.check family .chain NativeTypedPrimitives.emptyQuad (frameDemand family frame requested)).map
    (fun entry => .under (Frame.encode family frame entry.checked.left requested) (.primitive entry))

def allTen : List (Step family) := NativeFramePreservation.positiveFrames.filterMap framedUnit?

theorem all_ten_present : allTen.length = 10 := by decide +kernel

theorem all_ten_sources : allTen.all (fun step => step.left.checkAnnotations requested &&
    check family step.left.erase requested) = true := by decide +kernel

theorem all_ten_steps_checked : allTen.all (fun step => step.check requested) = true := by
  apply List.all_eq_true.mpr
  intro step listed
  exact (Step.check_iff_left step requested).mpr
    (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp all_ten_sources) step listed))

def unusedCarrier : TypedPrimitive family :=
  .ofAtom family (fun _ _ => false) NativePrimitiveAtoms.carrierAtom .rule1 ⟨0, 0, 1, 0⟩
    NativePrimitiveAtoms.carrier_code (by decide +kernel)

def nestedZero : Step family :=
  .under (.evaluateAt outerRequested (reference 2))
    (.under (.weightedRight requested (.zero requested)) (.symm (.primitive unusedCarrier)))

theorem nested_source_valid : nestedZero.left.checkAnnotations outerRequested = true ∧
    check family nestedZero.left.erase outerRequested = true := by decide +kernel

/-- The undefined target conditional remains below the defined zero weight.
The fixed outer reference is null, and the leaf's actual demand is empty. -/
theorem nested_step_checked : nestedZero.check outerRequested = true :=
  (Step.check_iff_left nestedZero outerRequested).mpr nested_source_valid

theorem nested_target_valid : nestedZero.right.checkAnnotations outerRequested = true ∧
    check family nestedZero.right.erase outerRequested = true :=
  (Step.endpoints_valid_iff nestedZero outerRequested).mp nested_source_valid

theorem nested_old_support_checked : checkDerivation family outerRequested nestedZero.erase.toDerivation = true :=
  Step.erase_checked_of_left nestedZero outerRequested nested_source_valid

theorem whole_reversal_checked : (Step.symm nestedZero).check outerRequested = true :=
  (Step.check_iff_left (.symm nestedZero) outerRequested).mpr nested_target_valid

def strictComm : Step family := .multiplyComm requested (Term.encode family unitTerm requested) (.zero requested)
def strictAssoc : Step family :=
  .under (.evaluateAt outerRequested (reference 2))
    (.symm (.multiplyAssoc requested (Term.encode family unitTerm requested) (.zero requested)
      (Term.encode family productTerm requested)))

theorem strict_comm_checked : strictComm.check requested = true :=
  (Step.check_iff_left strictComm requested).mpr (by decide +kernel)

theorem nested_strict_assoc_checked : strictAssoc.check outerRequested = true :=
  (Step.check_iff_left strictAssoc outerRequested).mpr (by decide +kernel)

def mixedRequested : Demand conflicting := NativeDemandFrames.mixedDemand
def mixedEntry : TypedPrimitive conflicting :=
  (TypedPrimitive.check conflicting .chain ⟨0, 1, 0, 0⟩ mixedRequested).get (by decide +kernel)
def mixedFrame : Frame conflicting :=
  .weightedLeft mixedRequested (Term.encode conflicting nullConditional
    (positiveDemand conflicting mixedRequested (termStatus conflicting mixedEntry.checked.left)))
def mixedStep : Step conflicting := .under mixedFrame (.primitive mixedEntry)

theorem mixed_source_valid : mixedStep.left.checkAnnotations mixedRequested = true ∧
    check conflicting mixedStep.left.erase mixedRequested = true := by decide +kernel

theorem mixed_target_valid : mixedStep.right.checkAnnotations mixedRequested = true ∧
    check conflicting mixedStep.right.erase mixedRequested = true :=
  (Step.endpoints_valid_iff mixedStep mixedRequested).mp mixed_source_valid

theorem mixed_step_checked : mixedStep.check mixedRequested = true :=
  (Step.check_iff_left mixedStep mixedRequested).mpr mixed_source_valid

/-- The unchanged literal factor has a positive demand in one profile and
an empty demand in the other at the very same declared reference. -/
theorem mixed_factor_demands :
    (match mixedFrame with
    | .weightedLeft _ factor => factor.demand ⟨0, by decide⟩ (reference 2) &&
        !factor.demand ⟨1, by decide⟩ (reference 2)
    | _ => false) = true := by decide +kernel

def wrongReference : Step family :=
  .under (.evaluateAt outerRequested (reference 2)) (.symm (.primitive NativePrimitiveAtoms.carrierEntry))

theorem raw_source_support_is_insufficient :
    check family wrongReference.left.erase outerRequested = true ∧
      check family wrongReference.right.erase outerRequested = false ∧
      wrongReference.left.checkAnnotations outerRequested = false := by decide +kernel

theorem wrong_reference_rejected : wrongReference.check outerRequested = false := by
  rw [Step.check_eq_left]
  decide +kernel

theorem malformed_source_rejected : NativeDemandSteps.malformedComm.check requested = false := by
  rw [Step.check_eq_left]
  decide +kernel

theorem wrong_root_request_rejected : NativeDemandSteps.vacuousComm.check requested = false := by
  rw [Step.check_eq_left]
  decide +kernel

def zeroDenominator : Step family :=
  .under (.divideLeft requested (.zero requested)) (.primitive NativeTypedPrimitives.unitPrimitive)

theorem zero_denominator_rejected : zeroDenominator.check requested = false := by
  rw [Step.check_eq_left]
  decide +kernel

end Thesis.Causality.Examples.NativeStepPreservation
