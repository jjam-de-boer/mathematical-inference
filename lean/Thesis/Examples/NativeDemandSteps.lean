import Thesis.CausalTransport.NativeStepEncoding
import Thesis.Examples.NativeDemandFrames
import Thesis.Examples.NativePrimitiveAtoms

namespace Thesis.Causality.Examples.NativeDemandSteps

open Probability NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping Thesis.Causality.NativeDemandEncoding

/-!
# Nested elementary steps retain null branches and exact demand boundaries

The actual rule-1 leaf is reversed beneath a zero-weight factor and fixed
evaluation at a null reference. The inner conditional is still unavailable
there, but the complete step is supported: only its empty factor demand is
skipped. A positive weight, a strict product, or a null denominator does not
receive that exemption. Mixed profiles exercise one common encoded frame,
not a different replacement selected separately for each model.

Strict multiplication commutativity and associativity remain their existing
schemas with arbitrary literal operand trees. Malformed annotations are
rejected even when their erasures have supported endpoints. Every concrete
computation is checked by the Lean kernel; there is no path enumeration,
optimizer execution, native-decide axiom, or new runtime pilot.
-/

def requested : Demand family := atReference (reference 2)

def carrierStep := DoCalculusRewriteStep.atom NativePrimitiveAtoms.carrierAtom
def zeroLeaf := DoCalculusRewriteStep.atom NativeTypedPrimitives.zeroPrimitive.atom

def nestedNullStep := DoCalculusRewriteStep.under (.evaluateAt (reference 2))
  (.under (.weightedRight .zero) (.symm carrierStep))

theorem nested_null_is_supported :
    checkDerivation family requested carrierStep.toDerivation = false ∧
      checkDerivation family requested nestedNullStep.toDerivation = true ∧
      (Step.encode? family nestedNullStep requested).isSome = true := by decide +kernel

def encodedNullStep : Step family :=
  Step.encode family nestedNullStep requested (by decide +kernel)

theorem nested_encoding_checked : encodedNullStep.check requested = true :=
  Step.encode_checked family nestedNullStep requested (by decide +kernel)

/-- Erasure retains the fixed null reference, the defined zero weight, and
the conditional that reversal placed in the target's unused factor. -/
theorem nested_literal_endpoints :
    encodedNullStep.left.erase = .evaluateAt (reference 2) (.weightedMultiply .zero unitTerm) ∧
      encodedNullStep.right.erase = .evaluateAt (reference 2) (.weightedMultiply .zero (.kernel carrier)) :=
  Step.erase_encode_endpoints family nestedNullStep requested (by decide +kernel)

theorem reverse_is_supported : (Step.symm encodedNullStep).check requested = true := by decide +kernel

def positiveStep := DoCalculusRewriteStep.under (.weightedRight unitTerm) carrierStep
def strictStep := DoCalculusRewriteStep.under (.multiplyRight .zero) carrierStep
def denominatorStep := DoCalculusRewriteStep.under (.divideLeft .zero) zeroLeaf

theorem no_extra_support_is_supplied :
    checkDerivation family requested zeroLeaf.toDerivation = true ∧
      (Step.encode? family positiveStep requested).isSome = false ∧
      (Step.encode? family strictStep requested).isSome = false ∧
      (Step.encode? family denominatorStep requested).isSome = false := by decide +kernel

def changingWeight := DoCalculusRewriteStep.under (.weightedLeft nullConditional) zeroLeaf
def mixedRequested : Demand conflicting := fun _ value => decide (value = reference 2)

def encodedMixed : Step conflicting := Step.encode conflicting changingWeight mixedRequested (by decide +kernel)

theorem mixed_encoding_checked : encodedMixed.check mixedRequested = true :=
  Step.encode_checked conflicting changingWeight mixedRequested (by decide +kernel)

theorem mixed_frame_keeps_both_profiles :
    (match encodedMixed with
    | .under (.weightedLeft _ factor) _ =>
        factor.demand ⟨0, by decide⟩ (reference 2) && !factor.demand ⟨1, by decide⟩ (reference 2)
    | _ => false) = true := by decide +kernel

def commStep := DoCalculusRewriteStep.atom
  (DoCalculusAtom.multiplyComm (G := projection.observedGraph) unitTerm .zero)
def assocStep := DoCalculusRewriteStep.under (.evaluateAt (reference 2))
  (.symm (.atom (DoCalculusAtom.multiplyAssoc (G := projection.observedGraph) unitTerm .zero productTerm)))

theorem strict_ac_is_encoded :
    (Step.encode? family commStep requested).map (fun encoded => encoded.check requested) = some true ∧
      (Step.encode? family assocStep requested).map (fun encoded => encoded.check requested) = some true := by decide +kernel

/-- All masks of an unused operand still have to be coherent with its
strict parent. Support of the erased numerical expressions is insufficient. -/
def malformedComm : Step family := .multiplyComm requested (Term.encode family unitTerm requested)
  (Term.encode family unitTerm (fun _ _ => false))

theorem malformed_annotations_are_rejected :
    checkDerivation family requested malformedComm.erase.toDerivation = true ∧
      malformedComm.check requested = false := by decide +kernel

def vacuousComm : Step family := .multiplyComm (fun _ _ => false)
  (Term.encode family unitTerm (fun _ _ => false)) (Term.encode family unitTerm (fun _ _ => false))

theorem root_request_is_not_vacuous :
    vacuousComm.check (fun _ _ => false) = true ∧ vacuousComm.check requested = false := by decide +kernel

end Thesis.Causality.Examples.NativeDemandSteps
