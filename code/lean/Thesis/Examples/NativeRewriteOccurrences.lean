import Thesis.CausalTransport.NativeRewriteOccurrences
import Thesis.Examples.NativeStepPreservation

namespace Thesis.Causality.Examples.NativeRewriteOccurrences

open Probability ProbabilityCode NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping Thesis.Causality.NativeDemandEncoding

/-!
# Supplied rule codes, literal frame stacks and faithful step conversion

A supplied chain code is decoded and placed under a fixed reference and a
denominator hole. Only its whole source is checked directly; reconstruction
and preservation supply the full step and target. All seven primitive tags
also retain their original decoded entries and symbolic finite membership.
The equation catalogue is never evaluated.

Flattening a nested reversed zero-weight step cancels two reversal wrappers
into one false direction bit while retaining both literal frames and exact
endpoints. Thus proof-wrapper placement can change, but no sibling, demand
label or endpoint tree disappears. Strict multiplication AC stays separate
from primitive codes. Mixed-profile weights retain one common occurrence.

Invalid indices and demanded null conditionals still fail decoding. Wrong
reference masks, malformed source annotations and zero denominators retain
their original refusals after flattening. These are small kernel checks and
applications of the correspondence theorems, with no trace or search pilot.
-/

def requested : Demand family := NativeStepPreservation.requested
def outerRequested : Demand family := NativeStepPreservation.outerRequested

def suppliedCode : PrimitiveRuleCode family := ⟨.chain, NativeTypedPrimitives.emptyQuad, requested⟩
def suppliedRule : CheckedPrimitiveRule family := suppliedCode.check.get (by decide +kernel)
def suppliedOccurrence : RewriteOccurrence family :=
  ⟨.primitive suppliedRule, false,
    [.evaluateAt outerRequested (reference 2), .divideRight requested (.zero requested)]⟩

theorem supplied_source_checked : suppliedOccurrence.check outerRequested = true := by decide +kernel

theorem supplied_reconstruction_checked : suppliedOccurrence.toStep.check outerRequested = true :=
  (suppliedOccurrence.toStep_check outerRequested).trans supplied_source_checked

theorem supplied_target_valid : suppliedOccurrence.right.checkAnnotations outerRequested = true ∧
    check family suppliedOccurrence.right.erase outerRequested = true :=
  suppliedOccurrence.target_checks_of_check outerRequested supplied_source_checked

theorem supplied_old_support_checked :
    checkDerivation family outerRequested suppliedOccurrence.toStep.erase.toDerivation = true :=
  suppliedOccurrence.erase_checked outerRequested supplied_source_checked

def everyRule (kind : PrimitiveCode) : CheckedPrimitiveRule family :=
  .ofPrimitive (NativePrimitiveAtoms.everyEntry kind)

theorem all_seven_entries_recovered (kind : PrimitiveCode) :
    (everyRule kind).entry = NativePrimitiveAtoms.everyEntry kind :=
  CheckedPrimitiveRule.entry_ofPrimitive _

/-- Coverage is obtained from the actual decoded rule, without reducing
the potentially large catalogue to find an index. -/
theorem all_seven_equations_catalogued (kind : PrimitiveCode) :
    ((everyRule kind).left, (everyRule kind).right) ∈ CheckedPrimitiveRule.equations family :=
  CheckedPrimitiveRule.mem_equations _

def badIndex : PrimitiveRuleCode family := ⟨.chain, ⟨2, 0, 0, 0⟩, requested⟩
def nullCarrier : PrimitiveRuleCode family := ⟨.rule1, ⟨0, 0, 1, 0⟩, requested⟩
def unusedCarrier : PrimitiveRuleCode family := ⟨.rule1, ⟨0, 0, 1, 0⟩, fun _ _ => false⟩

theorem decoding_support_boundaries : badIndex.check.isSome = false ∧
    nullCarrier.check.isSome = false ∧ unusedCarrier.check.isSome = true := by decide +kernel

def wrappedReversal : Step family := .symm NativeStepPreservation.nestedZero
def flattened := RewriteOccurrence.ofStep wrappedReversal

theorem literal_context_retained : flattened.context =
    [.evaluateAt outerRequested (reference 2), .weightedRight requested (.zero requested)] := rfl

theorem reversals_flattened : flattened.reversed = false := rfl

theorem flattened_endpoints : flattened.left = wrappedReversal.left ∧ flattened.right = wrappedReversal.right :=
  RewriteOccurrence.ofStep_endpoints _

theorem flattened_checked : flattened.check outerRequested = true := by
  rw [flattened, RewriteOccurrence.ofStep_check]
  exact NativeStepPreservation.whole_reversal_checked

theorem reconstructed_endpoints : flattened.toStep.left = wrappedReversal.left ∧
    flattened.toStep.right = wrappedReversal.right := RewriteOccurrence.toStep_ofStep_endpoints _

private def outerReversal : Step family → Bool
  | .symm _ => true
  | _ => false

/-- Literal endpoint preservation does not assert identity of proof trees:
the reconstructed step has its frame stack outside the root direction bit. -/
theorem wrapper_placement_can_change : outerReversal wrappedReversal = true ∧
    outerReversal flattened.toStep = false := by decide +kernel

theorem all_ten_frames_preserve_acceptance : NativeStepPreservation.allTen.all
    (fun step => (RewriteOccurrence.ofStep step).check requested) = true := by
  simpa only [RewriteOccurrence.ofStep_check] using NativeStepPreservation.all_ten_steps_checked

theorem strict_ac_instances_retained :
    (match (RewriteOccurrence.ofStep NativeStepPreservation.strictComm).redex with
    | .multiplyComm _ _ _ => true
    | _ => false) = true ∧
    (match (RewriteOccurrence.ofStep NativeStepPreservation.strictAssoc).redex with
    | .multiplyAssoc _ _ _ _ => true
    | _ => false) = true := by decide +kernel

def mixedOccurrence := RewriteOccurrence.ofStep NativeStepPreservation.mixedStep

theorem one_occurrence_checks_both_profiles : mixedOccurrence.toStep.check NativeStepPreservation.mixedRequested = true := by
  rw [RewriteOccurrence.toStep_check, mixedOccurrence, RewriteOccurrence.ofStep_check]
  exact NativeStepPreservation.mixed_step_checked

theorem wrong_reference_stays_rejected :
    (RewriteOccurrence.ofStep NativeStepPreservation.wrongReference).check outerRequested = false := by
  rw [RewriteOccurrence.ofStep_check]
  exact NativeStepPreservation.wrong_reference_rejected

theorem malformed_annotations_stay_rejected :
    (RewriteOccurrence.ofStep NativeDemandSteps.malformedComm).check requested = false := by
  rw [RewriteOccurrence.ofStep_check]
  exact NativeStepPreservation.malformed_source_rejected

theorem wrong_root_request_stays_rejected :
    (RewriteOccurrence.ofStep NativeDemandSteps.vacuousComm).check requested = false := by
  rw [RewriteOccurrence.ofStep_check]
  exact NativeStepPreservation.wrong_root_request_rejected

theorem zero_denominator_stays_rejected :
    (RewriteOccurrence.ofStep NativeStepPreservation.zeroDenominator).check requested = false := by
  rw [RewriteOccurrence.ofStep_check]
  exact NativeStepPreservation.zero_denominator_rejected

end Thesis.Causality.Examples.NativeRewriteOccurrences
