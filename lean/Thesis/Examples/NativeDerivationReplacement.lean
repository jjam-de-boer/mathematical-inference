import Thesis.CausalTransport.NativeDerivationReplacement
import Thesis.Examples.NativeKernelInterfaceObstruction

namespace Thesis.Causality.Examples.NativeDerivationReplacement

open Probability NativeSupportProfiles NativeKernelInterfaceObstruction

/-!
# Replacing an actual null-carrier detour, with its endpoints unchanged

The earlier obstruction has two proofs from `U` to `U * U`: a direct chain
step and a detour through `P(empty | Z)`. The direct step passes at every
reference; the detour fails at the declared null value of `Z`. This supplies
a genuine support improvement, not a replacement justified by status alone.

Use that same replacement inside a proof with a nonreflexive sibling, under
zero/positive weights, and across marginal/fixed-reference boundaries. The
symbolic application covers arbitrary enclosing contexts; the small literal
computations expose the branch boundaries without enumerating a catalogue.
An unrelated undefined sibling remains undefined after replacement.
-/

theorem direct_check (referenceValue : signature.Assignment) :
    HiddenDAGLocalDerivationSupport.check entry.model referenceValue expandUnit = true := by rfl

/-- The hypothesis is uniform in references, not just at the root where a
caller happens to evaluate the enclosing proof. -/
theorem direct_improves_detour (referenceValue : signature.Assignment) :
    HiddenDAGLocalDerivationSupport.check entry.model referenceValue carrierDetour = true →
      HiddenDAGLocalDerivationSupport.check entry.model referenceValue expandUnit = true :=
  fun _ => direct_check referenceValue

theorem replacement_in_any_context {left right : ProbabilityTerm signature}
    (context : DoCalculusDerivationContext projection.observedGraph unitTerm productTerm left right)
    (referenceValue : signature.Assignment)
    (accepted : HiddenDAGLocalDerivationSupport.check entry.model referenceValue (context.fill carrierDetour) = true) :
    HiddenDAGLocalDerivationSupport.check entry.model referenceValue (context.fill expandUnit) = true :=
  context.check_mono entry.model carrierDetour expandUnit direct_improves_detour referenceValue accepted

def changingSibling : DoCalculusDerivationContext projection.observedGraph unitTerm productTerm
    (.multiply unitTerm unitTerm) (.multiply productTerm productTerm) :=
  .multiplyLeft .hole expandUnit

theorem sibling_proof_is_retained : changingSibling.fill carrierDetour = .multiplyCongr carrierDetour expandUnit := rfl

theorem nonreflexive_sibling_replacement :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2) (changingSibling.fill carrierDetour) = false ∧
      HiddenDAGLocalDerivationSupport.check entry.model (reference 2) (changingSibling.fill expandUnit) = true := by
  constructor <;> decide +kernel

def zeroWeight : DoCalculusDerivationContext projection.observedGraph unitTerm productTerm
    (.weightedMultiply .zero unitTerm) (.weightedMultiply .zero productTerm) :=
  .weightedRight (.refl .zero) .hole

def positiveWeight : DoCalculusDerivationContext projection.observedGraph unitTerm productTerm
    (.weightedMultiply unitTerm unitTerm) (.weightedMultiply unitTerm productTerm) :=
  .weightedRight (.refl unitTerm) .hole

theorem zero_weight_retains_skipped_detour :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2) (zeroWeight.fill carrierDetour) = true ∧
      HiddenDAGLocalDerivationSupport.check entry.model (reference 2) (zeroWeight.fill expandUnit) = true := by
  constructor <;> decide +kernel

theorem positive_weight_retains_actual_requirement :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2) (positiveWeight.fill carrierDetour) = false ∧
      HiddenDAGLocalDerivationSupport.check entry.model (reference 2) (positiveWeight.fill expandUnit) = true := by
  constructor <;> decide +kernel

def marginal : DoCalculusDerivationContext projection.observedGraph unitTerm productTerm
    (.marginalize NodeSet.full unitTerm) (.marginalize NodeSet.full productTerm) :=
  .marginalize NodeSet.full .hole

def fixedNull : DoCalculusDerivationContext projection.observedGraph unitTerm productTerm
    (.evaluateAt (reference 2) unitTerm) (.evaluateAt (reference 2) productTerm) :=
  .evaluateAt (reference 2) .hole

/-- The root is supported for the detour, but its fixed-reference context
is not. A root-only comparison would therefore be an insufficient premise. -/
theorem root_only_comparison_is_insufficient :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 0) carrierDetour = true ∧
      HiddenDAGLocalDerivationSupport.check entry.model (reference 0) (fixedNull.fill carrierDetour) = false ∧
      HiddenDAGLocalDerivationSupport.check entry.model (reference 0) (fixedNull.fill expandUnit) = true := by
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

theorem marginal_replacement_checks_null_substitution :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 0) (marginal.fill carrierDetour) = false ∧
      HiddenDAGLocalDerivationSupport.check entry.model (reference 0) (marginal.fill expandUnit) = true := by
  constructor <;> decide +kernel

def nullSibling : DoCalculusDerivationContext projection.observedGraph unitTerm productTerm
    (.multiply unitTerm (.kernel carrier)) (.multiply productTerm (.kernel carrier)) :=
  .multiplyLeft .hole (.refl (.kernel carrier))

theorem replacement_does_not_repair_unrelated_null_sibling :
    HiddenDAGLocalDerivationSupport.check entry.model (reference 2) (nullSibling.fill carrierDetour) = false ∧
      HiddenDAGLocalDerivationSupport.check entry.model (reference 2) (nullSibling.fill expandUnit) = false := by
  constructor <;> decide +kernel

end Thesis.Causality.Examples.NativeDerivationReplacement
