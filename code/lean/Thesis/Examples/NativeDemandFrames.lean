import Thesis.CausalTransport.NativeDemandFrames
import Thesis.Examples.NativeTypedPrimitives

namespace Thesis.Causality.Examples.NativeDemandFrames

open Probability NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping
open Thesis.Causality.NativeDemandEncoding

/-!
# Literal siblings, null substitutions and mixed-profile weighted frames

A checked chain identity changes a weight without changing the fixed
conditional factor's demand. At a null reference both weights are zero, so
the factor may be unsupported. With two profiles the same reference is
positive in the first and zero in the second: one common frame must retain
both rows, demanding the factor only in the positive row.

The converse boundary is tested too. A supported inner proof cannot repair
an unavailable positive-weight factor or a zero denominator. Fixed and
marginal substitution retain their actual null references, and a literal
actionful sibling remains visible after replacement. These are small kernel
checks and applications of the quantified bridge, not rewrite-path search.
-/

def requested : Demand family := atReference (reference 2)
def changingWeight : ProbabilityTermFrame signature := .weightedLeft nullConditional
def zeroFactor : ProbabilityTermFrame signature := .weightedRight .zero
def positiveFactor : ProbabilityTermFrame signature := .weightedRight unitTerm

def zeroStep := NativeTypedPrimitives.zeroPrimitive.checked

theorem zero_inner_checked :
    checkDerivation family (frameDemand family changingWeight requested) zeroStep.derivation = true := by decide +kernel

theorem zero_weight_common_frame :
    Frame.encode family changingWeight zeroStep.left requested = Frame.encode family changingWeight zeroStep.right requested :=
  Frame.encode_eq_of_checked family changingWeight zeroStep.derivation requested zero_inner_checked

/-- The actual lifted proof is reconstructed from the two checked filled
terms, while its unsupported null factor remains literal syntax. -/
theorem zero_weight_lift_checked : checkDerivation family requested (changingWeight.lift zeroStep.derivation) = true := by
  apply (Frame.lift_check_iff family changingWeight zeroStep.derivation requested).mpr
  exact ⟨zero_inner_checked, by decide +kernel, by decide +kernel⟩

theorem fixed_null_factor_is_retained :
    (Frame.encode family changingWeight zeroStep.left requested).erase = changingWeight :=
  Frame.erase_encode family changingWeight zeroStep.left requested

theorem positive_weight_still_needs_factor :
    checkDerivation family (frameDemand family changingWeight requested) expandUnit = true ∧
      checkDerivation family requested (changingWeight.lift expandUnit) = false := by decide +kernel

theorem zero_factor_omits_only_support :
    checkDerivation family requested eraseNullCondition = false ∧
      checkDerivation family (frameDemand family zeroFactor requested) eraseNullCondition = true ∧
      checkDerivation family requested (zeroFactor.lift eraseNullCondition) = true ∧
      checkDerivation family requested (positiveFactor.lift eraseNullCondition) = false := by decide +kernel

theorem substituted_null_demand_is_retained :
    frameDemand family (.evaluateAt (reference 2)) (atReference (reference 0)) profileIndex (reference 2) = true ∧
      frameDemand family (.evaluateAt (reference 2)) (atReference (reference 0)) profileIndex (reference 0) = false ∧
      frameDemand family (.marginalize NodeSet.full) (atReference (reference 0)) profileIndex (reference 2) = true ∧
      checkDerivation family (atReference (reference 0)) ((ProbabilityTermFrame.evaluateAt (reference 2)).lift eraseNullCondition) = false := by decide +kernel

theorem zero_denominator_is_not_repaired :
    checkDerivation family requested expandUnit = true ∧
      checkDerivation family requested ((ProbabilityTermFrame.divideLeft .zero).lift expandUnit) = false ∧
      checkDerivation family requested ((ProbabilityTermFrame.divideRight .zero).lift expandUnit) = true := by decide +kernel

def actionSibling : ProbabilityTermFrame signature :=
  .multiplyLeft (.kernel ⟨NodeSet.empty, NodeSet.full, NodeSet.empty⟩)

theorem literal_action_remains_visible :
    ((Frame.encode family actionSibling unitTerm requested).fill (Term.encode family productTerm requested)).check = true ∧
      ((Frame.encode family actionSibling unitTerm requested).fill (Term.encode family productTerm requested)).actionFreeCheck = false := by decide +kernel

def mixedDemand : Demand conflicting := fun _ value => decide (value = reference 2)
def mixedContext := Frame.encode conflicting changingWeight zeroStep.left mixedDemand

/-- The formerly null reference is positive in one supplied profile. It
must not be skipped there, nor required in the other profile's zero branch. -/
theorem mixed_factor_demand :
    (match mixedContext with
    | .weightedLeft _ factor =>
        factor.demand ⟨0, by decide⟩ (reference 2) && !factor.demand ⟨1, by decide⟩ (reference 2)
    | _ => false) = true := by decide +kernel

theorem mixed_context_is_shared :
    Frame.encode conflicting changingWeight zeroStep.left mixedDemand = Frame.encode conflicting changingWeight zeroStep.right mixedDemand :=
  Frame.encode_eq_of_checked conflicting changingWeight zeroStep.derivation mixedDemand (by decide +kernel)

theorem both_profile_branches_are_supported :
    checkDerivation conflicting mixedDemand (changingWeight.lift zeroStep.derivation) = true := by
  apply Frame.lift_checked conflicting changingWeight zeroStep.derivation mixedDemand
  all_goals decide +kernel

/-- All ten forms and arbitrary sibling syntax are covered by the general
result. The demand at the root is the application's explicit request. -/
example (frame : ProbabilityTermFrame signature) {left right : ProbabilityTerm signature}
    (derivation : DoCalculusDerivation projection.observedGraph left right) (request : Demand conflicting)
    (accepted : checkDerivation conflicting (frameDemand conflicting frame request) derivation = true) :
    (Frame.encode conflicting frame left request).fill (Term.encode conflicting right (frameDemand conflicting frame request)) =
      Term.encode conflicting (frame.fill right) request :=
  Frame.encode_fill_right conflicting frame derivation request accepted

end Thesis.Causality.Examples.NativeDemandFrames
