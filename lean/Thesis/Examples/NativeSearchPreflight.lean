import Thesis.CausalTransport.NativeSearchPreflight
import Thesis.Examples.NativeGuardCompilation

namespace Thesis.Causality.Examples.NativeSearchPreflight

open Probability ProbabilityCode NativeSupportProfiles NativeCertificateCheck

/-!
# Resource refusal is not a causal negative answer

Large-space regressions evaluate only arithmetic or admission metadata,
never the corresponding list of raw codes. Actual catalogue execution is
restricted to a tiny explicitly supplied profile list and a leaf-only proof
budget. Symbolic equality transports the old mathematical catalogue contract.
No complete fixed-DAG/projection support generator is executed here.
-/

def limits : SearchLimits where
  maxObservedNodes := 3
  maxDictionaryEntries := 16
  maxExpressionDepth := 4
  maxProofDepth := 4
  maxSourceDepth := 3
  maxRawCandidates := 1000
  maxProfiles := 2
  maxGuardRows := 8
  maxProfileComparisons := 16
  maxTotalProfileComparisons := 4000

/-- This formalizes the review's arithmetic finding without allocating any
of its 135 million proof codes. The native wrapper consumes one level. -/
theorem three_binary_candidate_count : CodeCount.native ⟨8, 8⟩ 1 2 = 135298563 := by decide +kernel

example : CappedCount.native 100000 ⟨8, 8⟩ 1 2 = 100001 := by decide +kernel
example : CappedCount.native 0 ⟨0, 0⟩ 0 0 = 0 := rfl
example : CappedCount.mul 0 (CappedCount.clip 0 1000000000) (CappedCount.clip 0 0) = 0 := by decide +kernel
example : CappedCount.listLength 1 [0, 1, 2, 3, 4] = 2 := rfl

example : preflightSyntax limits signature 1000000 2 = .error (.expressionDepth 1000000 4) := by decide +kernel
example : preflightSyntax limits signature 1 1000000 = .error (.proofDepth 1000000 4) := by decide +kernel
example : preflightSyntax { limits with maxObservedNodes := 0 } signature 1 2 =
    .error (.observedNodes 1 0) := by decide +kernel
example : preflightSyntax { limits with maxDictionaryEntries := 1 } signature 1 2 =
    .error (.maskDictionary 1) := by decide +kernel
example : preflightSyntax { limits with maxDictionaryEntries := 2 } signature 1 2 =
    .error (.referenceDictionary 2) := by decide +kernel
example : preflightSyntax { limits with maxRawCandidates := 100 } signature 1 2 =
    .error (.rawCandidates 100) := by decide +kernel

/-- The declared null value remains in the reference count. -/
example : preflightSyntax limits signature 1 2 = .ok ⟨⟨2, 3⟩, 939⟩ := by decide +kernel

example : preflightProfiles { limits with maxProfiles := 0 } 3 profiles = .error (.profiles 0) := by decide +kernel
example : preflightProfiles { limits with maxGuardRows := 2 } 3 profiles = .error (.guardRows 2) := by decide +kernel
example : preflightProfiles { limits with maxProfileComparisons := 2 } 3 profiles =
    .error (.profileComparisons 2) := by decide +kernel
example : preflightProfiles limits 3 profiles = .ok ⟨1, 3, 3⟩ := by decide +kernel
example : preflightTotal limits 1000 5 = .error (.totalProfileComparisons 4000) := by decide +kernel
example : preflightTotal limits 939 3 = .ok 2817 := by decide +kernel

/-- Oversized source queries are refused independently of the encoded-proof
budget. No formula or support profile has to be compiled to report this. -/
example : NativeProofCode.guardedCatalogueOn { limits with maxSourceDepth := 0 }
    projection.observedGraph profiles source 0 1 = .error (.source 0) := rfl

example : NativeProofCode.guardedCatalogueOn { limits with maxProfiles := 0 }
    projection.observedGraph profiles source 0 1 = .error (.profiles 0) := rfl

/-- An admitted empty proof family is a successful bounded result, not a
resource refusal and not a claim of graph-level non-identifiability. -/
example : NativeProofCode.guardedCatalogueOn limits projection.observedGraph profiles source 0 0 = .ok [] := rfl

/-- Only eight native leaves are considered here. This executes the guarded
checker without opening either enormous whole-class profile generator. -/
example : (match NativeProofCode.guardedCatalogueOn limits projection.observedGraph profiles source 0 1 with
    | .error _ => false
    | .ok catalogue => !catalogue.isEmpty) = true := by decide +kernel

theorem admitted_catalogue_unchanged (expressionDepth proofDepth : Nat)
    (catalogue : List (CheckedNativeFormula projection.observedGraph profiles))
    (accepted : NativeProofCode.guardedCatalogueOn limits projection.observedGraph profiles source
      expressionDepth proofDepth = .ok catalogue) :
    catalogue = NativeProofCode.catalogueOn projection.observedGraph profiles source expressionDepth proofDepth :=
  NativeProofCode.guardedCatalogueOn_exact limits _ _ _ _ _ _ accepted

end Thesis.Causality.Examples.NativeSearchPreflight
