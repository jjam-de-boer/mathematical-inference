import Thesis.CausalTransport.NativeSearchMetadata
import Thesis.Examples.NativeSearchPreflight

namespace Thesis.Causality.Examples.NativeSearchMetadata

open Probability ProbabilityCode NativeSupportProfiles NativeCertificateCheck NativeSearchPreflight

/-!
# Cheap refusals and unchanged native applications

The three-valued fixture supplies the certified number three, retaining its
declared null intervention value. A separate parameterized `Fin (n + 1)`
signature supplies `n + 1` with the symbolic `List.length_finRange` theorem.
Its large cases occur ONLY in erased proposition/proof statements: neither
an executable top-level billion-element list nor a large search is created.

Equality proofs alone do not certify an eager implementation's cost: logical
reduction can discard unused work. The companion Python source-order guards
and inspection of generated code therefore check that early refusal branches
really precede value-enumeration calls. Those guards are not proof checking
or a hard runtime-cost theorem; Lean and the axiom audit remain mandatory.
-/

def sizes : DomainSizeMetadata signature :=
  ⟨fun _ => 3, fun _ => (List.length_finRange (n := 3)).symm⟩

/-- This constructor keeps the enumeration behind a function of a runtime
parameter. Its metadata is a number, not a measured generated value list. -/
def wideSignature (extra : Nat) : ObservedSignature where
  count := 1
  Value := fun _ => Fin (extra + 1)
  valueEnumeration := fun _ => List.finRange (extra + 1)
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => finRange_nodup (extra + 1)
  defaultValue := fun _ => ⟨0, Nat.succ_pos extra⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def wideSizes (extra : Nat) : DomainSizeMetadata (wideSignature extra) :=
  ⟨fun _ => extra + 1, fun _ => (List.length_finRange (n := extra + 1)).symm⟩

theorem mask_refusal_for_every_domain (extra : Nat) :
    preflightSyntax { limits with maxDictionaryEntries := 1 } (wideSignature extra) 1 2 =
      .error (.maskDictionary 1) := rfl

example (extra : Nat) :
    preflightSyntaxWithMetadata { limits with maxDictionaryEntries := 1 }
      (wideSignature extra) (wideSizes extra) 1 2 = .error (.maskDictionary 1) := rfl

/-- The billion is a natural-number comparison in this proof, not an
enumeration. No original-domain list is reduced to obtain its size. -/
theorem large_reference_refusal :
    preflightSyntaxWithMetadata limits (wideSignature 1000000000) (wideSizes 1000000000) 1 2 =
      .error (.referenceDictionary 16) := rfl

example : NativeProofCode.guardedEnumerationWithMetadata limits
    (wideSignature 1000000000) (wideSizes 1000000000) 1 2 = .error (.referenceDictionary 16) := rfl

example : preflightSyntaxWithMetadata limits signature sizes 1000000 2 =
    .error (.expressionDepth 1000000 4) := rfl
example : preflightSyntaxWithMetadata limits signature sizes 1 1000000 =
    .error (.proofDepth 1000000 4) := rfl
example : preflightSyntaxWithMetadata { limits with maxRawCandidates := 100 } signature sizes 1 2 =
    .error (.rawCandidates 100) := rfl

/-- All three declared references remain counted, not just the two positive
observational cells. The accepted count is exact and matches the old path. -/
example : preflightSyntaxWithMetadata limits signature sizes 1 2 = .ok ⟨⟨2, 3⟩, 939⟩ := rfl

example : NativeProofCode.guardedCatalogueOnWithMetadata { limits with maxSourceDepth := 0 }
    projection.observedGraph sizes profiles source 0 1 = .error (.source 0) := rfl
example : NativeProofCode.guardedCatalogueOnWithMetadata { limits with maxProfiles := 0 }
    projection.observedGraph sizes profiles source 0 1 = .error (.profiles 0) := rfl
example : NativeProofCode.guardedCatalogueOnWithMetadata { limits with maxTotalProfileComparisons := 0 }
    projection.observedGraph sizes profiles source 0 1 = .error (.totalProfileComparisons 0) := rfl
example : NativeProofCode.guardedCatalogueOnWithMetadata limits
    projection.observedGraph sizes profiles source 0 0 = .ok [] := rfl

/-- Execute only the eight native leaves on an already supplied tiny profile
list. This neither creates a complete model catalogue nor selects a formula. -/
example : (match NativeProofCode.guardedCatalogueOnWithMetadata limits
    projection.observedGraph sizes profiles source 0 1 with
    | .error _ => false
    | .ok catalogue => !catalogue.isEmpty) = true := by decide +kernel

theorem admitted_null_cell_covered
    (catalogue : List (CheckedNativeFormula projection.observedGraph profiles))
    (accepted : NativeProofCode.guardedCatalogueOnWithMetadata limits projection.observedGraph sizes profiles source 1 2 = .ok catalogue) :
    ∃ generated, generated ∈ catalogue ∧
      generated.available entry.model.observationalDist (reference 2) = true := by
  rw [NativeProofCode.guardedCatalogueOnWithMetadata_eq] at accepted
  exact NativeSearchPreflight.admitted_null_cell_covered catalogue accepted

end Thesis.Causality.Examples.NativeSearchMetadata
