import Thesis.Causality.CodeSearchMetadata
import Thesis.CausalTransport.NativeSearchPreflight

namespace Thesis.Causality

open Probability

/-!
# Native admission using certified domain-size metadata

Reuse every source, profile and total-work gate of the existing guarded
catalogue, but obtain early reference-size estimates from certified numbers.
Mask overflow is checked first. Reference overflow needs no generated value
list, no Cartesian dictionary and no raw proof enumeration.

The equality theorems retain both refusal decisions and complete admitted
catalogues. In particular, all old mathematical coverage and soundness
contracts remain applicable; metadata does not add a causal assumption or
turn policy refusal into a negative identification answer.

Profiles are still prepared inputs. Their construction and the cost of
evaluating one model/demand are NOT bounded by this adapter. It is not a
formula selector, and it adds no universal search or stopping theorem.
-/

variable {S : ObservedSignature.{0}} {P Q : FiniteLatentProjection S}

namespace ProbabilityCode.NativeProofCode

/-- Raw bounded enumeration is unchanged, but its admission can refuse from
certified numerical sizes without measuring generated domain lists. -/
def guardedEnumerationWithMetadata (limits : SearchLimits) (signature : ObservedSignature)
    (metadata : DomainSizeMetadata signature) (expressionDepth proofDepth : Nat) :
    Except SearchRefusal (List NativeProofCode) :=
  (preflightSyntaxWithMetadata limits signature metadata expressionDepth proofDepth).map
    (fun _ => enumerate signature expressionDepth proofDepth)

/-- Equality includes refusals, not only successful enumerations. It is not
an instruction to compile the metadata path back to the length-based one. -/
theorem guardedEnumerationWithMetadata_eq (limits : SearchLimits) (signature : ObservedSignature)
    (metadata : DomainSizeMetadata signature) (expressionDepth proofDepth : Nat) :
    guardedEnumerationWithMetadata limits signature metadata expressionDepth proofDepth =
      guardedEnumeration limits signature expressionDepth proofDepth := by
  unfold guardedEnumerationWithMetadata guardedEnumeration
  rw [preflightSyntaxWithMetadata_eq]

theorem guardedEnumerationWithMetadata_exact (limits : SearchLimits) (signature : ObservedSignature)
    (metadata : DomainSizeMetadata signature) (expressionDepth proofDepth : Nat) (codes : List NativeProofCode)
    (accepted : guardedEnumerationWithMetadata limits signature metadata expressionDepth proofDepth = .ok codes) :
    codes = enumerate signature expressionDepth proofDepth ∧ codes.length ≤ limits.maxRawCandidates := by
  rw [guardedEnumerationWithMetadata_eq] at accepted
  exact guardedEnumeration_exact limits signature expressionDepth proofDepth codes accepted

/-- Only the first metadata gate differs operationally from `guardedCatalogueOn`.
The source/query and supplied-profile checks remain mandatory and unchanged. -/
def guardedCatalogueOnWithMetadata (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat) :
    Except SearchRefusal (List (CheckedNativeFormula graph profiles)) := do
  let sizes ← preflightSyntaxWithMetadata limits S metadata expressionDepth proofDepth
  if source.Within sizes.dictionary limits.maxSourceDepth then
    let profile ← preflightProfiles limits sizes.dictionary.references profiles
    let _ ← preflightTotal limits sizes.candidates profile.comparisonsPerCertificate
    pure (catalogueOn graph profiles source expressionDepth proofDepth)
  else .error (.source limits.maxSourceDepth)

theorem guardedCatalogueOnWithMetadata_eq (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat) :
    guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth =
      guardedCatalogueOn limits graph profiles source expressionDepth proofDepth := by
  unfold guardedCatalogueOnWithMetadata guardedCatalogueOn
  rw [preflightSyntaxWithMetadata_eq]

/-- No admitted formula is lost: the entire bounded checked catalogue is
retained, rather than an arbitrary prefix meeting the requested limits. -/
theorem guardedCatalogueOnWithMetadata_exact (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat)
    (catalogue : List (CheckedNativeFormula graph profiles))
    (accepted : guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth = .ok catalogue) :
    catalogue = catalogueOn graph profiles source expressionDepth proofDepth := by
  rw [guardedCatalogueOnWithMetadata_eq] at accepted
  exact guardedCatalogueOn_exact limits graph profiles source expressionDepth proofDepth catalogue accepted

/-- Reuse the existing structural comparison allowance. This is not a bound
on the cost of evaluating a profile or constructing the supplied profiles. -/
theorem guardedCatalogueOnWithMetadata_total_bound (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat)
    (catalogue : List (CheckedNativeFormula graph profiles))
    (accepted : guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth = .ok catalogue) :
    (enumerate S expressionDepth proofDepth).length *
      ((profiles.length * (CodeDictionaries.ofSignature S).references) * profiles.length) ≤
        limits.maxTotalProfileComparisons := by
  rw [guardedCatalogueOnWithMetadata_eq] at accepted
  exact guardedCatalogueOn_total_bound limits graph profiles source expressionDepth proofDepth catalogue accepted

end ProbabilityCode.NativeProofCode
end Thesis.Causality
