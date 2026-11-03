import Thesis.CausalTransport.NativeQueryDemand
import Thesis.CausalTransport.NativeGuardedPaths
import Thesis.CausalTransport.NativeRewriteTraces
import Thesis.CausalTransport.NativeTargetRecognition

namespace Thesis.Causality.ProbabilityCode

open Probability NativeDemandTyping NativeDemandEncoding

/-!
# Available derivation certificates share a fixed query demand

The mask is computed from the source query and observed support/reference
cell, before consulting a candidate formula. Availability transports to every
listed profile with that same observed support. On the source-supported
cells selected by the mask, both endpoints are therefore defined and the
original certified guard supplies the full recursive derivation check.

One supplied derivation is then linearized and encoded once for the entire
profile family. Its finite trace retains the actual source and printed term,
and that printed term passes the finite target recognizer at the same fixed
mask. Different candidates for the same source and observed cell do not get
to choose different masks or favorable modelwise proofs.

The original certificate is unchanged. A null source can leave the mask
empty, but its soundness application still needs its separate source-support
witness. Printed availability remains required even in that case. The
`actionOne` branch keeps its own theorem and guard; only an explicitly
identified derivation branch is converted below. These are forward coverage
and witness constructions, not formula search, ground-AC correspondence or
a terminating reachability procedure.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}
variable {profiles : List (NativeTemplateInstance P)}

namespace CheckedNativeFormula

/-- Guard acceptance and observational availability use all observed support
bits, so changing positive numerical weights changes neither Boolean test. -/
theorem available_eq_of_pattern_eq (certificate : CheckedNativeFormula P.observedGraph profiles)
    {left right : FiniteProbRecord S.Assignment}
    (same : NativeSupportGuard.pattern S left = NativeSupportGuard.pattern S right) (reference : S.Assignment) :
    certificate.available left reference = certificate.available right reference := by
  have supportSame := NativeSupportGuard.support_eq_of_pattern_eq same
  have evaluated : (certificate.formula.observationalDenote left reference).isSome =
      (certificate.formula.observationalDenote right reference).isSome := by
    rw [← ProbabilityResult.status_isDefined, ← ProbabilityResult.status_isDefined,
      ProbabilityTerm.status_eq_of_support_eq certificate.formula supportSame reference]
  simp only [available, NativeSupportGuard.accepts_eq_of_pattern_eq certificate.guard same reference, evaluated]

/-- A fixed source-selected cell is active for every available certificate.
Its source witness is read from the mask; formula support comes separately
from observational availability and the certificate's action-free proof. -/
theorem queryDemand_le_activated (certificate : CheckedNativeFormula P.observedGraph profiles)
    (record : FiniteProbRecord S.Assignment) (fixed : S.Assignment)
    (available : certificate.available record fixed = true) (index : Fin profiles.length) (reference : S.Assignment)
    (needed : NativeQueryDemand.mask profiles certificate.source (NativeSupportGuard.pattern S record) fixed index reference = true) :
    certificate.proof.activatedDemand profiles certificate.guard index reference = true := by
  rcases (NativeQueryDemand.mask_exact ..).mp needed with ⟨samePattern, sameReference, sourceChecked⟩
  subst reference
  have atProfile : certificate.available (profiles.get index).model.observationalDist fixed = true :=
    (certificate.available_eq_of_pattern_eq samePattern fixed).trans available
  exact certificate.activated_of_available index fixed (ProbabilityResult.supportedOfIsSome _ sourceChecked) atProfile

/-- Restrict the original full proof check to the fixed query mask. All
intermediate demands are preserved by the existing exact checker theorem;
this argument does not replace them with endpoint support alone. -/
theorem query_derivation_checked (certificate : CheckedNativeFormula P.observedGraph profiles)
    (derivation : CheckedDerivation P.observedGraph) (branch : certificate.proof = .derivation derivation)
    (record : FiniteProbRecord S.Assignment) (fixed : S.Assignment)
    (available : certificate.available record fixed = true) :
    checkDerivation profiles (NativeQueryDemand.mask profiles certificate.source (NativeSupportGuard.pattern S record) fixed)
      derivation.derivation = true := by
  have guarded : NativeSupportGuard.check profiles (CheckedNativeProof.derivation derivation).demand certificate.guard = true := by
    simpa only [branch] using certificate.guardChecked
  have activated : checkDerivation profiles (certificate.proof.activatedDemand profiles certificate.guard) derivation.derivation = true := by
    simpa only [branch] using CheckedNativeProof.activated_derivation_checked profiles derivation certificate.guard guarded
  rw [checkDerivation_exact] at activated ⊢
  apply (allNeeded_exact ..).mpr
  intro index reference needed
  exact (allNeeded_exact ..).mp activated index reference
    (certificate.queryDemand_le_activated record fixed available index reference needed)

private theorem derivation_left (certificate : CheckedNativeFormula P.observedGraph profiles)
    (derivation : CheckedDerivation P.observedGraph) (branch : certificate.proof = .derivation derivation) :
    derivation.left = certificate.source := by
  simpa only [branch, CheckedNativeProof.left] using certificate.source_eq

private theorem derivation_right (certificate : CheckedNativeFormula P.observedGraph profiles)
    (derivation : CheckedDerivation P.observedGraph) (branch : certificate.proof = .derivation derivation) :
    derivation.right = certificate.formula := by
  simp only [formula, branch, CheckedNativeProof.right]

/-- Construct one actual trace, with literal encoded endpoints at the
source-based demand. No existential profile or proof is selected. Equality
transports only identify the supplied certificate's original endpoints. -/
def queryTrace (certificate : CheckedNativeFormula P.observedGraph profiles)
    (derivation : CheckedDerivation P.observedGraph) (branch : certificate.proof = .derivation derivation)
    (record : FiniteProbRecord S.Assignment) (fixed : S.Assignment)
    (available : certificate.available record fixed = true) :
    RewriteTrace profiles
      (Term.encode profiles certificate.source (NativeQueryDemand.mask profiles certificate.source (NativeSupportGuard.pattern S record) fixed))
      (Term.encode profiles certificate.formula (NativeQueryDemand.mask profiles certificate.source (NativeSupportGuard.pattern S record) fixed)) :=
  let requested := NativeQueryDemand.mask profiles certificate.source (NativeSupportGuard.pattern S record) fixed
  let path := Path.ofDerivation profiles requested derivation.derivation
    (certificate.query_derivation_checked derivation branch record fixed available)
  (RewriteTrace.ofPath path).reindex
    (congrArg (fun term => Term.encode profiles term requested) (derivation_left certificate derivation branch))
    (congrArg (fun term => Term.encode profiles term requested) (derivation_right certificate derivation branch))

theorem queryTrace_checked (certificate : CheckedNativeFormula P.observedGraph profiles)
    (derivation : CheckedDerivation P.observedGraph) (branch : certificate.proof = .derivation derivation)
    (record : FiniteProbRecord S.Assignment) (fixed : S.Assignment)
    (available : certificate.available record fixed = true) :
    (certificate.queryTrace derivation branch record fixed available).check
      (NativeQueryDemand.mask profiles certificate.source (NativeSupportGuard.pattern S record) fixed) = true := by
  simp only [queryTrace, RewriteTrace.check_reindex, RewriteTrace.ofPath_check, Path.ofDerivation_checked]

/-- Acceptance includes observational availability even if every matching
source is null and the native mask is empty. No source value follows. -/
theorem queryTrace_target_recognized (certificate : CheckedNativeFormula P.observedGraph profiles)
    (derivation : CheckedDerivation P.observedGraph) (branch : certificate.proof = .derivation derivation)
    (record : FiniteProbRecord S.Assignment) (fixed : S.Assignment)
    (available : certificate.available record fixed = true) :
    NativeTargetRecognition.recognize record.support
      (NativeQueryDemand.mask profiles certificate.source (NativeSupportGuard.pattern S record) fixed) fixed
      (Term.encode profiles certificate.formula (NativeQueryDemand.mask profiles certificate.source (NativeSupportGuard.pattern S record) fixed)) = true := by
  have target := (certificate.queryTrace derivation branch record fixed available).target_checks_of_check _
    (certificate.queryTrace_checked derivation branch record fixed available)
  apply (NativeTargetRecognition.recognize_record_iff ..).mpr
  refine ⟨target.1, target.2, ?_, ?_⟩
  · rw [Term.actionFreeCheck_encode]
    exact (ProbabilityTerm.actionFreeCheck_exact certificate.formula).mpr certificate.actionFree
  · rw [Term.erase_encode]
    exact (Bool.and_eq_true_iff.mp available).2

theorem queryTrace_erased_checked (certificate : CheckedNativeFormula P.observedGraph profiles)
    (derivation : CheckedDerivation P.observedGraph) (branch : certificate.proof = .derivation derivation)
    (record : FiniteProbRecord S.Assignment) (fixed : S.Assignment)
    (available : certificate.available record fixed = true) :
    checkDerivation profiles (NativeQueryDemand.mask profiles certificate.source (NativeSupportGuard.pattern S record) fixed)
      (certificate.queryTrace derivation branch record fixed available).toPath.erase.toDerivation = true :=
  (certificate.queryTrace derivation branch record fixed available).erase_checked _
    (certificate.queryTrace_checked derivation branch record fixed available)

end CheckedNativeFormula
end Thesis.Causality.ProbabilityCode
