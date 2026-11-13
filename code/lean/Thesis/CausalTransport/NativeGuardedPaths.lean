import Thesis.CausalTransport.NativeDerivationPaths
import Thesis.CausalTransport.NativeCertificateCheck

namespace Thesis.Causality.ProbabilityCode

open Probability NativeDemandTyping NativeDemandEncoding

/-!
# Guarded derivation certificates retain their real application boundary

A native proof's guard demand is deliberately vacuous when an endpoint is
undefined. It therefore cannot be used as an unconditional full-path support
proof on every guarded cell. The activated demand below retains a cell only
when the observable guard passes and both original endpoints have values.
On precisely those cells, guard certification supplies the full proof check.

Only the derivation branch is assembled into a typed path. `actionOne` keeps
its separate native theorem and guard, rather than becoming a composable
path leaf. The original certificate is an input and remains unchanged: its
source-support premise and printed observational availability are separate.
The last theorem shows that every original, genuinely supported application
activates its cell; an empty mask is never offered as a new probability value.

No serialized exporter, context-closure theorem or search is introduced here.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

namespace CheckedNativeProof

def activatedDemand (proof : CheckedNativeProof P.observedGraph)
    (profiles : List (NativeTemplateInstance P)) (guard : NativeSupportGuard.Code) : NativeDemandTyping.Demand profiles :=
  fun index reference => NativeSupportGuard.accepts guard (profiles.get index).model.observationalDist reference &&
    proof.endpoints P (profiles.get index).model reference

/-- Read guard safety at an actual supplied profile, using that same entry
as the explicit coverage witness. No representative model is chosen. -/
private theorem demand_at_profile (proof : CheckedNativeProof P.observedGraph)
    (profiles : List (NativeTemplateInstance P)) (guard : NativeSupportGuard.Code)
    (checked : NativeSupportGuard.check profiles proof.demand guard = true)
    (index : Fin profiles.length) (reference : S.Assignment)
    (atGuard : NativeSupportGuard.accepts guard (profiles.get index).model.observationalDist reference = true) :
    proof.demand P (profiles.get index).model reference = true :=
  NativeSupportGuard.soundAt profiles proof.demand proof.demand_invariant guard checked
    (profiles.get index).model
    ⟨profiles.get index, List.get_mem profiles index, CausalSupportAgreement.refl _⟩ reference atGuard

theorem activated_derivation_checked (profiles : List (NativeTemplateInstance P))
    (derivation : CheckedDerivation P.observedGraph) (guard : NativeSupportGuard.Code)
    (checked : NativeSupportGuard.check profiles (CheckedNativeProof.derivation derivation).demand guard = true) :
    checkDerivation profiles ((CheckedNativeProof.derivation derivation).activatedDemand profiles guard) derivation.derivation = true := by
  rw [checkDerivation_exact]
  apply (allNeeded_exact ..).mpr
  intro index reference needed
  have active := Bool.and_eq_true_iff.mp needed
  have demanded := demand_at_profile (.derivation derivation) profiles guard checked index reference active.1
  simpa only [demand, active.2, if_true] using demanded

/-- The type retains the original two terms and the activated outer demand.
The caller supplies the existing checked guard; no new guard is generated. -/
def derivationPath (profiles : List (NativeTemplateInstance P))
    (derivation : CheckedDerivation P.observedGraph) (guard : NativeSupportGuard.Code)
    (checked : NativeSupportGuard.check profiles (CheckedNativeProof.derivation derivation).demand guard = true) :
    Path profiles
      (Term.encode profiles derivation.left ((CheckedNativeProof.derivation derivation).activatedDemand profiles guard))
      (Term.encode profiles derivation.right ((CheckedNativeProof.derivation derivation).activatedDemand profiles guard)) :=
  Path.ofDerivation profiles _ derivation.derivation (activated_derivation_checked profiles derivation guard checked)

theorem derivationPath_checked (profiles : List (NativeTemplateInstance P))
    (derivation : CheckedDerivation P.observedGraph) (guard : NativeSupportGuard.Code)
    (checked : NativeSupportGuard.check profiles (CheckedNativeProof.derivation derivation).demand guard = true) :
    (derivationPath profiles derivation guard checked).check
      ((CheckedNativeProof.derivation derivation).activatedDemand profiles guard) = true :=
  Path.ofDerivation_checked profiles _ derivation.derivation (activated_derivation_checked profiles derivation guard checked)

theorem eraseData_derivationPath (profiles : List (NativeTemplateInstance P))
    (derivation : CheckedDerivation P.observedGraph) (guard : NativeSupportGuard.Code)
    (checked : NativeSupportGuard.check profiles (CheckedNativeProof.derivation derivation).demand guard = true) :
    (derivationPath profiles derivation guard checked).eraseData = ⟨derivation.left, derivation.right, derivation.derivation.linearize⟩ :=
  Path.eraseData_ofDerivation profiles _ derivation.derivation (activated_derivation_checked profiles derivation guard checked)

end CheckedNativeProof

namespace CheckedNativeFormula

/-- Preserve every existing application: observable availability plus the
original source witness activates the exact profile/reference cell. This is
not a converse granting source support from guard or formula availability. -/
theorem activated_of_available {profiles : List (NativeTemplateInstance P)}
    (certificate : CheckedNativeFormula P.observedGraph profiles) (index : Fin profiles.length) (reference : S.Assignment)
    (sourceSupported : (profiles.get index).model.TermSupportedAt certificate.source reference)
    (available : certificate.available (profiles.get index).model.observationalDist reference = true) :
    certificate.proof.activatedDemand profiles certificate.guard index reference = true := by
  have accepted := Bool.and_eq_true_iff.mp available
  apply Bool.and_eq_true_iff.mpr
  refine ⟨accepted.1, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · rw [certificate.source_eq]
    exact ProbabilityResult.supported_isSome sourceSupported
  · rw [← ProbabilityTerm.observationalDenote_eq_native (profiles.get index).model certificate.proof.right certificate.actionFree reference]
    exact accepted.2

end CheckedNativeFormula
end Thesis.Causality.ProbabilityCode
