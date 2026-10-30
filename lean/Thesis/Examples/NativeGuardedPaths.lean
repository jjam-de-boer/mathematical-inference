import Thesis.CausalTransport.NativeGuardedPaths
import Thesis.Examples.NativeDemandPaths

namespace Thesis.Causality.Examples.NativeGuardedPaths

open Probability ProbabilityCode NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping Thesis.Causality.NativeDemandEncoding

/-!
# Guard acceptance, source support and printed availability stay separate

The old null-carrier certificate is available observationally, but its source
conditional is undefined. Its guard check is legitimate and vacuous there;
using that check as an unconditional full-proof check would be wrong. The
activated demand instead omits this cell without assigning it a causal value.
The reverse certificate tests an unavailable printed formula with a supported
source. A direct chain certificate then exercises a real active application.

Full-proof conversion also retains unsupported intermediate terms and a
changing-weight congruence across conflicting profiles. Mixed-profile output
is certified by the general preservation theorem, with its input support
computed in the kernel; no native-evaluation axiom or runtime pilot is used.
-/

def guardProfiles := NativeKernelInterfaceObstruction.profiles
def guardIndex : Fin guardProfiles.length := ⟨0, by decide⟩
def requested : Demand family := atReference (reference 2)

def carrierProof : CheckedDerivation projection.observedGraph := ⟨.kernel carrier, unitTerm, eraseNullCondition⟩
def carrierDemand := (CheckedNativeProof.derivation carrierProof).activatedDemand guardProfiles unitFormula.guard
def carrierPath := CheckedNativeProof.derivationPath guardProfiles carrierProof unitFormula.guard unitFormula.guardChecked

theorem guard_is_not_unconditional_proof_support :
    unitFormula.available (guardProfiles.get guardIndex).model.observationalDist (reference 2) = true ∧
      ((guardProfiles.get guardIndex).model.termDenote unitFormula.source (reference 2)).isSome = false ∧
      checkDerivation guardProfiles
        (fun index value => NativeSupportGuard.accepts unitFormula.guard (guardProfiles.get index).model.observationalDist value)
        carrierProof.derivation = false ∧ carrierDemand guardIndex (reference 2) = false := by decide +kernel

/-- This path is checked only at its activated cells; its vacuous null cell
does not supply the separate source witness required by soundness. -/
theorem carrier_path_checked : carrierPath.check carrierDemand = true :=
  CheckedNativeProof.derivationPath_checked guardProfiles carrierProof unitFormula.guard unitFormula.guardChecked

def directProof : CheckedDerivation projection.observedGraph := ⟨unitTerm, productTerm, expandUnit⟩
def directCertificate : CheckedNativeFormula projection.observedGraph guardProfiles where
  source := unitTerm
  proof := .derivation directProof
  source_eq := rfl
  actionFree := productFormula.actionFree
  guard := [nullCell]
  guardChecked := by decide +kernel

def directPath := CheckedNativeProof.derivationPath guardProfiles directProof directCertificate.guard directCertificate.guardChecked

theorem supported_application_is_activated :
    directCertificate.proof.activatedDemand guardProfiles directCertificate.guard guardIndex (reference 2) = true :=
  directCertificate.activated_of_available guardIndex (reference 2)
    (ProbabilityResult.supportedOfIsSome _ (by decide +kernel)) (by decide +kernel)

theorem original_linearized_path_is_recovered : directPath.eraseData = ⟨unitTerm, productTerm, expandUnit.linearize⟩ :=
  CheckedNativeProof.eraseData_derivationPath guardProfiles directProof directCertificate.guard directCertificate.guardChecked

def reverseProof : CheckedDerivation projection.observedGraph := ⟨unitTerm, .kernel carrier, .symm eraseNullCondition⟩
def reverseCertificate : CheckedNativeFormula projection.observedGraph guardProfiles where
  source := unitTerm
  proof := .derivation reverseProof
  source_eq := rfl
  actionFree := by intro _; rfl
  guard := [nullCell]
  guardChecked := by decide +kernel

theorem unavailable_printed_formula_is_not_activated :
    ((guardProfiles.get guardIndex).model.termDenote reverseCertificate.source (reference 2)).isSome = true ∧
      reverseCertificate.available (guardProfiles.get guardIndex).model.observationalDist (reference 2) = false ∧
      reverseCertificate.proof.activatedDemand guardProfiles reverseCertificate.guard guardIndex (reference 2) = false := by decide +kernel

theorem full_proof_keeps_intermediate_support :
    (Path.ofDerivation? family requested carrierDetour).isSome = false ∧
      (Path.ofDerivation? family (atReference (reference 0)) carrierDetour).map
        (fun path => path.check (atReference (reference 0))) = some true := by decide +kernel

def mixedOriginal := NativeDemandSteps.changingWeight.toDerivation
def mixedPath := Path.ofDerivation conflicting NativeDemandSteps.mixedRequested mixedOriginal (by decide +kernel)

theorem full_proof_uses_one_path_for_both_profiles : mixedPath.check NativeDemandSteps.mixedRequested = true :=
  Path.ofDerivation_checked conflicting NativeDemandSteps.mixedRequested mixedOriginal (by decide +kernel)

theorem mixed_original_linearization_is_recovered : mixedPath.eraseData = ⟨_, _, mixedOriginal.linearize⟩ :=
  Path.eraseData_ofDerivation conflicting NativeDemandSteps.mixedRequested mixedOriginal (by decide +kernel)

end Thesis.Causality.Examples.NativeGuardedPaths
