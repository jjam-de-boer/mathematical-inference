import Thesis.CausalTransport.NativeQueryPaths
import Thesis.Examples.NativeGuardedPaths

namespace Thesis.Causality.Examples.NativeQueryPaths

open Probability ProbabilityCode NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open NativeGuardedPaths
open Thesis.Causality.NativeDemandTyping Thesis.Causality.NativeDemandEncoding

/-!
# Fixed query masks across candidates, reweightings and matching profiles

The observed law here is the original nonuniform three-valued law; its
uniform support representative has different positive numerical weights.
Both the query mask and candidate availability survive that reweighting.

A direct product certificate and a reflexive unit certificate share their
source mask despite different printed terms and guard domains. An unavailable
reverse certificate must use that same mask; it cannot hide its null printed
conditional by changing the request. A null source can instead leave the mask
empty, but still acquires no source-support witness or probability value.

The paired fixture retains both matching profiles in one actual trace. Full
proof checks still reject a null intermediate detour. These are small input
checks and applications of the general trace theorems, not normalization of
equality transports, formula enumeration or a search execution pilot.
-/

def observed : FiniteProbRecord signature.Assignment := entry.model.observationalDist
def observedPattern : List Bool := NativeSupportGuard.pattern signature observed
def requested : Demand guardProfiles := NativeQueryDemand.mask guardProfiles unitTerm observedPattern (reference 2)

def unitProof : CheckedDerivation projection.observedGraph := ⟨unitTerm, unitTerm, .refl unitTerm⟩

def unitCertificate : CheckedNativeFormula projection.observedGraph guardProfiles where
  source := unitTerm
  proof := .derivation unitProof
  source_eq := rfl
  actionFree := by intro _; rfl
  guard := [⟨[true, true, false], 0⟩, nullCell]
  guardChecked := by decide +kernel

theorem candidates_share_the_fixed_mask :
    NativeQueryDemand.mask guardProfiles unitCertificate.source observedPattern (reference 2) =
      NativeQueryDemand.mask guardProfiles directCertificate.source observedPattern (reference 2) ∧
    NativeQueryDemand.mask guardProfiles directCertificate.source observedPattern (reference 2) =
      NativeQueryDemand.mask guardProfiles reverseCertificate.source observedPattern (reference 2) := ⟨rfl, rfl⟩

/-- Different guard domains still give different old activated masks.
They have no influence on the new fixed source/observed-cell request. -/
theorem old_guard_domains_remain_distinct :
    unitCertificate.proof.activatedDemand guardProfiles unitCertificate.guard guardIndex (reference 0) = true ∧
      directCertificate.proof.activatedDemand guardProfiles directCertificate.guard guardIndex (reference 0) = false := by
  decide +kernel

theorem fixed_mask_keeps_only_its_reference :
    requested guardIndex (reference 2) = true ∧ requested guardIndex (reference 0) = false := by decide +kernel

theorem reweighting_keeps_the_mask :
    NativeQueryDemand.mask guardProfiles unitTerm (NativeSupportGuard.pattern signature entry.uniformSupport.model.observationalDist) (reference 2) =
      NativeQueryDemand.mask guardProfiles unitTerm observedPattern (reference 2) :=
  NativeQueryDemand.mask_eq_of_support_eq guardProfiles unitTerm same_causal_support.observational_support (reference 2)

theorem reweighting_keeps_availability :
    directCertificate.available entry.uniformSupport.model.observationalDist (reference 2) =
      directCertificate.available observed (reference 2) :=
  directCertificate.available_eq_of_pattern_eq
    (congrArg (fun support => signature.assignmentEnumeration.map support) same_causal_support.observational_support) (reference 2)

/-- Native intervention support is inspected directly. A factually null
reference may still have a defined intervened source; factual positivity
alone would wrongly discard this demanded cell. -/
theorem native_source_support_controls_the_mask :
    observed.support (reference 2) = false ∧
      NativeQueryDemand.mask guardProfiles forcedConditional observedPattern (reference 2) guardIndex (reference 2) = true ∧
      NativeQueryDemand.mask guardProfiles .zero observedPattern (reference 2) guardIndex (reference 2) = true ∧
      NativeQueryDemand.mask guardProfiles nullConditional observedPattern (reference 2) guardIndex (reference 2) = false := by
  decide +kernel

def directTrace := directCertificate.queryTrace directProof rfl observed (reference 2) (by decide +kernel)
def reflexiveTrace := unitCertificate.queryTrace unitProof rfl observed (reference 2) (by decide +kernel)

theorem two_available_candidates_have_checked_traces :
    directTrace.check requested = true ∧ reflexiveTrace.check requested = true :=
  ⟨directCertificate.queryTrace_checked directProof rfl observed (reference 2) (by decide +kernel),
    unitCertificate.queryTrace_checked unitProof rfl observed (reference 2) (by decide +kernel)⟩

theorem both_targets_are_recognized :
    NativeTargetRecognition.recognize observed.support requested (reference 2) (Term.encode guardProfiles productTerm requested) = true ∧
      NativeTargetRecognition.recognize observed.support requested (reference 2) (Term.encode guardProfiles unitTerm requested) = true :=
  ⟨directCertificate.queryTrace_target_recognized directProof rfl observed (reference 2) (by decide +kernel),
    unitCertificate.queryTrace_target_recognized unitProof rfl observed (reference 2) (by decide +kernel)⟩

theorem old_full_checker_accepts_the_reconstructed_trace :
    checkDerivation guardProfiles requested directTrace.toPath.erase.toDerivation = true :=
  directCertificate.queryTrace_erased_checked directProof rfl observed (reference 2) (by decide +kernel)

theorem unavailable_target_cannot_shrink_the_mask :
    NativeQueryDemand.mask guardProfiles reverseCertificate.source observedPattern (reference 2) guardIndex (reference 2) = true ∧
      reverseCertificate.proof.activatedDemand guardProfiles reverseCertificate.guard guardIndex (reference 2) = false ∧
      reverseCertificate.available observed (reference 2) = false ∧
      NativeTargetRecognition.recognize observed.support requested (reference 2)
        (Term.encode guardProfiles reverseCertificate.formula requested) = false := by
  decide +kernel

def nullRequested : Demand guardProfiles := NativeQueryDemand.mask guardProfiles unitFormula.source observedPattern (reference 2)
def nullSourceTrace := unitFormula.queryTrace carrierProof rfl observed (reference 2) (by decide +kernel)

theorem empty_source_mask_is_not_a_source_value :
    unitFormula.available observed (reference 2) = true ∧
      nullRequested guardIndex (reference 2) = false ∧
      ((guardProfiles.get guardIndex).model.termDenote unitFormula.source (reference 2)).isSome = false := by
  decide +kernel

theorem unused_null_source_trace_is_checked : nullSourceTrace.check nullRequested = true :=
  unitFormula.queryTrace_checked carrierProof rfl observed (reference 2) (by decide +kernel)

theorem genuine_original_application_is_retained : requested guardIndex (reference 2) = true :=
  NativeQueryDemand.at_covered guardProfiles unitTerm entry.model guardIndex same_causal_support (reference 2)
    (ProbabilityResult.supportedOfIsSome _ (by decide +kernel))

theorem null_intermediate_detour_is_still_rejected :
    checkDerivation guardProfiles requested expandUnit = true ∧
      checkDerivation guardProfiles requested carrierDetour = false := by decide +kernel

def paired : List (NativeTemplateInstance projection) := [entry, entry.uniformSupport]
def pairedRequested : Demand paired := NativeQueryDemand.mask paired unitTerm observedPattern (reference 2)

def pairedCertificate : CheckedNativeFormula projection.observedGraph paired where
  source := unitTerm
  proof := .derivation directProof
  source_eq := rfl
  actionFree := directCertificate.actionFree
  guard := [nullCell]
  guardChecked := by decide +kernel

def pairedTrace := pairedCertificate.queryTrace directProof rfl observed (reference 2) (by decide +kernel)

theorem every_matching_profile_is_retained :
    pairedRequested ⟨0, by decide⟩ (reference 2) = true ∧
      pairedRequested ⟨1, by decide⟩ (reference 2) = true := by decide +kernel

theorem one_common_trace_checks_both_profiles : pairedTrace.check pairedRequested = true :=
  pairedCertificate.queryTrace_checked directProof rfl observed (reference 2) (by decide +kernel)

/-- A profile with another observed support pattern is excluded even when
its source is defined; no record is silently treated as having that pattern. -/
theorem other_observed_patterns_are_excluded :
    NativeQueryDemand.mask conflicting unitTerm observedPattern (reference 2) ⟨0, by decide⟩ (reference 2) = false ∧
      NativeQueryDemand.mask conflicting unitTerm observedPattern (reference 2) ⟨1, by decide⟩ (reference 2) = true := by
  decide +kernel

end Thesis.Causality.Examples.NativeQueryPaths
