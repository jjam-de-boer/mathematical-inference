import Thesis.CausalTransport.NativeTraceCertificates
import Thesis.CausalTransport.NativeGuardCompilation
import Thesis.Examples.NativeQueryPaths

namespace Thesis.Causality.Examples.NativeTraceCertificates

open Probability ProbabilityCode NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open NativeGuardedPaths NativeQueryPaths
open Thesis.Causality.NativeDemandTyping Thesis.Causality.NativeDemandEncoding

/-!
# Converse certificates retain the actual query and its application boundary

Reconstruct a product certificate from the supplied common trace, then use
the existing original-model soundness theorem with explicit coverage and
source support. The one-row guard accepts numerical reweightings of its
observed support cell, while refusing other references and support patterns.

Defined zero sources remain supported. A null source can yield an available
printed formula but still has no source value. An empty profile catalogue
also supplies no original-model coverage: its one-row guard is nevertheless
well-formed and checked, whereas the optional compiled guard has no rows.
This exercises the generic converse without adding a representation premise.

The final negative test is about an observationally unavailable *specified*
printed conditional, not failure of graph identification or all alternative
formulas. No trace search, serialized exporter or runtime solver is executed.
-/

def reconstructed := CheckedNativeFormula.ofQueryTrace unitTerm observed (reference 2) directTrace
  two_available_candidates_have_checked_traces.1 both_targets_are_recognized.1

theorem literal_source_and_formula_are_preserved :
    reconstructed.source = unitTerm ∧ reconstructed.formula = productTerm := by
  constructor
  · rfl
  · exact Term.erase_encode guardProfiles productTerm NativeQueryPaths.requested

theorem reconstructed_is_available : reconstructed.available observed (reference 2) = true :=
  CheckedNativeFormula.ofQueryTrace_available unitTerm observed (reference 2) directTrace
    two_available_candidates_have_checked_traces.1 both_targets_are_recognized.1

theorem reweighted_law_is_accepted :
    reconstructed.available entry.uniformSupport.model.observationalDist (reference 2) = true :=
  (CheckedNativeFormula.ofQueryTrace_available_iff unitTerm observed (reference 2) directTrace
    two_available_candidates_have_checked_traces.1 both_targets_are_recognized.1 _ _).mpr
      ⟨congrArg (fun support => signature.assignmentEnumeration.map support) same_causal_support.observational_support, rfl⟩

theorem another_reference_is_refused : reconstructed.available observed (reference 0) ≠ true := by
  intro accepted
  have atCell := (CheckedNativeFormula.ofQueryTrace_available_iff unitTerm observed (reference 2) directTrace
    two_available_candidates_have_checked_traces.1 both_targets_are_recognized.1 observed (reference 0)).mp accepted
  have different : reference 0 ≠ reference 2 := by decide +kernel
  exact different atCell.2

theorem another_support_pattern_is_refused :
    reconstructed.available fullSupport.model.observationalDist (reference 2) ≠ true := by
  intro accepted
  have atCell := (CheckedNativeFormula.ofQueryTrace_available_iff unitTerm observed (reference 2) directTrace
    two_available_candidates_have_checked_traces.1 both_targets_are_recognized.1 _ _).mp accepted
  have different : NativeSupportGuard.pattern signature fullSupport.model.observationalDist ≠ observedPattern := by decide +kernel
  exact different atCell.1

/-- This is the old soundness application with its actual source witness
and support-agreeing representative. Availability alone is not an input
substitute for either premise. -/
noncomputable def reconstructed_original_application :
    entry.model.TermEquivalentAt unitTerm productTerm (reference 2) := by
  have result := reconstructed.soundAt entry.model rfl
    ⟨entry.uniformSupport, List.mem_cons.mpr (Or.inl rfl), same_causal_support⟩ (reference 2)
    (ProbabilityResult.supportedOfIsSome _ (by decide +kernel)) reconstructed_is_available
  simpa only [literal_source_and_formula_are_preserved.1, literal_source_and_formula_are_preserved.2] using result

def zeroRequested : Demand guardProfiles := NativeQueryDemand.mask guardProfiles .zero observedPattern (reference 2)
def zeroTree : Term guardProfiles := Term.encode guardProfiles .zero zeroRequested
def zeroTrace := RewriteTrace.nil zeroTree
def zeroCertificate := CheckedNativeFormula.ofQueryTrace .zero observed (reference 2) zeroTrace
  (by decide +kernel) (by decide +kernel)

theorem defined_zero_remains_supported :
    zeroCertificate.available observed (reference 2) = true ∧
      (entry.model.termDenote zeroCertificate.source (reference 2)).isSome = true :=
  ⟨CheckedNativeFormula.ofQueryTrace_available .zero observed (reference 2) zeroTrace
    (by decide +kernel) (by decide +kernel), by decide +kernel⟩

def nullCertificate := CheckedNativeFormula.ofQueryTrace unitFormula.source observed (reference 2) nullSourceTrace
  unused_null_source_trace_is_checked
  (unitFormula.queryTrace_target_recognized carrierProof rfl observed (reference 2) (by decide +kernel))

theorem a_null_source_gains_no_value :
    nullCertificate.available observed (reference 2) = true ∧
      (entry.model.termDenote nullCertificate.source (reference 2)).isSome = false :=
  ⟨CheckedNativeFormula.ofQueryTrace_available unitFormula.source observed (reference 2) nullSourceTrace
    unused_null_source_trace_is_checked
    (unitFormula.queryTrace_target_recognized carrierProof rfl observed (reference 2) (by decide +kernel)), by decide +kernel⟩

def emptyProfiles : List (NativeTemplateInstance projection) := []
def emptyRequested : Demand emptyProfiles := NativeQueryDemand.mask emptyProfiles unitTerm observedPattern (reference 2)
def emptyTree : Term emptyProfiles := Term.encode emptyProfiles unitTerm emptyRequested
def emptyTrace := RewriteTrace.nil emptyTree
def emptyCertificate := CheckedNativeFormula.ofQueryTrace unitTerm observed (reference 2) emptyTrace
  (by decide +kernel) (by decide +kernel)

/-- The compiled guard's existing represented-pattern qualification is
essential here. The point guard needs no such additional premise, but the
empty catalogue still cannot cover an original causal model. -/
theorem empty_catalogue_guard_boundary :
    emptyCertificate.available observed (reference 2) = true ∧
      NativeSupportGuard.accepts (NativeSupportGuard.compile emptyProfiles emptyCertificate.proof.demand)
        observed (reference 2) = false :=
  ⟨CheckedNativeFormula.ofQueryTrace_available unitTerm observed (reference 2) emptyTrace
    (by decide +kernel) (by decide +kernel), rfl⟩

def pairedReconstructed := CheckedNativeFormula.ofQueryTrace unitTerm observed (reference 2) pairedTrace
  one_common_trace_checks_both_profiles
  (pairedCertificate.queryTrace_target_recognized directProof rfl observed (reference 2) (by decide +kernel))

theorem paired_guard_checks_every_matching_profile :
    pairedReconstructed.proof.demand projection entry.model (reference 2) = true ∧
      pairedReconstructed.proof.demand projection entry.uniformSupport.model (reference 2) = true := by
  have every := (NativeSupportGuard.point_checked_iff ..).mp pairedReconstructed.guardChecked
  constructor
  · exact every entry (List.mem_cons.mpr (Or.inl rfl)) rfl
  · exact every entry.uniformSupport (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      (congrArg (fun support => signature.assignmentEnumeration.map support) same_causal_support.observational_support).symm

/-- Exercise the equivalence's forward direction with an actual existing
certificate. Its reverse direction is the constructor used above. -/
theorem existing_certificate_has_a_recognized_trace :
    ∃ trace : RewriteTrace guardProfiles (Term.encode guardProfiles unitTerm NativeQueryPaths.requested)
      (Term.encode guardProfiles productTerm NativeQueryPaths.requested),
      trace.check NativeQueryPaths.requested = true ∧
      NativeTargetRecognition.recognize observed.support NativeQueryPaths.requested (reference 2)
        (Term.encode guardProfiles productTerm NativeQueryPaths.requested) = true :=
  (query_certificate_iff_trace unitTerm productTerm observed (reference 2)).mp
    ⟨directCertificate, rfl, rfl, directProof, rfl, by decide +kernel⟩

theorem unavailable_target_has_no_available_derivation_certificate :
    ¬ ∃ certificate : CheckedNativeFormula projection.observedGraph guardProfiles,
      certificate.source = unitTerm ∧ certificate.formula = .kernel carrier ∧
      ∃ derivation : CheckedDerivation projection.observedGraph, certificate.proof = .derivation derivation ∧
        certificate.available observed (reference 2) = true := by
  intro supplied
  rcases (query_certificate_iff_trace unitTerm (.kernel carrier) observed (reference 2)).mp supplied with
    ⟨trace, _checked, recognized⟩
  have refused : NativeTargetRecognition.recognize observed.support NativeQueryPaths.requested (reference 2)
      (Term.encode guardProfiles (.kernel carrier) NativeQueryPaths.requested) = false := by decide +kernel
  exact Bool.noConfusion (refused.symm.trans recognized)

end Thesis.Causality.Examples.NativeTraceCertificates
