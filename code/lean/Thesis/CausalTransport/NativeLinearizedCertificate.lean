import Thesis.CausalTransport.NativeDerivationLinearization
import Thesis.CausalTransport.NativeCertificateCheck

namespace Thesis.Causality.ProbabilityCode

/-!
# Preserve accepted native certificates while linearizing their proof

Only the proof presentation changes. The original source, observational
formula and supplied observable guard remain literally the same, so runtime
availability is unchanged for every record/reference, not just one favorable
profile. Guard certification is transported over every supplied profile.

The semantic graph must be the profiles' actual projected graph. The generic
checker also accepts graph/profile combinations without this agreement, but
its native soundness theorem does not justify such combinations; neither does
this bridge. Fixed-DAG and projection-wide public catalogues both satisfy
the required graph agreement by construction.

`actionOne` remains its separate top-level native theorem. It is not inserted
as a composable do-calculus atom. The bridge transforms reconstructed typed
proofs; it does not add a serialized parser/exporter, a new certificate search,
or a universal stopping theorem. Original conditional-source support remains
an independent premise of every existing soundness application.
-/

open Probability

variable {S : ObservedSignature} {P Q : FiniteLatentProjection S}
variable {graph : ObservedGraph S} {profiles : List (NativeTemplateInstance Q)}

namespace CheckedNativeProof

def linearized : CheckedNativeProof graph → CheckedNativeProof graph
  | .derivation checked => .derivation ⟨checked.left, checked.right, checked.derivation.linearize.toDerivation⟩
  | .actionOne kernel => .actionOne kernel

theorem linearized_left (proof : CheckedNativeProof graph) : proof.linearized.left = proof.left := by cases proof <;> rfl
theorem linearized_right (proof : CheckedNativeProof graph) : proof.linearized.right = proof.right := by cases proof <;> rfl

/-- Preserve each actual model's old support demand. This is a pointwise
implication for the same transformed proof, not a model-dependent choice of
different paths or a replacement of equality by a support-profile test. -/
theorem linearized_demand (proof : CheckedNativeProof graph)
    (model : FiniteHiddenDAGSCM S P) (graphEqual : graph = P.observedGraph)
    (reference : S.Assignment) (accepted : proof.demand P model reference = true) :
    proof.linearized.demand P model reference = true := by
  cases graphEqual
  cases proof with
  | derivation checked =>
      change (if (model.termDenote checked.left reference).isSome && (model.termDenote checked.right reference).isSome then
        HiddenDAGLocalDerivationSupport.check model reference checked.derivation.linearize.toDerivation else true) = true
      change (if (model.termDenote checked.left reference).isSome && (model.termDenote checked.right reference).isSome then
        HiddenDAGLocalDerivationSupport.check model reference checked.derivation else true) = true at accepted
      split at accepted
      next endpoints =>
        rw [if_pos endpoints]
        exact checked.derivation.linearize_toDerivation_check model reference accepted
      next endpoints => rw [if_neg endpoints]
  | actionOne kernel => exact accepted

/-- Every matching profile is checked, including a later profile with the
same observed pattern. No finite-profile witness is selected or discarded. -/
theorem linearized_guardChecked (proof : CheckedNativeProof graph)
    (graphEqual : graph = Q.observedGraph) (guard : NativeSupportGuard.Code)
    (accepted : NativeSupportGuard.check profiles proof.demand guard = true) :
    NativeSupportGuard.check profiles proof.linearized.demand guard = true := by
  apply List.all_eq_true.mpr
  intro cell listed
  have oldCell := (List.all_eq_true.mp accepted) cell listed
  cases decoded : ProbabilityCode.assignment S cell.reference with
  | none => simp only [NativeSupportGuard.checkCell, decoded, Bool.false_eq_true] at oldCell
  | some reference =>
      simp only [NativeSupportGuard.checkCell, decoded] at oldCell ⊢
      apply List.all_eq_true.mpr
      intro entry member
      by_cases samePattern : cell.observed = NativeSupportGuard.pattern S entry.model.observationalDist
      · have demand := (List.all_eq_true.mp oldCell) entry member
        rw [if_pos samePattern]
        exact proof.linearized_demand entry.model graphEqual reference (by simpa only [if_pos samePattern] using demand)
      · simp only [if_neg samePattern]

end CheckedNativeProof

namespace CheckedNativeFormula

/-- Keep the entire certified application boundary unchanged while replacing
the old proof tree by its elementary-path reinterpretation. This is proof
data reconstruction, not an extension of the untrusted serialized language. -/
def linearized (checked : CheckedNativeFormula graph profiles) (graphEqual : graph = Q.observedGraph) :
    CheckedNativeFormula graph profiles where
  source := checked.source
  proof := checked.proof.linearized
  source_eq := checked.proof.linearized_left.trans checked.source_eq
  actionFree := by rw [CheckedNativeProof.linearized_right]; exact checked.actionFree
  guard := checked.guard
  guardChecked := checked.proof.linearized_guardChecked graphEqual checked.guard checked.guardChecked

theorem linearized_source (checked : CheckedNativeFormula graph profiles) (graphEqual : graph = Q.observedGraph) :
    (checked.linearized graphEqual).source = checked.source := rfl

theorem linearized_formula (checked : CheckedNativeFormula graph profiles) (graphEqual : graph = Q.observedGraph) :
    (checked.linearized graphEqual).formula = checked.formula := checked.proof.linearized_right

theorem linearized_guard (checked : CheckedNativeFormula graph profiles) (graphEqual : graph = Q.observedGraph) :
    (checked.linearized graphEqual).guard = checked.guard := rfl

/-- Availability is equal for arbitrary input records, not merely included
on the finite profiles. In particular a null original target is not silently
made supported by changing its proof presentation. -/
theorem linearized_available (checked : CheckedNativeFormula graph profiles) (graphEqual : graph = Q.observedGraph)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) :
    (checked.linearized graphEqual).available record reference = checked.available record reference := by
  unfold available
  rw [linearized_guard, linearized_formula]

end CheckedNativeFormula
end Thesis.Causality.ProbabilityCode
