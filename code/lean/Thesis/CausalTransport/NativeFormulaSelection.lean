import Thesis.CausalTransport.NativeCertificateCheck

namespace Thesis.Causality

open Probability

/-!
# Observable selection retaining native support-table guards

Scan a supplied finite list of checked native formulas in its given order.
Availability checks the actual support table and the partial observational
expression. A defined zero is a value; an undefined conditional is not.
Neither hidden mechanisms nor causal source support are inspected by search.

The older `ObservationalFormulaPlan` has only two guard constructors. Native
support tables must not be erased to coerce these certificates into that API.
Instead this small scan retains each complete `CheckedNativeFormula` record.
Proof fields are erased at execution; selection uses its observable data.

The scan reuses `List.find?` and its membership, acceptance and failure
lemmas rather than duplicating list induction. Finite-family completeness
remains a separate theorem. Lists here need not share a source: generic
soundness concerns the selected record's actual source. The bounded adapter separately
proves that every generated member retains the user's decoded source query.
Conditional-source support and model/profile coverage remain explicit native
soundness premises. An empty selection is not general non-identifiability.
-/

variable {S : ObservedSignature.{0}} {P Q : FiniteLatentProjection S}
variable {graph : ObservedGraph S} {profiles : List (NativeTemplateInstance Q)}

/-- Checking a certificate retains the literal decoded input query. This
bridge exposes data already stored by the checker; no source is selected
from a propositional existence claim or replaced by a printed endpoint. -/
theorem ProbabilityCode.NativeCertificateCode.checkOn_source
    (code : ProbabilityCode.NativeCertificateCode)
    (checked : ProbabilityCode.CheckedNativeFormula graph profiles)
    (accepted : code.checkOn graph profiles = some checked) :
    code.source.decode S = some checked.source := by
  cases decoded : code.source.decode S with
  | none =>
      simp only [ProbabilityCode.NativeCertificateCode.checkOn, decoded, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at accepted
  | some source =>
      cases decodedProof : code.proof.check graph with
      | none =>
          simp only [ProbabilityCode.NativeCertificateCode.checkOn, decoded, Option.bind_eq_bind, Option.bind_some,
            decodedProof, Option.bind_none, reduceCtorEq] at accepted
      | some proof =>
          by_cases same : proof.left = source
          · by_cases actionFree : proof.right.actionFreeCheck = true
            · by_cases guardChecked : NativeSupportGuard.check profiles proof.demand code.guard = true
              · have result : (⟨source, proof, same,
                    (ProbabilityTerm.actionFreeCheck_exact proof.right).mp actionFree,
                    code.guard, guardChecked⟩ : ProbabilityCode.CheckedNativeFormula graph profiles) = checked := Option.some.inj (by
                  simpa only [ProbabilityCode.NativeCertificateCode.checkOn, decoded, Option.bind_eq_bind, Option.bind_some, decodedProof,
                    dif_pos same, dif_pos actionFree, dif_pos guardChecked, Option.pure_def] using accepted)
                rw [← result]
              · simp only [ProbabilityCode.NativeCertificateCode.checkOn, decoded, Option.bind_eq_bind, Option.bind_some, decodedProof,
                  dif_pos same, dif_pos actionFree, dif_neg guardChecked, reduceCtorEq] at accepted
            · simp only [ProbabilityCode.NativeCertificateCode.checkOn, decoded, Option.bind_eq_bind, Option.bind_some, decodedProof,
                dif_pos same, dif_neg actionFree, reduceCtorEq] at accepted
          · simp only [ProbabilityCode.NativeCertificateCode.checkOn, decoded, Option.bind_eq_bind, Option.bind_some, decodedProof,
              dif_neg same, reduceCtorEq] at accepted

namespace ProbabilityCode.CheckedNativeFormula

/-- First available supplied certificate. All native guards are retained;
this definition neither generates profiles nor admits a search budget. -/
def select (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) :
    List (CheckedNativeFormula graph profiles) → Option (CheckedNativeFormula graph profiles) :=
  List.find? (fun candidate => candidate.available record reference)

theorem select_cons_of_available (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (candidate : CheckedNativeFormula graph profiles) (candidates : List (CheckedNativeFormula graph profiles))
    (accepted : candidate.available record reference = true) :
    select record reference (candidate :: candidates) = some candidate := by
  simp only [select, List.find?_cons, accepted]

/-- A rejected first candidate cannot mask an available later candidate. -/
theorem select_cons_of_unavailable (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (candidate : CheckedNativeFormula graph profiles) (candidates : List (CheckedNativeFormula graph profiles))
    (rejected : candidate.available record reference = false) :
    select record reference (candidate :: candidates) = select record reference candidates := by
  simp only [select, List.find?_cons, rejected]

/-- The scan cannot invent an unchecked fallback. It returns an actual
member, including that member's original guard and native proof. -/
theorem select_mem (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (candidates : List (CheckedNativeFormula graph profiles)) (chosen : CheckedNativeFormula graph profiles)
    (selected : select record reference candidates = some chosen) : chosen ∈ candidates :=
  List.mem_of_find?_eq_some selected

theorem select_available (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (candidates : List (CheckedNativeFormula graph profiles)) (chosen : CheckedNativeFormula graph profiles)
    (selected : select record reference candidates = some chosen) : chosen.available record reference = true :=
  List.find?_some (p := fun candidate : CheckedNativeFormula graph profiles =>
    candidate.available record reference) selected

/-- Exact failure only within this list. In particular, failure says nothing
about a formula absent from the list or a larger serialized proof budget. -/
theorem select_none_iff (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (candidates : List (CheckedNativeFormula graph profiles)) :
    select record reference candidates = none ↔
      ∀ candidate, candidate ∈ candidates → candidate.available record reference = false := by
  simpa only [select, Bool.eq_false_iff] using
    (List.find?_eq_none (p := fun candidate => candidate.available record reference) (l := candidates))

theorem select_complete (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (candidates : List (CheckedNativeFormula graph profiles))
    (available : ∃ candidate, candidate ∈ candidates ∧ candidate.available record reference = true) :
    ∃ chosen, select record reference candidates = some chosen := by
  cases result : select record reference candidates with
  | some chosen => exact ⟨chosen, rfl⟩
  | none =>
      rcases available with ⟨candidate, listed, accepted⟩
      have unavailable := (select_none_iff record reference candidates).mp result candidate listed
      rw [accepted] at unavailable
      cases unavailable

/-- Selection does not manufacture original conditional support. The
application supplies that premise and actual coverage of this native model. -/
noncomputable def select_soundAt (model : FiniteHiddenDAGSCM S P)
    (graphEqual : graph = P.observedGraph)
    (covered : ∃ entry, entry ∈ profiles ∧ CausalSupportAgreement entry.model model)
    (reference : S.Assignment) (candidates : List (CheckedNativeFormula graph profiles))
    (chosen : CheckedNativeFormula graph profiles)
    (selected : select model.observationalDist reference candidates = some chosen)
    (sourceSupported : model.TermSupportedAt chosen.source reference) :
    model.TermEquivalentAt chosen.source chosen.formula reference :=
  chosen.soundAt model graphEqual covered reference sourceSupported
    (select_available model.observationalDist reference candidates chosen selected)

end ProbabilityCode.CheckedNativeFormula
end Thesis.Causality
