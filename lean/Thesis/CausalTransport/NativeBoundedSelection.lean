import Thesis.CausalTransport.NativeFormulaSelection
import Thesis.CausalTransport.NativeSearchMetadata

namespace Thesis.Causality

open Probability

/-!
# Selection from explicitly admitted bounded native catalogues

Admission uses certified domain-size metadata and all existing source,
dictionary, depth, supplied-profile and structural-work gates. Only an
admitted catalogue is scanned. The result deliberately has three forms:

* `Except.error reason`: resource/policy refusal; no negative causal answer.
* `Except.ok none`: this admitted bounded catalogue has no available member.
* `Except.ok (some checked)`: an available checked native formula, with its
  original support-table guard and proof intact.

The complete bounded catalogue is constructed first, not streamed or silently
truncated. Selection checks each visited member once and stops at the first
available one. Its list length is bounded by the admitted raw-code allowance;
this does NOT bound the cost of observational formula evaluation. Existing
profile-comparison allowances concern catalogue certification, not a newly
claimed total runtime bound for scanning. Profiles, the observational record
and cheap metadata remain prepared inputs; their construction is not timed.
No complete profile generator is implicitly executed here.

Common-query preservation is proved below, rather than assuming an arbitrary
list's members have the same source. Semantic soundness keeps actual model
coverage and original conditional-source support explicit. Bounded acceptance
coverage includes every previously accepted supplied guard for a bounded
serialized proof. There is no claim about arbitrary Lean semantic proofs,
larger budgets, universal formula coverage, or a universal stopping criterion.
-/

variable {S : ObservedSignature.{0}} {P Q : FiniteLatentProjection S}

namespace ProbabilityCode

variable {graph : ObservedGraph S} {profiles : List (NativeTemplateInstance Q)}

/-- Guard generation changes neither the decoded input nor the query checked
against the proof's left endpoint. This is a data-preservation bridge. -/
theorem NativeProofCode.compileGuardOn_source (proof : NativeProofCode) (source : TermCode)
    (checked : CheckedNativeFormula graph profiles)
    (accepted : proof.compileGuardOn graph profiles source = some checked) :
    source.decode S = some checked.source := by
  unfold NativeProofCode.compileGuardOn at accepted
  cases checkedInput : (⟨source, proof, []⟩ : NativeCertificateCode).checkOn graph profiles with
  | none => simp only [checkedInput, Option.map_none, reduceCtorEq] at accepted
  | some seed =>
      have same : seed.withCompiledGuard = checked := Option.some.inj
        (by simpa only [checkedInput, Option.map_some] using accepted)
      rw [← same, CheckedNativeFormula.withCompiledGuard_source]
      exact NativeCertificateCode.checkOn_source _ seed checkedInput

namespace NativeProofCode

theorem catalogueOn_source (graph : ObservedGraph S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat) (checked : CheckedNativeFormula graph profiles)
    (member : checked ∈ catalogueOn graph profiles source expressionDepth proofDepth) :
    source.decode S = some checked.source := by
  rcases (mem_catalogueOn_iff graph profiles source expressionDepth proofDepth checked).mp member with
    ⟨proof, _bounded, accepted⟩
  exact proof.compileGuardOn_source source checked accepted

/-- The metadata guard runs before catalogue generation or selection. The
option inside the successful result distinguishes an admitted empty answer
from a refused search, without inventing a causal value for either case. -/
def guardedSelectOnWithMetadata (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) :
    Except SearchRefusal (Option (CheckedNativeFormula graph profiles)) :=
  (guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth).map
    (CheckedNativeFormula.select record reference)

theorem guardedSelectOnWithMetadata_of_admission (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (catalogue : List (CheckedNativeFormula graph profiles))
    (admitted : guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth = .ok catalogue) :
    guardedSelectOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth record reference =
      .ok (CheckedNativeFormula.select record reference catalogue) := by
  simp only [guardedSelectOnWithMetadata, admitted, Except.map]

/-- Refusal is propagated exactly, never reinterpreted as an admitted search
with no supported formula. Conversely scanning cannot create a new refusal. -/
theorem guardedSelectOnWithMetadata_error_iff (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) (reason : SearchRefusal) :
    guardedSelectOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth record reference = .error reason ↔
      guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth = .error reason := by
  cases admitted : guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth with
  | error refused =>
      simp only [guardedSelectOnWithMetadata, admitted, Except.map]
      -- The two errors have different successful-result types. Compare
      -- their refusal payloads explicitly, rather than treating the two
      -- displayed error equalities as definitionally the same proposition.
      constructor
      · intro same
        have payload : refused = reason := Except.error.inj same
        cases payload
        rfl
      · intro same
        have payload : refused = reason := Except.error.inj same
        cases payload
        rfl
  | ok catalogue =>
      simp only [guardedSelectOnWithMetadata, admitted, Except.map]
      constructor <;> intro impossible <;> cases impossible

/-- Extract the actually admitted list without unfolding its enumerator. -/
theorem guardedSelectOnWithMetadata_admission (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (result : Option (CheckedNativeFormula graph profiles))
    (selected : guardedSelectOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth record reference = .ok result) :
    ∃ catalogue, guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth = .ok catalogue ∧
      CheckedNativeFormula.select record reference catalogue = result := by
  cases admitted : guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth with
  | error reason =>
      simp only [guardedSelectOnWithMetadata, admitted, Except.map, reduceCtorEq] at selected
  | ok catalogue =>
      exact ⟨catalogue, rfl, Except.ok.inj
        (by simpa only [guardedSelectOnWithMetadata, admitted, Except.map] using selected)⟩

/-- Empty success is exact relative failure in the admitted list, not the
stronger assertion that every possible identifying formula is unavailable. -/
theorem guardedSelectOnWithMetadata_none_iff (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (catalogue : List (CheckedNativeFormula graph profiles))
    (admitted : guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth = .ok catalogue) :
    guardedSelectOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth record reference = .ok none ↔
      ∀ candidate, candidate ∈ catalogue → candidate.available record reference = false := by
  rw [guardedSelectOnWithMetadata_of_admission limits graph metadata profiles source expressionDepth proofDepth record reference catalogue admitted]
  constructor
  · intro empty
    exact (CheckedNativeFormula.select_none_iff record reference catalogue).mp (Except.ok.inj empty)
  · intro unavailable
    rw [(CheckedNativeFormula.select_none_iff record reference catalogue).mpr unavailable]

/-- The result is a member of the original complete bounded catalogue and
passes its full native guard and actual partial-expression check. -/
theorem guardedSelectOnWithMetadata_selected (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (chosen : CheckedNativeFormula graph profiles)
    (selected : guardedSelectOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth record reference = .ok (some chosen)) :
    chosen ∈ catalogueOn graph profiles source expressionDepth proofDepth ∧ chosen.available record reference = true := by
  rcases guardedSelectOnWithMetadata_admission limits graph metadata profiles source expressionDepth proofDepth
      record reference (some chosen) selected with ⟨catalogue, admitted, picked⟩
  have same := guardedCatalogueOnWithMetadata_exact limits graph metadata profiles source expressionDepth proofDepth catalogue admitted
  exact ⟨by rw [← same]; exact CheckedNativeFormula.select_mem record reference catalogue chosen picked,
    CheckedNativeFormula.select_available record reference catalogue chosen picked⟩

theorem guardedSelectOnWithMetadata_source (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (chosen : CheckedNativeFormula graph profiles)
    (selected : guardedSelectOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth record reference = .ok (some chosen)) :
    source.decode S = some chosen.source :=
  catalogueOn_source graph profiles source expressionDepth proofDepth chosen
    (guardedSelectOnWithMetadata_selected limits graph metadata profiles source expressionDepth proofDepth record reference chosen selected).1

/-- Certify the user's decoded source query, not merely whichever source a
returned record happens to contain. Null original conditioners stay outside
this theorem unless their actual source-support premise can be supplied. -/
noncomputable def guardedSelectOnWithMetadata_soundAt (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat) (query : ProbabilityTerm S)
    (decoded : source.decode S = some query) (model : FiniteHiddenDAGSCM S P)
    (graphEqual : graph = P.observedGraph)
    (covered : ∃ entry, entry ∈ profiles ∧ CausalSupportAgreement entry.model model)
    (reference : S.Assignment) (chosen : CheckedNativeFormula graph profiles)
    (selected : guardedSelectOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth
      model.observationalDist reference = .ok (some chosen))
    (sourceSupported : model.TermSupportedAt query reference) :
    model.TermEquivalentAt query chosen.formula reference := by
  have same : chosen.source = query := Option.some.inj
    ((guardedSelectOnWithMetadata_source limits graph metadata profiles source expressionDepth proofDepth
      model.observationalDist reference chosen selected).symm.trans decoded)
  rw [← same] at sourceSupported ⊢
  exact chosen.soundAt model graphEqual covered reference sourceSupported
    (guardedSelectOnWithMetadata_selected limits graph metadata profiles source expressionDepth proofDepth
      model.observationalDist reference chosen selected).2

/-- At most the admitted raw-code allowance many certificates can be visited.
This is a list-size bound, not a cost bound for an individual availability test. -/
theorem guardedCatalogueOnWithMetadata_length_bound (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (source : TermCode) (expressionDepth proofDepth : Nat)
    (catalogue : List (CheckedNativeFormula graph profiles))
    (admitted : guardedCatalogueOnWithMetadata limits graph metadata profiles source expressionDepth proofDepth = .ok catalogue) :
    catalogue.length ≤ limits.maxRawCandidates := by
  have oldAdmission := admitted
  rw [guardedCatalogueOnWithMetadata_eq] at oldAdmission
  rcases guardedCatalogueOn_admission limits graph profiles source expressionDepth proofDepth catalogue oldAdmission with
    ⟨syntaxEstimate, syntaxChecked, _sourceFits, _profile, _profileChecked, _total, _totalChecked⟩
  have bounds := preflightSyntax_bounds limits S expressionDepth proofDepth syntaxEstimate syntaxChecked
  have rawBound : (enumerate S expressionDepth proofDepth).length ≤ limits.maxRawCandidates := by
    simpa only [bounds.1, count_eq_length] using bounds.2.2.2.1
  rw [guardedCatalogueOnWithMetadata_exact limits graph metadata profiles source expressionDepth proofDepth catalogue admitted]
  exact Nat.le_trans (List.length_filterMap_le _ _) rawBound

/-- Any accepted supplied guard for a bounded proof forces successful
selection on a covered original model, provided this search was admitted.
It need not select that same syntax: every selected member is sound. -/
theorem guardedSelectOnWithMetadata_covers (limits : SearchLimits) (graph : ObservedGraph S)
    (metadata : DomainSizeMetadata S) (profiles : List (NativeTemplateInstance Q))
    (expressionDepth proofDepth : Nat) (code : NativeCertificateCode)
    (bounded : code.proof.Within S expressionDepth proofDepth)
    (checked : CheckedNativeFormula graph profiles) (accepted : code.checkOn graph profiles = some checked)
    (catalogue : List (CheckedNativeFormula graph profiles))
    (admitted : guardedCatalogueOnWithMetadata limits graph metadata profiles code.source expressionDepth proofDepth = .ok catalogue)
    (model : FiniteHiddenDAGSCM S P)
    (covered : ∃ entry, entry ∈ profiles ∧ CausalSupportAgreement entry.model model)
    (reference : S.Assignment) (available : checked.available model.observationalDist reference = true) :
    ∃ chosen, guardedSelectOnWithMetadata limits graph metadata profiles code.source expressionDepth proofDepth
      model.observationalDist reference = .ok (some chosen) ∧
      chosen.available model.observationalDist reference = true := by
  have coverage := catalogueOn_covers graph profiles expressionDepth proofDepth code bounded checked accepted
    model covered reference available
  have same := guardedCatalogueOnWithMetadata_exact limits graph metadata profiles code.source expressionDepth proofDepth catalogue admitted
  rw [← same] at coverage
  rcases CheckedNativeFormula.select_complete model.observationalDist reference catalogue coverage with ⟨chosen, picked⟩
  refine ⟨chosen, ?_, CheckedNativeFormula.select_available model.observationalDist reference catalogue chosen picked⟩
  rw [guardedSelectOnWithMetadata_of_admission limits graph metadata profiles code.source expressionDepth proofDepth
    model.observationalDist reference catalogue admitted, picked]

end NativeProofCode
end ProbabilityCode
end Thesis.Causality
