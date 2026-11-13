import Thesis.CausalTransport.NativeDemandTypes

namespace Thesis.Causality

open Probability NativeDemandTyping

/-!
# A query demand independent of its candidate formula

Fix the source query, one complete observed support pattern and one declared
reference. The mask below retains exactly that reference in every matching
causal profile where the source has a value. It never inspects a printed
formula, a derivation, a guard, or numerical observational weights.

Source support is deliberately part of the mask. An undefined causal
conditioner contributes no demanded cell and acquires no probability value.
The coverage lemma therefore still requires an original source-support
witness. Observational availability of a later candidate is a separate test,
also when this mask is empty. Hypothetical or malformed support-bit lists
cannot certify an original application merely by matching no profile.

The small pattern lemmas expose why reweighting an observed law does not
change guard acceptance. Equality here concerns every declared support bit;
it does not identify numerical laws or supply a causal equation.
-/

variable {S : ObservedSignature.{0}} {P Q : FiniteLatentProjection S}

namespace NativeSupportGuard

theorem support_eq_of_pattern_eq {left right : FiniteProbRecord S.Assignment}
    (same : pattern S left = pattern S right) : left.support = right.support := by
  have atEvery := List.map_inj_left.mp same
  funext reference
  exact atEvery reference (S.assignmentEnumeration_complete reference)

theorem accepts_eq_of_pattern_eq (code : Code) {left right : FiniteProbRecord S.Assignment}
    (same : pattern S left = pattern S right) (reference : S.Assignment) :
    accepts code left reference = accepts code right reference := by
  simp only [accepts, Cell.accepts, same]

end NativeSupportGuard

namespace NativeQueryDemand

/-- All matching profiles are retained at the fixed reference when their
own source query is defined. No favorable representative is selected. -/
def mask (profiles : List (NativeTemplateInstance P)) (source : ProbabilityTerm S)
    (observed : List Bool) (fixed : S.Assignment) : Demand profiles :=
  fun index reference =>
    (decide (NativeSupportGuard.pattern S (profiles.get index).model.observationalDist = observed) &&
      decide (reference = fixed)) && ((profiles.get index).model.termDenote source reference).isSome

theorem mask_exact (profiles : List (NativeTemplateInstance P)) (source : ProbabilityTerm S)
    (observed : List Bool) (fixed : S.Assignment) (index : Fin profiles.length) (reference : S.Assignment) :
    mask profiles source observed fixed index reference = true ↔
      NativeSupportGuard.pattern S (profiles.get index).model.observationalDist = observed ∧
      reference = fixed ∧ ((profiles.get index).model.termDenote source reference).isSome = true := by
  simp only [mask, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc]

/-- This checks the source only where its actual definedness selected it.
It is not a theorem that the source is defined at the omitted references. -/
theorem source_checked (profiles : List (NativeTemplateInstance P)) (source : ProbabilityTerm S)
    (observed : List Bool) (fixed : S.Assignment) :
    check profiles source (mask profiles source observed fixed) = true := by
  rw [check_exact]
  apply (allNeeded_exact ..).mpr
  intro index reference needed
  exact ((mask_exact ..).mp needed).2.2

theorem mask_eq_of_support_eq (profiles : List (NativeTemplateInstance P)) (source : ProbabilityTerm S)
    {left right : FiniteProbRecord S.Assignment} (same : left.support = right.support) (fixed : S.Assignment) :
    mask profiles source (NativeSupportGuard.pattern S left) fixed =
      mask profiles source (NativeSupportGuard.pattern S right) fixed := by
  simp only [NativeSupportGuard.pattern, same]

/-- A supplied support-agreeing profile retains every genuinely supported
application of the original model. The witness is an input, not recovered
by choosing a profile from a mere existential coverage statement. -/
theorem at_covered (profiles : List (NativeTemplateInstance P)) (source : ProbabilityTerm S)
    (model : FiniteHiddenDAGSCM S Q) (index : Fin profiles.length)
    (same : CausalSupportAgreement (profiles.get index).model model) (fixed : S.Assignment)
    (sourceSupported : model.TermSupportedAt source fixed) :
    mask profiles source (NativeSupportGuard.pattern S model.observationalDist) fixed index fixed = true := by
  apply (mask_exact ..).mpr
  refine ⟨congrArg (fun support => S.assignmentEnumeration.map support) same.observational_support, rfl, ?_⟩
  rw [← ProbabilityResult.status_isDefined, same.term_status source fixed, ProbabilityResult.status_isDefined]
  exact ProbabilityResult.supported_isSome sourceSupported

end NativeQueryDemand
end Thesis.Causality
