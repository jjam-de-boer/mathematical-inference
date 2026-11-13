import Thesis.CausalTransport.NativeSupportSemantics

namespace Thesis.Causality

open Probability

/-!
# Exact executable checks for complete native derivation support

Checking only a derivation's printed endpoints is insufficient: intermediate
conditioners and every finite marginal substitution must also be supported.
This checker mirrors the established support tree, including its asymmetric
weighted branch. A zero *defined* weight skips the factor; an undefined weight
does not become zero. A positive weight demands the complete factor subtree.

Acceptance reconstructs support data from the model's actual evaluated
options. Conversely every existing support tree passes. Support-equivalent
native models therefore give the same answer, even when their numerical
probabilities, hidden graphs or source denominators differ. This is the link
needed to check support using the finite causal profile catalogue.

Only proof-data reconstruction is marked noncomputable, for Lean's indexed
recursor compilation restriction. The Boolean checker is computable, and no
choice, general excluded middle or new semantic assumption is introduced.
-/

variable {S : ObservedSignature.{0}} {P Q : FiniteLatentProjection S}

namespace HiddenDAGLocalDerivationSupport

def check {G : ObservedGraph S} (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right) : Bool :=
  ((model.termDenote left reference).isSome && (model.termDenote right reference).isSome) &&
    match derivation with
    | .refl _ => true
    | .symm inner => check model reference inner
    | .trans first second => check model reference first && check model reference second
    | .doRule _ => true
    | .marginalization _ _ _ _ _ => true
    | .conditioning _ _ _ _ _ => true
    | .chain _ _ _ _ _ => true
    | .weightedChain _ _ _ _ _ => true
    | .multiplyComm _ _ => true
    | .multiplyAssoc _ _ _ => true
    | .marginalizeCongr nodes inner =>
        (ProbabilityTerm.marginalAssignments S nodes reference).all (fun variant => check model variant inner)
    | .evaluateAtCongr fixed inner => check model fixed inner
    | .addCongr first second => check model reference first && check model reference second
    | .multiplyCongr first second => check model reference first && check model reference second
    | @DoCalculusDerivation.weightedMultiplyCongr _ _ _ weight _ _ _ first second =>
        check model reference first &&
          (if ProbabilityResult.status (model.termDenote weight reference) = .positive then check model reference second else true)
    | .divideCongr numerator denominator => check model reference numerator && check model reference denominator
    | .eqCongr _ _ inner => check model reference inner

private noncomputable def endpointsOfCheck {G : ObservedGraph S} (model : FiniteHiddenDAGSCM S P)
    (reference : S.Assignment) {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation G left right) (accepted : check model reference derivation = true) :
    model.TermSupportedAt left reference × model.TermSupportedAt right reference := by
  cases derivation <;>
    exact ⟨ProbabilityResult.supportedOfIsSome _ (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1).1,
      ProbabilityResult.supportedOfIsSome _ (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1).2⟩

/-- Rebuild all witnesses, including the actual values at each branch. No
value is extracted from a propositional existential or copied from a profile. -/
noncomputable def ofCheck {G : ObservedGraph S} (model : FiniteHiddenDAGSCM S P)
    (reference : S.Assignment) {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation G left right) (accepted : check model reference derivation = true) :
    HiddenDAGLocalDerivationSupport model reference derivation := by
  induction derivation generalizing reference
  all_goals
    have endpoints := endpointsOfCheck model reference _ accepted
    refine ⟨endpoints.1, endpoints.2, ?_⟩
  case refl => exact ()
  case symm inner ih => exact ih reference (Bool.and_eq_true_iff.mp accepted).2
  case trans first second firstIH secondIH =>
    have both := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).2
    exact ⟨firstIH reference both.1, secondIH reference both.2⟩
  case doRule => exact ()
  case marginalization => exact ()
  case conditioning => exact ()
  case chain => exact ()
  case weightedChain => exact ()
  case multiplyComm => exact ()
  case multiplyAssoc => exact ()
  case marginalizeCongr nodes inner ih =>
    intro variant member
    exact ih variant ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp accepted).2) variant member)
  case evaluateAtCongr fixed left right inner ih => exact ih fixed (Bool.and_eq_true_iff.mp accepted).2
  case addCongr first second firstIH secondIH =>
    have both := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).2
    exact ⟨firstIH reference both.1, secondIH reference both.2⟩
  case multiplyCongr first second firstIH secondIH =>
    have both := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).2
    exact ⟨firstIH reference both.1, secondIH reference both.2⟩
  case weightedMultiplyCongr weight weight' factor factor' first second firstIH secondIH =>
    have both := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).2
    refine ⟨firstIH reference both.1, ?_⟩
    intro positive
    have status := ProbabilityResult.positiveSupported_status positive
    exact secondIH reference (by simpa only [status, if_pos rfl] using both.2)
  case divideCongr numerator denominator numeratorIH denominatorIH =>
    have both := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).2
    exact ⟨numeratorIH reference both.1, denominatorIH reference both.2⟩
  case eqCongr _ _ inner ih => exact ih reference (Bool.and_eq_true_iff.mp accepted).2

theorem check_of_supported {G : ObservedGraph S} (model : FiniteHiddenDAGSCM S P)
    (reference : S.Assignment) {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation G left right)
    (supported : HiddenDAGLocalDerivationSupport model reference derivation) :
    check model reference derivation = true := by
  induction derivation generalizing reference
  all_goals
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨ProbabilityResult.supported_isSome supported.1,
      ProbabilityResult.supported_isSome supported.2.1⟩, ?_⟩
  case refl => rfl
  case symm inner ih => exact ih reference supported.2.2
  case trans first second firstIH secondIH =>
    exact Bool.and_eq_true_iff.mpr ⟨firstIH reference supported.2.2.1, secondIH reference supported.2.2.2⟩
  case doRule => rfl
  case marginalization => rfl
  case conditioning => rfl
  case chain => rfl
  case weightedChain => rfl
  case multiplyComm => rfl
  case multiplyAssoc => rfl
  case marginalizeCongr nodes inner ih =>
    exact List.all_eq_true.mpr (fun variant member => ih variant (supported.2.2 variant member))
  case evaluateAtCongr fixed left right inner ih => exact ih fixed supported.2.2
  case addCongr first second firstIH secondIH =>
    exact Bool.and_eq_true_iff.mpr ⟨firstIH reference supported.2.2.1, secondIH reference supported.2.2.2⟩
  case multiplyCongr first second firstIH secondIH =>
    exact Bool.and_eq_true_iff.mpr ⟨firstIH reference supported.2.2.1, secondIH reference supported.2.2.2⟩
  case weightedMultiplyCongr weight weight' factor factor' first second firstIH secondIH =>
    apply Bool.and_eq_true_iff.mpr
    refine ⟨firstIH reference supported.2.2.1, ?_⟩
    split
    next positive =>
      exact secondIH reference (supported.2.2.2 (ProbabilityResult.positiveSupportedOfStatus _ positive))
    next => rfl
  case divideCongr numerator denominator numeratorIH denominatorIH =>
    exact Bool.and_eq_true_iff.mpr ⟨numeratorIH reference supported.2.2.1, denominatorIH reference supported.2.2.2⟩
  case eqCongr _ _ inner ih => exact ih reference supported.2.2

theorem check_exact {G : ObservedGraph S} (model : FiniteHiddenDAGSCM S P)
    (reference : S.Assignment) {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right) :
    check model reference derivation = true ↔ Nonempty (HiddenDAGLocalDerivationSupport model reference derivation) :=
  ⟨fun accepted => ⟨ofCheck model reference derivation accepted⟩,
    fun ⟨supported⟩ => check_of_supported model reference derivation supported⟩

/-- The whole check, not merely printed definedness, is invariant under
the support agreement supplied by the finite profile representation. -/
theorem check_eq_of_agreement {G : ObservedGraph S} {leftModel : FiniteHiddenDAGSCM S P}
    {rightModel : FiniteHiddenDAGSCM S Q} (same : CausalSupportAgreement leftModel rightModel)
    (reference : S.Assignment) {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right) :
    check leftModel reference derivation = check rightModel reference derivation := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    exact check_of_supported rightModel reference derivation
      (same.localSupportToRight derivation reference (ofCheck leftModel reference derivation accepted))
  · intro accepted
    exact check_of_supported leftModel reference derivation
      (same.symm.localSupportToRight derivation reference (ofCheck rightModel reference derivation accepted))

end HiddenDAGLocalDerivationSupport
end Thesis.Causality
