import Thesis.CausalTransport.BinaryInstrumentalComputedBounds

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Complete fixed-law point identification for binary IV

Graph-level ID failure is not a fixed-distribution answer: particular laws
can still determine a treatment risk or the average treatment effect.  Here
identification quantifies over *every* native model on the specified original
hidden DAG that has the supplied whole observed law.  The sharp universal
bounds and actual endpoint models give an exact classification: identification
holds precisely when the corresponding computed endpoints coincide.

Compatibility is an explicit premise of both equivalences.  Without it the
model class may be empty and universal agreement would hold vacuously.  The
executable tests below are therefore advertised only for compatible laws.
Either instrument arm may be null, individual cells may be zero, and hidden
and private-noise domains retain arbitrary finite sizes.  No monotonicity or
positivity premise is added.

Effect identification is stated using `nativeEffectScore`, the injective
affine encoding `(ATE + 1) / 2` of the signed ATE, not a truncated subtraction
of two probability numerators.  Equality of this encoding is equality of the
signed target.  This module does not yet assert interval-interior attainment.
-/

def RiskIdentifiedAt (projection : FiniteLatentProjection signature)
    (law : FiniteProbRecord signature.Assignment) (action : Bool) : Prop :=
  forall left right : FiniteHiddenDAGSCM signature projection,
    HasObservedLaw left law → HasObservedLaw right law →
      QProb.Equiv (left.interventionalValue (intervention action) (fun sample => sample y))
        (right.interventionalValue (intervention action) (fun sample => sample y))

def EffectIdentifiedAt (projection : FiniteLatentProjection signature)
    (law : FiniteProbRecord signature.Assignment) : Prop :=
  forall left right : FiniteHiddenDAGSCM signature projection,
    HasObservedLaw left law → HasObservedLaw right law →
      QProb.Equiv (nativeEffectScore left) (nativeEffectScore right)

/-- Both lower risks occur together, as do both upper risks.  These are
actual original-DAG models, not independent numerical extrema. -/
theorem computedBounds_risk_endpoints (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (checked : (computedBounds law).compatible = true) :
    RisksAttainableAt projection law (computedBounds law).lowerRisk ∧
      RisksAttainableAt projection law (computedBounds law).upperRisk := by
  have lower := computedBounds_risk_corners projection graphMatch law checked false false
  have upper := computedBounds_risk_corners projection graphMatch law checked true true
  have lowerSelected : computedSelectedRisk law false false = (computedBounds law).lowerRisk := by
    funext action
    cases action <;> rfl
  have upperSelected : computedSelectedRisk law true true = (computedBounds law).upperRisk := by
    funext action
    cases action <;> rfl
  exact ⟨lowerSelected ▸ lower, upperSelected ▸ upper⟩

/-- Every model in a collapsed interval has its unique represented value.
Only rational-order antisymmetry is needed, not a decision of a proposition
about arbitrary models. -/
private theorem equiv_lower_of_collapsed {lower upper value : QProb}
    (same : QProb.Equiv lower upper)
    (bounds : QProb.LE lower value ∧ QProb.LE value upper) :
    QProb.Equiv value lower :=
  QProb.equiv_of_le_of_le
    (QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_symm same) bounds.2) bounds.1

/-- Complete classification of either treatment-specific risk at a fixed
compatible law.  Necessity uses two actual endpoint models; sufficiency
uses universal containment for every native model, not just that pair. -/
theorem riskIdentifiedAt_iff_bounds_equiv (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (checked : (computedBounds law).compatible = true) (action : Bool) :
    RiskIdentifiedAt projection law action ↔
      QProb.Equiv ((computedBounds law).lowerRisk action) ((computedBounds law).upperRisk action) := by
  constructor
  · intro identified
    obtain ⟨lower, lowerLaw, lowerValue⟩ := (computedBounds_risk_endpoints projection graphMatch law checked).1
    obtain ⟨upper, upperLaw, upperValue⟩ := (computedBounds_risk_endpoints projection graphMatch law checked).2
    exact QProb.equiv_trans (QProb.equiv_symm (lowerValue action))
      (QProb.equiv_trans (identified lower upper lowerLaw upperLaw) (upperValue action))
  · intro same left right leftLaw rightLaw
    exact QProb.equiv_trans
      (equiv_lower_of_collapsed same (computedBounds_native_risks left graphMatch law leftLaw action))
      (QProb.equiv_symm
        (equiv_lower_of_collapsed same (computedBounds_native_risks right graphMatch law rightLaw action)))

/-- The same complete criterion for the signed ATE, via its injective
affine score.  Both endpoint values already have whole-law native witnesses. -/
theorem effectIdentifiedAt_iff_bounds_equiv (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (checked : (computedBounds law).compatible = true) :
    EffectIdentifiedAt projection law ↔
      QProb.Equiv (computedBounds law).lowerEffect (computedBounds law).upperEffect := by
  constructor
  · intro identified
    obtain ⟨lower, lowerLaw, lowerValue⟩ := (computedBounds_effect_endpoints projection graphMatch law checked).1
    obtain ⟨upper, upperLaw, upperValue⟩ := (computedBounds_effect_endpoints projection graphMatch law checked).2
    exact QProb.equiv_trans (QProb.equiv_symm lowerValue)
      (QProb.equiv_trans (identified lower upper lowerLaw upperLaw) upperValue)
  · intro same left right leftLaw rightLaw
    exact QProb.equiv_trans
      (equiv_lower_of_collapsed same (computedBounds_native_effect left graphMatch law leftLaw))
      (QProb.equiv_symm (equiv_lower_of_collapsed same (computedBounds_native_effect right graphMatch law rightLaw)))

/-- These tests compare exact rational values, not their presentations.
Callers must check compatibility before interpreting a result as identification. -/
def riskIdentificationCheck (law : FiniteProbRecord signature.Assignment) (action : Bool) : Bool :=
  decide (QProb.Equiv ((computedBounds law).lowerRisk action) ((computedBounds law).upperRisk action))

def effectIdentificationCheck (law : FiniteProbRecord signature.Assignment) : Bool :=
  decide (QProb.Equiv (computedBounds law).lowerEffect (computedBounds law).upperEffect)

theorem riskIdentificationCheck_iff (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (checked : (computedBounds law).compatible = true) (action : Bool) :
    riskIdentificationCheck law action = true ↔ RiskIdentifiedAt projection law action := by
  exact (decide_eq_true_iff _).trans
    (riskIdentifiedAt_iff_bounds_equiv projection graphMatch law checked action).symm

theorem effectIdentificationCheck_iff (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (checked : (computedBounds law).compatible = true) :
    effectIdentificationCheck law = true ↔ EffectIdentifiedAt projection law := by
  exact (decide_eq_true_iff _).trans
    (effectIdentifiedAt_iff_bounds_equiv projection graphMatch law checked).symm

end BinaryInstrumental
end Causality
end Thesis
