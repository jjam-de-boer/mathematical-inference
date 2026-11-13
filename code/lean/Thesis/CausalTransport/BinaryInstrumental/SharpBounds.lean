import Thesis.CausalTransport.BinaryInstrumental.EffectBounds

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Computed sharp IV certificates for risks and average treatment effect

This application-facing module assembles universal containment and actual
endpoint attainment.  The eight observed joint cells determine the normalized
margins; four capacity checks certify compatibility.  That checked data
constructs all four risk corners and both signed-effect extrema on the
original hidden DAG.  Incompatible laws are not assigned vacuous sharp bounds.

The quantified containment direction still ranges over every finite native
SCM with the entire supplied observed law, not just these constructors or a
fixed rational grid.  The effect endpoints use `(ATE + 1) / 2`; the previous
module also supplies literal signed integer cross-product bounds.

These certificates require both instrument values to have positive mass and
allow every other observed cell to be zero. `BinaryInstrumental.NullBounds`
constructs the missing-arm consistency bounds, retaining its free response
margin. `BinaryInstrumental.ComputedBounds` combines both cases into the
whole-domain interface.
-/

/-- Every attained risk pair is contained, and every lower/upper corner
is attained by one native model preserving the full law. -/
theorem native_observed_sharp_risk_bounds (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true)
    (capacities : forall label, observedRows law label + observedColumns law label ≤ observedTotal law) :
    (forall risks, RisksAttainableAt projection law risks → forall action,
      QProb.LE (riskLower (observedTotal law) (observedTotal_positive law falsePositive truePositive)
          (observedRows law) (observedColumns law) action) (risks action) ∧
        QProb.LE (risks action)
          (riskUpper (observedTotal law) (observedTotal_positive law falsePositive truePositive)
            (observedRows law) (observedColumns law) action)) ∧
      (forall controlUpper treatedUpper, RisksAttainableAt projection law
        (selectedRisk (observedTotal law) (observedTotal_positive law falsePositive truePositive)
          (observedRows law) (observedColumns law) controlUpper treatedUpper)) := by
  constructor
  · rintro risks ⟨native, observed, attained⟩ action
    have bounded := native_observed_risk_bounds native graphMatch law observed falsePositive truePositive action
    exact ⟨QProb.le_congr (QProb.equiv_refl _) (attained action) bounded.1,
      QProb.le_congr (attained action) (QProb.equiv_refl _) bounded.2⟩
  · exact native_observed_risk_endpoints_attainable projection graphMatch law falsePositive truePositive capacities

/-- Universal effect containment and two genuine native extrema.  All
displayed margins come from the observed record, not an external optimizer
certificate; the finite capacity inequalities are the complete compatibility
test already proved for this positive-instrument branch. -/
theorem native_observed_sharp_effect_bounds (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true)
    (capacities : forall label, observedRows law label + observedColumns law label ≤ observedTotal law) :
    (forall score, EffectScoreAttainableAt projection law score →
      QProb.LE (effectLower (observedTotal law) (observedTotal_positive law falsePositive truePositive)
          (observedRows law) (observedColumns law)) score ∧
        QProb.LE score (effectUpper (observedTotal law) (observedTotal_positive law falsePositive truePositive)
          (observedRows law) (observedColumns law))) ∧
      EffectScoreAttainableAt projection law
        (effectLower (observedTotal law) (observedTotal_positive law falsePositive truePositive)
          (observedRows law) (observedColumns law)) ∧
        EffectScoreAttainableAt projection law
          (effectUpper (observedTotal law) (observedTotal_positive law falsePositive truePositive)
            (observedRows law) (observedColumns law)) := by
  constructor
  · rintro score ⟨native, observed, attained⟩
    have bounded := native_observed_effect_bounds native graphMatch law observed falsePositive truePositive
    exact ⟨QProb.le_congr (QProb.equiv_refl _) attained bounded.1,
      QProb.le_congr attained (QProb.equiv_refl _) bounded.2⟩
  · exact native_observed_effect_endpoints_attainable projection graphMatch law falsePositive truePositive capacities

end BinaryInstrumental
end Causality
end Thesis
