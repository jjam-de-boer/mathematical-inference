import Thesis.CausalTransport.BinaryInstrumental.RiskBounds
import Thesis.CausalTransport.BinaryInstrumental.Effect
import Thesis.Examples.BinaryInstrumental.Compatibility

namespace Thesis
namespace Causality
namespace Examples
namespace BinaryInstrumentalRiskBounds

open Probability BinaryInstrumental

/-!
# Universal native risk bounds agree with the constructed endpoint witnesses

Uniform observed data yield the interval `[1/4,3/4]` for both actions.
The first theorem ranges over *every* native model with that entire law;
hidden alphabets and response denominators remain unrestricted.  The next
two theorems reuse actual original-DAG witnesses with opposing risk pairs.
Thus the numerical endpoint checks cannot substitute for universal validity.

This regression is deliberately about unconditional treatment risks.  The
native effect-score witnesses are retained separately, and it does not assert
that the final arbitrary-law sharp-effect package or null-instrument branch
has already been assembled.
-/

abbrev projection := BinaryInstrumentalCompatibility.projection
abbrev uniformLaw := BinaryInstrumentalCompatibility.uniformLaw
theorem projected_iv_graph : HasIVProjection projection := BinaryInstrumentalCompatibility.projected_iv_graph

theorem uniform_risk_endpoints (action : Bool) :
    QProb.Equiv
      (riskLower (observedTotal uniformLaw)
        (observedTotal_positive uniformLaw BinaryInstrumentalCompatibility.uniform_false_positive BinaryInstrumentalCompatibility.uniform_true_positive)
        (observedRows uniformLaw) (observedColumns uniformLaw) action) BinaryInstrumentalTransportation.quarter ∧
      QProb.Equiv
        (riskUpper (observedTotal uniformLaw)
          (observedTotal_positive uniformLaw BinaryInstrumentalCompatibility.uniform_false_positive BinaryInstrumentalCompatibility.uniform_true_positive)
          (observedRows uniformLaw) (observedColumns uniformLaw) action) BinaryInstrumentalTransportation.threeQuarters := by
  cases action <;> decide +kernel

/-- The displayed interval bounds every compatible original-DAG model,
including ones whose rational weights are not on the observed grid. -/
theorem uniform_native_bounds (native : FiniteHiddenDAGSCM signature projection)
    (observed : HasObservedLaw native uniformLaw) (action : Bool) :
    QProb.LE BinaryInstrumentalTransportation.quarter
        (native.interventionalValue (intervention action) (fun sample => sample y)) ∧
      QProb.LE (native.interventionalValue (intervention action) (fun sample => sample y))
        BinaryInstrumentalTransportation.threeQuarters := by
  have bounded := native_observed_risk_bounds native projected_iv_graph uniformLaw observed
    BinaryInstrumentalCompatibility.uniform_false_positive BinaryInstrumentalCompatibility.uniform_true_positive action
  exact ⟨QProb.le_congr (uniform_risk_endpoints action).1 (QProb.equiv_refl _) bounded.1,
    QProb.le_congr (QProb.equiv_refl _) (uniform_risk_endpoints action).2 bounded.2⟩

theorem uniform_lower_effect_risks_attained :
    RisksAttainableAt projection uniformLaw BinaryInstrumentalTransportation.lowerRisks :=
  BinaryInstrumentalTransportation.lower_native_risks

theorem uniform_upper_effect_risks_attained :
    RisksAttainableAt projection uniformLaw BinaryInstrumentalTransportation.upperRisks :=
  BinaryInstrumentalTransportation.upper_native_risks

end BinaryInstrumentalRiskBounds
end Examples
end Causality
end Thesis
