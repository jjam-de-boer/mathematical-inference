import Thesis.CausalTransport.BinaryInstrumental.EffectBounds
import Thesis.Examples.BinaryInstrumental.Compatibility

namespace Thesis
namespace Causality
namespace Examples
namespace BinaryInstrumentalEffectBounds

open Probability BinaryInstrumental

/-!
# Native sharp-risk and signed-effect regressions

For uniform observed data, the computed affine effect scores are one quarter
and three quarters: the corresponding *signed* ATE endpoints are minus and
plus one half.  All four risk corners have genuine whole-law native witnesses,
and the score bounds range over every such model, not merely the constructors.

The two full-compliance laws retain zeros in six of the eight observed cells.
One has outcome equal to treatment; the other has its negation.  The bounds
collapse respectively to affine score one and zero, encoding ATE plus one
and minus one.  In particular, the negative-effect check would fail if a
nonnegative rational subtraction silently truncated the target to zero.

No monotonicity field is assumed in any theorem.  These particular laws
are simple regression inputs, not a restriction of the optimizer's class.
-/

abbrev projection := BinaryInstrumentalCompatibility.projection
abbrev uniformLaw := BinaryInstrumentalCompatibility.uniformLaw
theorem projected_iv_graph : HasIVProjection projection := BinaryInstrumentalCompatibility.projected_iv_graph

theorem uniform_effect_endpoints :
    QProb.Equiv
        (effectLower (observedTotal uniformLaw)
          (observedTotal_positive uniformLaw BinaryInstrumentalCompatibility.uniform_false_positive
            BinaryInstrumentalCompatibility.uniform_true_positive)
          (observedRows uniformLaw) (observedColumns uniformLaw)) BinaryInstrumentalTransportation.quarter ∧
      QProb.Equiv
        (effectUpper (observedTotal uniformLaw)
          (observedTotal_positive uniformLaw BinaryInstrumentalCompatibility.uniform_false_positive
            BinaryInstrumentalCompatibility.uniform_true_positive)
          (observedRows uniformLaw) (observedColumns uniformLaw)) BinaryInstrumentalTransportation.threeQuarters := by
  decide +kernel

theorem uniform_native_effect_bounds (native : FiniteHiddenDAGSCM signature projection)
    (observed : HasObservedLaw native uniformLaw) :
    QProb.LE BinaryInstrumentalTransportation.quarter (nativeEffectScore native) ∧
      QProb.LE (nativeEffectScore native) BinaryInstrumentalTransportation.threeQuarters := by
  have bounded := native_observed_effect_bounds native projected_iv_graph uniformLaw observed
    BinaryInstrumentalCompatibility.uniform_false_positive BinaryInstrumentalCompatibility.uniform_true_positive
  exact ⟨QProb.le_congr uniform_effect_endpoints.1 (QProb.equiv_refl _) bounded.1,
    QProb.le_congr (QProb.equiv_refl _) uniform_effect_endpoints.2 bounded.2⟩

theorem uniform_all_risk_corners (controlUpper treatedUpper : Bool) :
    RisksAttainableAt projection uniformLaw
      (selectedRisk (observedTotal uniformLaw)
        (observedTotal_positive uniformLaw BinaryInstrumentalCompatibility.uniform_false_positive
          BinaryInstrumentalCompatibility.uniform_true_positive)
        (observedRows uniformLaw) (observedColumns uniformLaw) controlUpper treatedUpper) :=
  native_observed_risk_endpoints_attainable projection projected_iv_graph uniformLaw
    BinaryInstrumentalCompatibility.uniform_false_positive BinaryInstrumentalCompatibility.uniform_true_positive
    BinaryInstrumentalCompatibility.uniform_capacities controlUpper treatedUpper

theorem uniform_native_effect_endpoints :
    EffectScoreAttainableAt projection uniformLaw BinaryInstrumentalTransportation.quarter ∧
      EffectScoreAttainableAt projection uniformLaw BinaryInstrumentalTransportation.threeQuarters := by
  have attained := native_observed_effect_endpoints_attainable projection projected_iv_graph uniformLaw
    BinaryInstrumentalCompatibility.uniform_false_positive BinaryInstrumentalCompatibility.uniform_true_positive
    BinaryInstrumentalCompatibility.uniform_capacities
  rcases attained.1 with ⟨lower, lowerLaw, lowerScore⟩
  rcases attained.2 with ⟨upper, upperLaw, upperScore⟩
  exact ⟨⟨lower, lowerLaw, QProb.equiv_trans lowerScore uniform_effect_endpoints.1⟩,
    ⟨upper, upperLaw, QProb.equiv_trans upperScore uniform_effect_endpoints.2⟩⟩

def fullComplianceLaw (negative : Bool) : FiniteProbRecord signature.Assignment :=
  ⟨[(BinaryInstrumentalCompatibility.assignment false false negative, 1),
    (BinaryInstrumentalCompatibility.assignment true true (!negative), 1)], 2, by decide, rfl⟩

theorem fullCompliance_false_positive (negative : Bool) :
    0 < instrumentMass (fullComplianceLaw negative) false := by cases negative <;> decide +kernel
theorem fullCompliance_true_positive (negative : Bool) :
    0 < instrumentMass (fullComplianceLaw negative) true := by cases negative <;> decide +kernel
theorem fullCompliance_capacities (negative : Bool) : forall label,
    observedRows (fullComplianceLaw negative) label + observedColumns (fullComplianceLaw negative) label ≤
      observedTotal (fullComplianceLaw negative) := by cases negative <;> decide +kernel

/-- Score zero is the negative signed effect minus one, not an ATE of zero.
Score one is the positive signed effect plus one. -/
theorem fullCompliance_effect_endpoints (negative : Bool) :
    QProb.Equiv
        (effectLower (observedTotal (fullComplianceLaw negative))
          (observedTotal_positive (fullComplianceLaw negative)
            (fullCompliance_false_positive negative) (fullCompliance_true_positive negative))
          (observedRows (fullComplianceLaw negative)) (observedColumns (fullComplianceLaw negative)))
        (if negative then QProb.zero else QProb.one) ∧
      QProb.Equiv
        (effectUpper (observedTotal (fullComplianceLaw negative))
          (observedTotal_positive (fullComplianceLaw negative)
            (fullCompliance_false_positive negative) (fullCompliance_true_positive negative))
          (observedRows (fullComplianceLaw negative)) (observedColumns (fullComplianceLaw negative)))
        (if negative then QProb.zero else QProb.one) := by
  cases negative <;> decide +kernel

theorem fullCompliance_native_effect_exists (negative : Bool) :
    EffectScoreAttainableAt projection (fullComplianceLaw negative)
      (if negative then QProb.zero else QProb.one) := by
  have attained := (native_observed_effect_endpoints_attainable projection projected_iv_graph
    (fullComplianceLaw negative) (fullCompliance_false_positive negative) (fullCompliance_true_positive negative)
    (fullCompliance_capacities negative)).1
  rcases attained with ⟨native, observed, same⟩
  exact ⟨native, observed, QProb.equiv_trans same (fullCompliance_effect_endpoints negative).1⟩

end BinaryInstrumentalEffectBounds
end Examples
end Causality
end Thesis
