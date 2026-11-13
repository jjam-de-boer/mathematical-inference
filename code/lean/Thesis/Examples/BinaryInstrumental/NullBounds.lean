import Thesis.CausalTransport.BinaryInstrumental.ComputedBounds
import Thesis.Examples.BinaryInstrumental.Compatibility

namespace Thesis
namespace Causality
namespace Examples
namespace BinaryInstrumentalNullBounds

open Probability BinaryInstrumental

/-!
# Whole-law null-instrument risk and signed-effect regressions

Each fixture has only the selected instrument value, while treatment takes
both values fairly.  With outcome equal to treatment the ATE interval is
`[0,1]`, encoded by `[1/2,1]`; with its negation it is `[-1,0]`, encoded by
`[0,1/2]`.  Both possible missing instrument values are checked.

An explicitly listed off-support atom has zero weight.  It must not be
mistaken for a positive-probability observation, removed to justify the
theorem, or assigned a conditional at its instrument value.  All risk
corners and effect endpoints have actual original-DAG native witnesses, and
universal bounds cover every native model with the supplied whole law.

The final two checks exercise the computed API on positive-arm uniform data
and on incompatible exclusion-violating observations.  Thus the unified
compatibility flag is tested on all three branches, not just null fixtures.
-/

abbrev projection := BinaryInstrumentalCompatibility.projection
theorem projected_iv_graph : HasIVProjection projection := BinaryInstrumentalCompatibility.projected_iv_graph
def half : QProb := ⟨1, 2, by decide⟩

def nullLaw (active negative : Bool) : FiniteProbRecord signature.Assignment :=
  ⟨[(BinaryInstrumentalCompatibility.assignment active false negative, 1),
    (BinaryInstrumentalCompatibility.assignment active true (!negative), 1),
    (BinaryInstrumentalCompatibility.assignment (!active) false true, 0)], 2, by decide, rfl⟩

theorem nullLaw_missing (active negative : Bool) : instrumentMass (nullLaw active negative) (!active) = 0 := by
  cases active <;> cases negative <;> decide +kernel

theorem nullLaw_compatible (active negative : Bool) : (computedBounds (nullLaw active negative)).compatible = true := by
  cases active <;> cases negative <;> decide +kernel

theorem nullLaw_effect_endpoints (active negative : Bool) :
    QProb.Equiv (computedBounds (nullLaw active negative)).lowerEffect (if negative then QProb.zero else half) ∧
      QProb.Equiv (computedBounds (nullLaw active negative)).upperEffect (if negative then half else QProb.one) := by
  cases active <;> cases negative <;> decide +kernel

theorem nullLaw_sharp (active negative : Bool) : ComputedBoundsSharp projection (nullLaw active negative) :=
  computedBounds_sharp projection projected_iv_graph (nullLaw active negative) (nullLaw_compatible active negative)

theorem nullLaw_all_risk_corners (active negative controlUpper treatedUpper : Bool) :
    RisksAttainableAt projection (nullLaw active negative)
      (computedSelectedRisk (nullLaw active negative) controlUpper treatedUpper) :=
  (nullLaw_sharp active negative).risk_corners controlUpper treatedUpper

theorem nullLaw_native_effect_bounds (active negative : Bool)
    (native : FiniteHiddenDAGSCM signature projection) (observed : HasObservedLaw native (nullLaw active negative)) :
    QProb.LE (if negative then QProb.zero else half) (nativeEffectScore native) ∧
      QProb.LE (nativeEffectScore native) (if negative then half else QProb.one) := by
  have bounds := (nullLaw_sharp active negative).effect_bounds native observed
  exact ⟨QProb.le_congr (nullLaw_effect_endpoints active negative).1 (QProb.equiv_refl _) bounds.1,
    QProb.le_congr (QProb.equiv_refl _) (nullLaw_effect_endpoints active negative).2 bounds.2⟩

theorem nullLaw_native_effect_endpoints (active negative : Bool) :
    EffectScoreAttainableAt projection (nullLaw active negative) (if negative then QProb.zero else half) ∧
      EffectScoreAttainableAt projection (nullLaw active negative) (if negative then half else QProb.one) := by
  have endpoints := (nullLaw_sharp active negative).effect_endpoints
  rcases endpoints.1 with ⟨lower, lowerLaw, lowerScore⟩
  rcases endpoints.2 with ⟨upper, upperLaw, upperScore⟩
  exact ⟨⟨lower, lowerLaw, QProb.equiv_trans lowerScore (nullLaw_effect_endpoints active negative).1⟩,
    ⟨upper, upperLaw, QProb.equiv_trans upperScore (nullLaw_effect_endpoints active negative).2⟩⟩

theorem positive_uniform_sharp : ComputedBoundsSharp projection BinaryInstrumentalCompatibility.uniformLaw :=
  computedBounds_sharp projection projected_iv_graph BinaryInstrumentalCompatibility.uniformLaw (by decide +kernel)

theorem excluded_compatibility_flag : (computedBounds BinaryInstrumentalCompatibility.excludedLaw).compatible = false := by
  decide +kernel

theorem excluded_no_native : ¬ ∃ native : FiniteHiddenDAGSCM signature projection,
    HasObservedLaw native BinaryInstrumentalCompatibility.excludedLaw := by
  intro purported
  have checked := (computedBounds_compatible_iff projection projected_iv_graph
    BinaryInstrumentalCompatibility.excludedLaw).mpr purported
  rw [excluded_compatibility_flag] at checked
  exact Bool.noConfusion checked

end BinaryInstrumentalNullBounds
end Examples
end Causality
end Thesis
