import Thesis.CausalTransport.BinaryInstrumentalAttainable
import Thesis.Examples.BinaryInstrumentalIdentification

namespace Thesis
namespace Causality
namespace Examples
namespace BinaryInstrumentalAttainable

open Probability BinaryInstrumental

private instance probabilityOrderDecidable (left right : QProb) : Decidable (QProb.LE left right) := by
  unfold QProb.LE
  infer_instance

/-!
# Native rational interior witnesses and exact rejection boundaries

Uniform IV observations admit the simultaneous risk pair `(1/3, 2/3)` and
the effect score `2/5`, which encodes the negative ATE `-1/5`.  These are
interior values with denominators different from the observed denominator.
The theorem constructs actual native models, not just feasible numeric pairs.

Null-arm laws are checked for either instrument value and either outcome
sign.  Perfect compliance tests collapsed intervals at both ATE signs.
Finally an incompatible observed law and an out-of-bounds request are rejected
by the complete attainable-set iff, not by incomplete numerical search.
-/

abbrev projection := BinaryInstrumentalCompatibility.projection
theorem projected_iv_graph : HasIVProjection projection := BinaryInstrumentalCompatibility.projected_iv_graph
abbrev uniformLaw := BinaryInstrumentalCompatibility.uniformLaw

def third : QProb := ⟨1, 3, by decide⟩
def twoThirds : QProb := ⟨2, 3, by decide⟩
def quarter : QProb := ⟨1, 4, by decide⟩
def twoFifths : QProb := ⟨2, 5, by decide⟩
def uniformRisks (action : Bool) : QProb := if action then twoThirds else third

theorem uniform_interior_pair : RisksAttainableAt projection uniformLaw uniformRisks := by
  apply (risksAttainableAt_iff_computed_bounds projection projected_iv_graph uniformLaw uniformRisks).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro action
  cases action <;> decide +kernel

theorem uniform_negative_interior_effect : EffectScoreAttainableAt projection uniformLaw twoFifths := by
  apply (effectScoreAttainableAt_iff_computed_bounds projection projected_iv_graph uniformLaw twoFifths).mpr
  decide +kernel

def nullRisks (negative action : Bool) : QProb :=
  if negative then (if action then quarter else twoThirds) else (if action then twoThirds else quarter)

theorem null_interior_pair (active negative : Bool) :
    RisksAttainableAt projection (BinaryInstrumentalNullBounds.nullLaw active negative) (nullRisks negative) := by
  apply (risksAttainableAt_iff_computed_bounds projection projected_iv_graph _ _).mpr
  refine ⟨BinaryInstrumentalNullBounds.nullLaw_compatible active negative, ?_⟩
  intro action
  cases active <;> cases negative <;> cases action <;> decide +kernel

def fullComplianceRisks (negative action : Bool) : QProb :=
  if action then (if negative then QProb.zero else QProb.one) else (if negative then QProb.one else QProb.zero)

theorem collapsed_risk_pair (negative : Bool) :
    RisksAttainableAt projection (BinaryInstrumentalEffectBounds.fullComplianceLaw negative) (fullComplianceRisks negative) := by
  apply (risksAttainableAt_iff_computed_bounds projection projected_iv_graph _ _).mpr
  refine ⟨BinaryInstrumentalIdentification.fullCompliance_compatible negative, ?_⟩
  intro action
  cases negative <;> cases action <;> decide +kernel

theorem collapsed_effect (negative : Bool) :
    EffectScoreAttainableAt projection (BinaryInstrumentalEffectBounds.fullComplianceLaw negative)
      (if negative then QProb.zero else QProb.one) := by
  apply (effectScoreAttainableAt_iff_computed_bounds projection projected_iv_graph _ _).mpr
  cases negative <;> decide +kernel

theorem incompatible_has_no_pair (risks : Bool → QProb) :
    ¬ RisksAttainableAt projection BinaryInstrumentalCompatibility.excludedLaw risks := by
  intro purported
  have compatible := (risksAttainableAt_iff_computed_bounds projection projected_iv_graph _ risks).mp purported |>.1
  have excluded : (computedBounds BinaryInstrumentalCompatibility.excludedLaw).compatible = false := by decide +kernel
  exact Bool.noConfusion (excluded.symm.trans compatible)

theorem incompatible_has_no_effect (score : QProb) :
    ¬ EffectScoreAttainableAt projection BinaryInstrumentalCompatibility.excludedLaw score := by
  intro purported
  have compatible := (effectScoreAttainableAt_iff_computed_bounds projection projected_iv_graph _ score).mp purported |>.1
  have excluded : (computedBounds BinaryInstrumentalCompatibility.excludedLaw).compatible = false := by decide +kernel
  exact Bool.noConfusion (excluded.symm.trans compatible)

theorem below_risk_interval_impossible : ¬ RisksAttainableAt projection uniformLaw (fun _ => QProb.zero) := by
  intro purported
  have bounds := (risksAttainableAt_iff_computed_bounds projection projected_iv_graph uniformLaw _).mp purported |>.2
  have excluded : ¬ QProb.LE ((computedBounds uniformLaw).lowerRisk false) QProb.zero := by decide +kernel
  exact excluded (bounds false).1

end BinaryInstrumentalAttainable
end Examples
end Causality
end Thesis
