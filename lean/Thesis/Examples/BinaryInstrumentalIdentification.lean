import Thesis.CausalTransport.BinaryInstrumentalIdentification
import Thesis.Examples.BinaryInstrumentalEffectBounds
import Thesis.Examples.BinaryInstrumentalNullBounds

namespace Thesis
namespace Causality
namespace Examples
namespace BinaryInstrumentalIdentification

open Probability BinaryInstrumental

/-!
# Identified and nonidentified IV laws, including null support

Perfect compliance with either outcome sign identifies both risks and the
signed ATE.  Uniform observations identify none of them.  With a deterministic
instrument and deterministic factual treatment, only that treatment's risk is
identified; the other risk and ATE remain free.  These statements use the
complete native-model classification, not just values in an endpoint family.

All positive identification claims first establish whole-law compatibility.
The excluded IV fixture is deliberately not passed to the classification:
on an empty model class universal agreement would be logically vacuous.
-/

abbrev projection := BinaryInstrumentalCompatibility.projection
theorem projected_iv_graph : HasIVProjection projection := BinaryInstrumentalCompatibility.projected_iv_graph

theorem fullCompliance_compatible (negative : Bool) :
    (computedBounds (BinaryInstrumentalEffectBounds.fullComplianceLaw negative)).compatible = true := by
  cases negative <;> decide +kernel

theorem fullCompliance_risk_identified (negative action : Bool) :
    RiskIdentifiedAt projection (BinaryInstrumentalEffectBounds.fullComplianceLaw negative) action := by
  apply (riskIdentificationCheck_iff projection projected_iv_graph _ (fullCompliance_compatible negative) action).mp
  cases negative <;> cases action <;> decide +kernel

theorem fullCompliance_effect_identified (negative : Bool) :
    EffectIdentifiedAt projection (BinaryInstrumentalEffectBounds.fullComplianceLaw negative) := by
  apply (effectIdentificationCheck_iff projection projected_iv_graph _ (fullCompliance_compatible negative)).mp
  cases negative <;> decide +kernel

theorem uniform_risk_not_identified (action : Bool) :
    ¬ RiskIdentifiedAt projection BinaryInstrumentalCompatibility.uniformLaw action := by
  intro purported
  have checked := (riskIdentificationCheck_iff projection projected_iv_graph _ (by decide +kernel) action).mpr purported
  have failed : riskIdentificationCheck BinaryInstrumentalCompatibility.uniformLaw action = false := by
    cases action <;> decide +kernel
  exact Bool.noConfusion (failed.symm.trans checked)

theorem uniform_effect_not_identified :
    ¬ EffectIdentifiedAt projection BinaryInstrumentalCompatibility.uniformLaw := by
  intro purported
  have checked := (effectIdentificationCheck_iff projection projected_iv_graph _ (by decide +kernel)).mpr purported
  have failed : effectIdentificationCheck BinaryInstrumentalCompatibility.uniformLaw = false := by decide +kernel
  exact Bool.noConfusion (failed.symm.trans checked)

def constantLaw (active : Bool) : FiniteProbRecord signature.Assignment :=
  ⟨[(BinaryInstrumentalCompatibility.assignment active false true, 1)], 1, by decide, rfl⟩

theorem constantLaw_compatible (active : Bool) : (computedBounds (constantLaw active)).compatible = true := by
  cases active <;> decide +kernel

theorem constantLaw_factual_risk_identified (active : Bool) : RiskIdentifiedAt projection (constantLaw active) false := by
  apply (riskIdentificationCheck_iff projection projected_iv_graph _ (constantLaw_compatible active) false).mp
  cases active <;> decide +kernel

theorem constantLaw_other_risk_not_identified (active : Bool) : ¬ RiskIdentifiedAt projection (constantLaw active) true := by
  intro purported
  have checked := (riskIdentificationCheck_iff projection projected_iv_graph _ (constantLaw_compatible active) true).mpr purported
  have failed : riskIdentificationCheck (constantLaw active) true = false := by cases active <;> decide +kernel
  exact Bool.noConfusion (failed.symm.trans checked)

theorem constantLaw_effect_not_identified (active : Bool) : ¬ EffectIdentifiedAt projection (constantLaw active) := by
  intro purported
  have checked := (effectIdentificationCheck_iff projection projected_iv_graph _ (constantLaw_compatible active)).mpr purported
  have failed : effectIdentificationCheck (constantLaw active) = false := by cases active <;> decide +kernel
  exact Bool.noConfusion (failed.symm.trans checked)

end BinaryInstrumentalIdentification
end Examples
end Causality
end Thesis
