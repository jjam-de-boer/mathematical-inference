import Thesis.CausalTransport.BoundedNativeRepresentation
import Thesis.Examples.HiddenDAGMultivaluedPresentation

namespace Thesis.Causality.Examples.BoundedNativeConditionals

open Probability HiddenDAGMultivaluedPresentation

/-!
# Bounded native coding preserves factual nulls and supported conditionals

The genuine three-valued finite-population fixture has factual probability
zero at count two, although two remains a declared intervention value. Its
bounded native representative keeps that factual null. Forcing the count to
two instead makes the evidence positive, and every event of the resulting
supported conditioned record is preserved.

These are same-model preservation checks, not a conditional-identification
policy for an observationally compatible family. No factual null conditional
is supplied, and no observed-support hypothesis is substituted for the
original causal evidence required by conditioning.
-/

def evidence : Event signature.Assignment := fun values => decide (readValue (values y) = 2)
def forceNull : HardIntervention signature := (HardIntervention.empty signature).set y nullCode
def represented := model.boundedSearchRepresentative

theorem factual_evidence_zero : (represented.model.observationalValue evidence).num = 0 :=
  (model.boundedSearchRepresentative_num_zero_iff (HardIntervention.empty signature) evidence).mpr
    ((QProb.equiv_num_zero_iff null_observed_y).mpr rfl)

theorem no_factual_conditional_support : ¬ represented.model.observationalDist.EventPositive evidence := by
  intro positive
  change 0 < (represented.model.observationalValue evidence).num at positive
  rw [factual_evidence_zero] at positive
  exact Nat.lt_irrefl 0 positive

theorem forced_evidence_positive : (model.interventionalDist forceNull).EventPositive evidence :=
  (QProb.equiv_num_pos_iff do_y_null_probability_one).mpr (by decide : 0 < QProb.one.num)

theorem forced_evidence_preserved : (represented.model.interventionalDist forceNull).EventPositive evidence :=
  (model.boundedSearchRepresentative_eventPositive_iff forceNull evidence).mpr forced_evidence_positive

theorem all_supported_conditioned_events (event : Event signature.Assignment) :
    QProb.Equiv
      (((represented.model.interventionalDist forceNull).conditionOn evidence forced_evidence_preserved).probVal event)
      (((model.interventionalDist forceNull).conditionOn evidence forced_evidence_positive).probVal event) :=
  model.boundedSearchRepresentative_conditionOn_probVal forceNull evidence event forced_evidence_positive

end Thesis.Causality.Examples.BoundedNativeConditionals
