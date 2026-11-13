import Thesis.Causality.CausalRemainder
import Thesis.Examples.CausalAbstractionScale
import Thesis.Examples.CausalAbstractionEmergence

namespace Thesis.Examples.CausalAbstraction
open Probability Causality CausalRemainder

/-! Event remainders on actual aggregation maps. The OR comparison is a
specialization of the general rational gap, using the already proved laws.
Exactness is recovered only by vanishing on all events, not one event. -/

/-- A declared OR comparison accepts double-true cause surgery. It respects
forced assignments but will fail the separate full-law exactness obligation. -/
def orComparisonMap : CausalInterventionMap microSignature macroSignature where
  microModel := microModel
  macroModel := orMacro
  assignmentMap := mergeAssignment Bool.or
  omega intervention :=
    if intervention.value (0 : Fin 3) = some true ∧ intervention.value (1 : Fin 3) = some true
    then some macroDoTrue else none
  respects := by
    intro intervention action defined state realizes
    split at defined
    next both =>
      cases Option.some.inj defined
      apply orCoarsening.representative_respects macroDoTrue rfl state
      intro node value forced
      have bound : node.val < 3 := node.isLt
      by_cases first : node.val = 0
      · have nodeEq : node = (0 : Fin 3) := Fin.ext first
        subst node
        have selected : true = value := Option.some.inj forced
        rw [← selected]
        exact realizes (0 : Fin 3) true both.1
      · by_cases second : node.val = 1
        · have nodeEq : node = (1 : Fin 3) := Fin.ext second
          subst node
          have selected : true = value := Option.some.inj forced
          rw [← selected]
          exact realizes (1 : Fin 3) true both.2
        · have nodeEq : node = (2 : Fin 3) := Fin.ext (by change node.val = 2; omega)
          subst node
          cases forced
    next absent => cases defined

private theorem gap_one_third : QProb.Equiv (gap QProb.one ⟨1, 3, by decide⟩) ⟨2, 3, by decide⟩ := by
  decide +kernel

/-- The old 1 versus 1/3 example now instantiates the general discrepancy
calculus, rather than introducing another isolated probability calculation. -/
theorem or_remainder_two_thirds : QProb.Equiv
    (orComparisonMap.remainder microDoubleTrue macroDoTrue yTrue) ⟨2, 3, by decide⟩ :=
  QProb.equiv_trans (gap_congr or_merge_fails.1 or_merge_fails.2.1) gap_one_third

theorem or_remainder_positive : 0 < (orComparisonMap.remainder microDoubleTrue macroDoTrue yTrue).num :=
  (QProb.equiv_num_pos_iff or_remainder_two_thirds).mpr (by decide +kernel)

/-- The comparison is illegal because its accepted pair fails Exact. It
remains a well-defined comparison of two unconditional finite laws. -/
theorem or_comparison_not_exact : ¬ orComparisonMap.Exact := by
  intro exactness
  have zero := (orComparisonMap.exact_iff_remainder_zero.mp exactness)
    microDoubleTrue macroDoTrue rfl yTrue
  have contradiction := QProb.equiv_trans (QProb.equiv_symm or_remainder_two_thirds) zero
  exact (by decide +kernel : ¬ QProb.Equiv (⟨2, 3, by decide⟩ : QProb) QProb.zero) contradiction

/-- Each edge and the composite of the existing three-grain chain have
zero remainder on every event wherever both partial intervention maps exist. -/
theorem exact_grain_chain_remainders (intervention middleAction lastAction)
    (firstDefined : andInterventionMap.omega intervention = some middleAction)
    (secondDefined : collapseInterventionMap.omega middleAction = some lastAction)
    (middleEvent : Event macroSignature.Assignment) (lastEvent : Event terminalSignature.Assignment) :
    QProb.Equiv (andInterventionMap.remainder intervention middleAction middleEvent) QProb.zero ∧
    QProb.Equiv (collapseInterventionMap.remainder middleAction lastAction lastEvent) QProb.zero ∧
    QProb.Equiv (twoStepMap.remainder intervention lastAction lastEvent) QProb.zero := by
  refine ⟨(andInterventionMap.exact_iff_remainder_zero.mp and_intervention_exact) _ _ firstDefined _,
    (collapseInterventionMap.exact_iff_remainder_zero.mp collapse_intervention_exact) _ _ secondDefined _, ?_⟩
  apply CausalInterventionMap.comp_remainder_zero andInterventionMap collapseInterventionMap rfl
  · exact and_intervention_exact
  · exact collapse_intervention_exact
  · change (andInterventionMap.omega intervention).bind collapseInterventionMap.omega = some lastAction
    rw [firstDefined]
    exact secondDefined

theorem and_double_true_defined : andInterventionMap.omega microDoubleTrue = some macroDoTrue := by
  change some (coarseAction (some true) none) = some macroDoTrue
  apply congrArg some
  apply HardIntervention.extensional
  decide +kernel

/-- Contrast between the two fine-to-coarse aggregation choices: an exact
AND edge has zero discrepancy, while the illegal OR edge has positive gap. -/
theorem aggregation_remainders :
    QProb.Equiv (andInterventionMap.remainder microDoubleTrue macroDoTrue yTrue) QProb.zero ∧
    QProb.Equiv (orComparisonMap.remainder microDoubleTrue macroDoTrue yTrue) ⟨2, 3, by decide⟩ :=
  ⟨(andInterventionMap.exact_iff_remainder_zero.mp and_intervention_exact) _ _ and_double_true_defined _, or_remainder_two_thirds⟩

/-- Every action that forces E, even together with other coarse targets,
is unsupported by this lift. The conclusion applies to either Boolean value. -/
theorem emergent_forced_action_unsupported (action : HardIntervention emergentSignature)
    (value : Bool) (forced : action.value (2 : Fin 3) = some value) :
    ∀ intervention : HardIntervention macroSignature,
      emergentInterventionMap.omega intervention ≠ some action := by
  apply emergentInterventionMap.no_representative_of_unforced_image (2 : Fin 3) _ action value forced
  intro intervention candidate defined
  cases Option.some.inj defined
  rfl

/-- Unsupported interventions are not impossible states. Actual micro
assignments can realize E=true or E=false through the derived readout. -/
theorem emergent_values_are_realizable : ∀ value : Bool,
    appendEmergent (coarseState true value) (2 : Fin 3) = value := by decide +kernel

end Thesis.Examples.CausalAbstraction
