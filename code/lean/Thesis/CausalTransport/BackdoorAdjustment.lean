import Thesis.CausalTransport.ObservationalFormulaSelection
import Thesis.CausalTransport.HiddenDAGSupportedDomain

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Zero-aware adjustment candidates independent of ID's chosen output

An adjustment witness contains two actual graphical do-rule applications:
the selected covariates' marginal is unchanged by the action (rule 3), and
the outcome's conditional exchanges the action for observation given those
covariates (rule 2).  Their finite probability marginal/chain assembly proves
the adjustment formula; no external adjustment or identification theorem is
assumed.  Different witnesses may produce genuinely different expressions.

Support is only the literal formula's support.  A zero covariate weight skips
its conditional.  At a positive weight, rule 3 first supplies the *actual*
causal covariate mass, which constructs the rule-2 source conditioner.  Thus
soundness is not assumed to establish its own support, nor is global observed
positivity or positivity of the requested outcome added as a premise.
-/

/-- Sufficient graphical evidence for a particular adjustment set.  Both
fields are inspectable do-rule applications, not semantic equality axioms.
The disjointnesses allow the ordinary marginal and weighted chain steps. -/
structure BackdoorAdjustmentWitness (projection : FiniteLatentProjection S)
    (query : JointKernelQuery S) (covariates : NodeSet S) where
  action_disjoint : NodeSet.Disjoint query.action covariates
  outcome_disjoint : NodeSet.Disjoint query.outcome covariates
  removeAction : DoRuleApplication projection.observedGraph
    (rule3Left NodeSet.empty covariates query.action NodeSet.empty)
    (rule3Right NodeSet.empty covariates query.action NodeSet.empty)
  exchangeAction : DoRuleApplication projection.observedGraph
    (rule2Left NodeSet.empty query.outcome query.action covariates)
    (rule2Right NodeSet.empty query.outcome query.action covariates)

namespace BackdoorAdjustmentWitness

/-- The directed covariate weight is important: a supported zero contributes
zero without demanding the outcome conditional at that covariate cell. -/
def formula (query : JointKernelQuery S) (covariates : NodeSet S) : ProbabilityTerm S :=
  .marginalize covariates
    (.weightedMultiply (.kernel ⟨covariates, NodeSet.empty, NodeSet.empty⟩)
      (.kernel ⟨query.outcome, NodeSet.empty, NodeSet.union query.action covariates⟩))

theorem formula_actionFree (query : JointKernelQuery S) (covariates : NodeSet S) :
    (formula query covariates).ActionFree :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Rule 3 is interpreted independently of the outcome factor.  Both of its
endpoints are unconditional, so their support is available even at zeros. -/
noncomputable def weight_equivalent {query : JointKernelQuery S} {covariates : NodeSet S}
    (witness : BackdoorAdjustmentWitness P query covariates)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment) :
    model.TermEquivalentAt (.kernel ⟨covariates, query.action, NodeSet.empty⟩)
      (.kernel ⟨covariates, NodeSet.empty, NodeSet.empty⟩) reference := by
  simpa only [rule3Left, rule3Right, NodeSet.union_empty_left] using
    model.doRule_soundAt reference witness.removeAction
      (model.kernelSupportedAt_unconditional covariates (NodeSet.union NodeSet.empty query.action) reference)
      (model.kernelSupportedAt_unconditional covariates NodeSet.empty reference)

/-- A positive *actual causal* covariate kernel constructs the conditioner
of the outcome kernel.  The unconditional-denotation theorem relates the
kernel fraction to its genuine cylinder probability before positivity is
read back; no observational agreement is used to infer causal support. -/
private noncomputable def outcome_supported_of_positive_weight
    (model : FiniteHiddenDAGSCM S P) (query : JointKernelQuery S)
    (covariates : NodeSet S) (reference : S.Assignment)
    (positive : ProbabilityResult.PositiveSupportedValue
      (model.kernelDenote ⟨covariates, query.action, NodeSet.empty⟩ reference)) :
    model.TermSupportedAt (.kernel ⟨query.outcome, query.action, covariates⟩) reference := by
  let weightKernel : Kernel S := ⟨covariates, query.action, NodeSet.empty⟩
  let outcomeKernel : Kernel S := ⟨query.outcome, query.action, covariates⟩
  have collapsed : ProbabilityResult.PositiveSupportedValue
      (weightKernel.denote model.toLatentRootSCM reference) := by
    rw [← model.kernelDenote_preserved weightKernel reference]
    exact positive
  let cylinder := collapsed.transport
    (Kernel.unconditionalDenote model.toLatentRootSCM covariates query.action reference)
  have cylinderPositive : 0 < ((weightKernel.distribution model.toLatentRootSCM reference).probVal
      (Kernel.agreesOn covariates reference)).num := by
    cases cylinder.equivalent with
    | value equivalent => exact (QProb.equiv_num_pos_iff equivalent).mpr cylinder.positive
  apply model.termSupportedAt_of_collapsed
  apply Kernel.supportedAt_of_condition_positive model.toLatentRootSCM outcomeKernel reference
  rw [Kernel.distribution_eq_of_action model.toLatentRootSCM query.outcome covariates
    query.action covariates NodeSet.empty reference]
  exact cylinderPositive

/-- One finite covariate contribution is the genuine causal joint kernel.
Its factor comparison is demanded only on a positive causal weight.  The
independently interpreted weight leaf transfers that positivity to the
printed weight, whose supported contribution then supplies the printed
factor.  At zero weight neither conditional must be manufactured. -/
private noncomputable def contribution_soundAt {query : JointKernelQuery S} {covariates : NodeSet S}
    (witness : BackdoorAdjustmentWitness P query covariates)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (printed : model.TermSupportedAt
      (.weightedMultiply (.kernel ⟨covariates, NodeSet.empty, NodeSet.empty⟩)
        (.kernel ⟨query.outcome, NodeSet.empty, NodeSet.union query.action covariates⟩)) reference) :
    model.TermEquivalentAt (.kernel ⟨NodeSet.union query.outcome covariates, query.action, NodeSet.empty⟩)
      (.weightedMultiply (.kernel ⟨covariates, NodeSet.empty, NodeSet.empty⟩)
        (.kernel ⟨query.outcome, NodeSet.empty, NodeSet.union query.action covariates⟩)) reference := by
  have weights := witness.weight_equivalent model reference
  have chain : model.TermEquivalentAt
      (.kernel ⟨NodeSet.union query.outcome covariates, query.action, NodeSet.empty⟩)
      (.weightedMultiply (.kernel ⟨covariates, query.action, NodeSet.empty⟩)
        (.kernel ⟨query.outcome, query.action, covariates⟩)) reference := by
    apply model.termEquivalentAt_of_collapsed
    simpa only [NodeSet.union_empty_right] using
      ProbabilityTerm.weightedChain_soundAt model.toLatentRootSCM query.action query.outcome covariates NodeSet.empty reference
  apply ProbabilityResult.trans chain
  apply ProbabilityResult.weightedMultiply_congr_on_positive weights
  intro positive
  let observedPositive := positive.transport weights
  let observedFactor := ProbabilityResult.supported_factor_of_weightedMultiply observedPositive printed
  let causalFactor := outcome_supported_of_positive_weight model query covariates reference positive
  simpa only [rule2Left, rule2Right, NodeSet.union_empty_left] using
    model.doRule_soundAt reference witness.exchangeAction
      (by simpa only [rule2Left, NodeSet.union_empty_left] using causalFactor)
      observedFactor

/-- Native adjustment soundness on exactly the literal formula's support.
Finite marginal substitutions are retained, with a contribution proof at
every demanded variant.  The source marginal is an ordinary probability
identity with internally constructed unconditional endpoint support. -/
noncomputable def soundAt {query : JointKernelQuery S} {covariates : NodeSet S}
    (witness : BackdoorAdjustmentWitness P query covariates)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (printed : model.TermSupportedAt (formula query covariates) reference) :
    model.TermEquivalentAt query.sourceTerm (formula query covariates) reference := by
  letI : DecidableEq S.Assignment :=
    FiniteProduct.assignmentDecidableEq S.count S.Value S.valueDecidableEq
  let variants := ProbabilityTerm.marginalAssignments S covariates reference
  let joint : ProbabilityTerm S :=
    .kernel ⟨NodeSet.union query.outcome covariates, query.action, NodeSet.empty⟩
  let contribution : ProbabilityTerm S :=
    .weightedMultiply (.kernel ⟨covariates, NodeSet.empty, NodeSet.empty⟩)
      (.kernel ⟨query.outcome, NodeSet.empty, NodeSet.union query.action covariates⟩)
  have contributionSupported : forall variant, variant ∈ variants →
      model.TermSupportedAt contribution variant := by
    intro variant listed
    exact ProbabilityResult.supported_map_of_mem_sum variants
      (fun assignment => model.termDenote contribution assignment) variant listed printed
  let four := FourWayDisjoint.of_empty_w query.action query.outcome covariates
    query.action_outcome_disjoint witness.action_disjoint witness.outcome_disjoint
  let marginal : DoCalculusDerivation P.observedGraph query.sourceTerm (.marginalize covariates joint) :=
    .marginalization query.action query.outcome covariates NodeSet.empty four
  let marginalSupported : model.TermSupportedAt (.marginalize covariates joint) reference :=
    ProbabilityResult.sum_map_supported_of_mem variants (fun variant => model.termDenote joint variant)
      (fun variant _ => model.kernelSupportedAt_unconditional (NodeSet.union query.outcome covariates) query.action variant)
  have first := marginal.hiddenDAG_denotational_soundAt
    ⟨model.kernelSupportedAt_unconditional query.outcome query.action reference, marginalSupported, ()⟩
  have second : model.TermEquivalentAt (.marginalize covariates joint)
      (formula query covariates) reference :=
    ProbabilityResult.sum_map_congr_mem variants
      (fun variant => model.termDenote joint variant)
      (fun variant => model.termDenote contribution variant)
      (fun variant listed => witness.contribution_soundAt model variant (contributionSupported variant listed))
  exact ProbabilityResult.trans first second

/-- The independent formula enters a catalogue with no engine-result field.
Graphical validity is proved for every native model on its printed domain;
the catalogue may also retain ID's own candidate as a fallback. -/
noncomputable def candidate {query : JointKernelQuery S} {covariates : NodeSet S}
    (witness : BackdoorAdjustmentWitness P query covariates) :
    GuardedObservationalFormula P query.sourceTerm where
  formula := formula query covariates
  actionFree := formula_actionFree query covariates
  guard := .always
  interpret := fun model reference _ _ printed => witness.soundAt model reference printed

/-- Unlike an action-one candidate, this alternative is a graph-valid
positive-covered representation on its entire printed support domain.  It
therefore inhabits the existing graph-level semantic identification predicate
without changing that predicate to a law-specific one. -/
theorem supported_identifiable {query : JointKernelQuery S} {covariates : NodeSet S}
    (witness : BackdoorAdjustmentWitness P query covariates) :
    HiddenDAGSupportedDomain.jointIdentifiable P query :=
  ⟨formula query covariates, formula_actionFree query covariates,
    HiddenDAGSupportedDomain.positiveCovered_of_zeroFree _ ⟨trivial, trivial⟩,
    fun model reference admissible =>
      ⟨witness.soundAt model reference
        (model.supportedAt_of_usedConditionalsAdmissible _ reference admissible)⟩⟩

end BackdoorAdjustmentWitness
end Causality
end Thesis
