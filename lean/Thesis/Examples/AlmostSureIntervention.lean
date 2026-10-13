import Thesis.CausalTransport.ObservationalFormulaSelection
import Thesis.Examples.HiddenDAGCompleteness

namespace Thesis
namespace Causality
namespace Examples
namespace AlmostSureIntervention

open Probability HiddenDAGCollapse

/-!
# A law-specific candidate despite actual graph-level failure

Keep the original hidden relay graph and mechanisms.  Only the private noise
at `U` becomes concentrated on true, with a *listed zero-weight false atom*.
Consequently `X = true` with probability one.  Setting that already factual
value preserves the whole population law, despite the existing failed joint
and conditional ID queries on this graph.

The zero-noise unit is deliberately retained: it has factual `X = false`,
and forcing `X = true` changes its outcome.  This checks almost-sure rather
than literal unitwise invariance.  The opposite action is not justified by
the probability-one guard, even though the observational formula is defined.
No missing conditional is completed, and graph failure remains unchanged.
-/

def concentrated : FiniteProbRecord Bool where
  atoms := [(false, 0), (true, 1)]
  den := 1
  den_pos := by decide
  total_mass := rfl

def factors (node : Fin fullGraph.count) : FiniteProbRecord Bool :=
  if node.val = 0 then concentrated else unbiased

/-- An actual native SCM with the original graph and equations.  The finite
product proof is rebuilt for the new prior, not retained from a different law. -/
def model : FiniteHiddenDAGSCM signature projection := {
  HiddenDAGCollapse.model with
  factor := factors
  prior := FiniteProduct.record 5 (fun _ => Bool) factors
  product_law := FiniteProduct.record_rectangular_probVal 5 (fun _ => Bool) factors
}

def reference : signature.Assignment := fun _ => true
def opposite : signature.Assignment := fun _ => false
def zeroUnit : model.NoiseAssignment := fun _ => false

/-- Probability one is checked in the original native record, with the
zero-weight atom and all unused independent noises still present. -/
theorem factual_action_one : QProb.Equiv
    (model.observationalDist.probVal (Kernel.agreesOn (NodeSet.singleton x) reference)) QProb.one := by
  decide +kernel

theorem zero_unit_factually_opposite :
    model.evalObserved (HardIntervention.empty signature) zeroUnit x = false := by
  decide +kernel

/-- The population theorem must not demand agreement at every noise label:
at this zero-weight unit forcing `X` really does change `Y`. -/
theorem zero_unit_outcome_changes :
    model.evalObserved (HardIntervention.empty signature) zeroUnit y = false ∧
      model.evalObserved ((HardIntervention.empty signature).set x true) zeroUnit y = true := by
  decide +kernel

noncomputable def jointCandidate : GuardedObservationalFormula projection HiddenDAGCompleteness.failedJointQuery.sourceTerm :=
  .ofActionOne HiddenDAGCompleteness.failedJointQuery.operationKernel

noncomputable def conditionalCandidate :
    GuardedObservationalFormula projection HiddenDAGCompleteness.failedConditionalQuery.sourceTerm :=
  .ofActionOne HiddenDAGCompleteness.failedConditionalQuery.operationKernel

theorem joint_available : jointCandidate.available model.observationalDist reference = true := by
  decide +kernel

theorem conditional_available : conditionalCandidate.available model.observationalDist reference = true := by
  decide +kernel

/-- The selector really returns the law-specific candidate; this is not an
invocation of the failed graph engine under a relabelled success predicate. -/
theorem joint_selected : GuardedObservationalFormula.select model.observationalDist reference
    [jointCandidate] = some jointCandidate := by
  simp only [GuardedObservationalFormula.select, joint_available, if_true]

theorem conditional_selected : GuardedObservationalFormula.select model.observationalDist reference
    [conditionalCandidate] = some conditionalCandidate := by
  simp only [GuardedObservationalFormula.select, conditional_available, if_true]

noncomputable def joint_native_sound : model.TermEquivalentAt
    HiddenDAGCompleteness.failedJointQuery.sourceTerm jointCandidate.formula reference :=
  GuardedObservationalFormula.select_soundAt model reference [jointCandidate] jointCandidate joint_selected
    (model.kernelSupportedAt_unconditional _ _ reference)

/-- Original causal conditioning support is established separately from
the observational acceptance test.  It is not inferred just because a
different formula returned a number. -/
noncomputable def conditional_source_supported : model.TermSupportedAt
    HiddenDAGCompleteness.failedConditionalQuery.sourceTerm reference :=
  model.kernelSupportedAt_of_observational_overlap _ reference (by
    change 0 < (model.observationalDist.probVal
      (Kernel.agreesOn (NodeSet.union (NodeSet.singleton x) (NodeSet.singleton z)) reference)).num
    decide +kernel)

noncomputable def conditional_native_sound : model.TermEquivalentAt
    HiddenDAGCompleteness.failedConditionalQuery.sourceTerm conditionalCandidate.formula reference :=
  GuardedObservationalFormula.select_soundAt model reference [conditionalCandidate] conditionalCandidate conditional_selected
    conditional_source_supported

/-- These unchanged graph queries still fail.  The new theorem is explicitly
about this law and action reference, not a contradiction of graph completeness. -/
theorem graph_joint_still_failed : identifyGuardedJointKernel projection.observedGraph
    HiddenDAGCompleteness.failedJointQuery = .failed HiddenDAGCompleteness.jointFailure.val :=
  (identifyGuardedJointKernel_failed_iff _ _ _).mpr HiddenDAGCompleteness.jointFailure.property

theorem graph_conditional_still_failed : identifyGuardedConditionalKernel projection.observedGraph
    HiddenDAGCompleteness.failedConditionalQuery = .failed HiddenDAGCompleteness.conditionalFailure.val :=
  (identifyGuardedConditionalKernel_failed_iff _ _ _).mpr HiddenDAGCompleteness.conditionalFailure.property

/-- A defined observational formula is insufficient for the opposite
action.  Acceptance must retain its probability-one causal justification. -/
theorem opposite_action_rejected : jointCandidate.available model.observationalDist opposite = false := by
  decide +kernel

theorem opposite_observational_formula_defined :
    (jointCandidate.formula.observationalDenote model.observationalDist opposite).isSome = true := by
  decide +kernel

theorem opposite_selection_empty : GuardedObservationalFormula.select model.observationalDist opposite
    [jointCandidate] = none := by
  simp only [GuardedObservationalFormula.select, opposite_action_rejected,
    Bool.false_eq_true, if_false]

end AlmostSureIntervention
end Examples
end Causality
end Thesis
