import Thesis.CausalTransport.GuardedConditionalSoundness
import Thesis.Examples.GuardedIdentificationKernel

namespace Thesis
namespace Causality
namespace Examples
namespace GuardedConditionalZeroRegression

open Probability GuardedKernelZeroRegression

/-!
# A native Bayes compilation with a genuinely zero numerator

Reuse the original hidden-DAG mediator model: `Y` is constantly false and
`Z` copies the unbiased hidden root shared by `X,Y,Z`.  The declared common
cause blocks the exchange test for `P(Y | Z)`, so the actual guarded IDC run
uses its Bayes branch.  At `Y = true, Z = true` the conditional is a supported
zero, although the observed law is not globally positive.

Unlike a computation-only regression, this fixture supplies the uniform
compiler's actual recursive local data.  The action-free joint call starts
from unit observational data; all numerator and denominator marginal variants
receive that inherited data.  The displayed denominator has value one half.
The generic native soundness adapter interprets the constructed support tree.
No complete tree or semantic-equality theorem is passed in as fixture data.
-/

def query : ConditionalKernelQuery signature := {
  outcome := NodeSet.singleton y
  action := NodeSet.empty
  condition := NodeSet.singleton z
  action_outcome_disjoint := NodeSet.disjoint_empty_left _
  action_condition_disjoint := NodeSet.disjoint_empty_left _
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
}

def numeratorFormula : ProbabilityTerm signature :=
  .marginalize (NodeSet.diff NodeSet.full query.jointNumerator.outcome) (observationalJointTerm signature)

def formula : ProbabilityTerm signature := conditionalBayesTermFrom query numeratorFormula

theorem no_exchange : conditionalExchangeStep? projection.observedGraph query = none := by
  have absent : (NodeSet.members query.condition).find?
      (conditionalExchangeTest projection.observedGraph query) = none := by decide +kernel
  unfold conditionalExchangeStep?
  split
  · rfl
  · rename_i found
    rw [absent] at found
    cases found

theorem numerator_identified :
    identifyGuardedJointKernel projection.observedGraph query.jointNumerator = .identified numeratorFormula := by
  have emptyAction : NodeSet.isEmpty query.jointNumerator.action = true := by decide +kernel
  simp only [identifyGuardedJointKernel, kernelIdentificationFuel, identifyGuardedKernelFuel,
    NodeSet.inter_full_right, emptyAction, if_true]
  rfl

theorem identified : identifyGuardedConditionalKernel projection.observedGraph query = .identified formula := by
  simp only [identifyGuardedConditionalKernel, identifyGuardedConditionalKernelFuel, no_exchange, numerator_identified]
  rfl

/-- Keep the actual successful program compilation, rather than substituting
a bespoke observational conditional derivation for its generated formula. -/
noncomputable def compilation :=
  (identifyGuardedConditionalKernelLocalCompilation projection.observedGraph.dSeparationCorrectness query identified).aligned

/-- Instantiate every primitive field of the actual compiled boundary.
The displayed source and denominator are computed from the nonpositive
model; the inherited joint data is unit at every requested finite variant. -/
noncomputable def localData : compilation.Data model.toLatentRootSCM reference := by
  change (identifyGuardedConditionalKernelFuelLocalCompilation
    projection.observedGraph.dSeparationCorrectness (1 + 1) query identified).compilation.Data
      model.toLatentRootSCM reference
  rw [identifyGuardedConditionalKernelFuelLocalCompilation_bayes_data
    projection.observedGraph.dSeparationCorrectness 1 query no_exchange numerator_identified identified]
  refine {
    sourceSupported := ?_
    numeratorData := ?_
    denominatorData := ?_
    denominatorPositive := ?_
  }
  · exact model.termSupportedAt_to_collapsed query.sourceTerm reference
      (model.kernelSupportedAt_of_observational_overlap query.operationKernel reference (by
        unfold FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt
        decide +kernel))
  · exact fun _variant _listed => ()
  · exact fun _variant _listed _innerVariant _innerListed => ()
  · refine ⟨(⟨1, 2, by decide⟩ : QProb), .value ?_, by decide⟩
    decide +kernel

/-- This is the generic theorem applied to the literal successful formula
and constructed native tree, not a numerical equality replacing soundness. -/
noncomputable def native_sound : model.TermEquivalentAt query.sourceTerm formula reference :=
  compilation.hiddenDAG_soundAt model reference localData

theorem formula_supported_zero : (model.termDenote formula reference).map (fun value => value.num) = some 0 := by
  decide +kernel

theorem source_supported_zero : (model.termDenote query.sourceTerm reference).map (fun value => value.num) = some 0 := by
  decide +kernel

/-- The local theorem really applies outside the positive model class.
The complete all-true observed assignment asks for impossible `Y = true`. -/
theorem model_not_observationally_positive : ¬ model.ObservationallyPositive := by
  intro positive
  have impossible := positive reference
  have zero : (model.observationalDist.probVal (FiniteProbRecord.singletonEvent reference)).num = 0 := by
    decide +kernel
  rw [zero] at impossible
  exact Nat.not_lt_zero _ impossible

end GuardedConditionalZeroRegression
end Examples
end Causality
end Thesis
