import Thesis.CausalTransport.GuardedConditionalSoundness
import Thesis.Examples.GuardedIdentificationKernel

namespace Thesis
namespace Causality
namespace Examples
namespace NullActionPromotionSupport

open Probability GuardedKernelZeroRegression

/-!
# Conditioner promotion at a null factual action

Reuse the five-node full hidden DAG, but make `X` constantly false while
retaining its declared hidden parent.  The mediator still copies `X` with
an independent noisy bit, and `Y` remains false.  For `P(Y | do(X), M)` at
the all-true reference, the factual action `X = true` has zero mass, yet the
actual intervened conditioner `M = true` has positive mass.

The intrinsic support constructor uses that actual causal conditioner, not
observable overlap.  The promotion theorem builds support after additionally
fixing `M`, and the recorded graph test gives native rule-2 equality from
only the original source support.  The old overlap premise would exclude
this application even though its actual conditional endpoints are defined.

The full guarded conditional program also succeeds and computes a supported
zero.  Its terminal joint recursion exercises ancestry pruning and a
containing-component restriction.  These last checks are program/numerical
checks, not an instantiation of every recursive joint data field: that deeper
data-validation stage remains separate from the generic promotion proof
actually applied here.
-/

def model : FiniteHiddenDAGSCM signature projection := {
  GuardedKernelZeroRegression.model with
  mechanism := fun node parents seed =>
    if node.val = 1 then false else GuardedKernelZeroRegression.model.mechanism node parents seed
}

def query : ConditionalKernelQuery signature := {
  outcome := NodeSet.singleton y
  action := NodeSet.singleton x
  condition := NodeSet.singleton mediator
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
}

/-- The actual incoming-action/outgoing-mediator graph test is checked,
and the remaining given-set is retained by the shared rule compiler. -/
def step : ConditionalExchangeStep projection.observedGraph query where
  node := mediator
  selected := rfl
  separated := by decide +kernel

theorem observational_action_is_null :
    (model.observationalDist.probVal (Kernel.agreesOn query.action reference)).num = 0 := by
  decide +kernel

/-- Read the actual positive conditioner from this SCM under `do(X = true)`.
This is not a positive observational cylinder or a chosen latent unit. -/
noncomputable def original_supported : model.TermSupportedAt query.sourceTerm reference :=
  model.termSupportedAt_of_collapsed query.sourceTerm reference
    (Kernel.supportedAt_of_condition_positive model.toLatentRootSCM query.operationKernel reference (by
      decide +kernel))

/-- One-model SCM composition constructs the promoted support; no second
support premise or global observed positivity is passed to the constructor. -/
noncomputable def promoted_supported :
    model.TermSupportedAt (query.exchangeCondition step.node step.selected).sourceTerm reference :=
  query.hiddenDAG_exchangeCondition_supportedAt step.node step.selected model reference original_supported

/-- The proved native rule-2 adapter interprets the actual graph-tested
promotion.  Its single original support input comes from causal conditioning. -/
noncomputable def promotion_sound :
    model.TermEquivalentAt query.sourceTerm (query.exchangeCondition step.node step.selected).sourceTerm reference :=
  step.hiddenDAG_soundAt model reference original_supported

def formula : ProbabilityTerm signature :=
  match identifyGuardedConditionalKernel projection.observedGraph query with
  | .identified term => term
  | _ => unitProbabilityTerm signature

theorem identified : identifyGuardedConditionalKernel projection.observedGraph query = .identified formula := by
  have found : (match identifyGuardedConditionalKernel projection.observedGraph query with
      | .identified _ => true | _ => false) = true := by decide +kernel
  cases result : identifyGuardedConditionalKernel projection.observedGraph query with
  | identified _term => simp only [formula, result]
  | failed _failure => simp only [result, Bool.false_eq_true] at found
  | unfinished => simp only [result, Bool.false_eq_true] at found

theorem source_supported_zero : (model.termDenote query.sourceTerm reference).map (fun value => value.num) = some 0 := by
  decide +kernel

theorem promoted_supported_zero :
    (model.termDenote (query.exchangeCondition step.node step.selected).sourceTerm reference).map
      (fun value => value.num) = some 0 := by decide +kernel

theorem formula_supported_zero : (model.termDenote formula reference).map (fun value => value.num) = some 0 := by
  decide +kernel

end NullActionPromotionSupport
end Examples
end Causality
end Thesis
