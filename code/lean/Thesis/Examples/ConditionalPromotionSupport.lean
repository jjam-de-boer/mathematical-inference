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
containing-component restriction.  The checks in this module are numerical
and control-flow checks, not complete recursive data.  The companion
`ConditionalPromotionCompilation` now supplies that data at every demanded
marginal variant, builds the complete native tree, and proves its formula
literally equals this program's output before applying native soundness.
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

private def candidateFormula (outcome : IdentificationOutcome signature) : ProbabilityTerm signature :=
  match outcome with
  | .identified term => term
  | _ => unitProbabilityTerm signature

/-- Inspect the constructor abstractly before substituting the concrete run.
This keeps formula alignment from unfolding the complete recursive graph
search during simplification; no proof limits need to be increased. -/
private theorem identified_of_tag (outcome : IdentificationOutcome signature)
    (found : (match outcome with | .identified _ => true | _ => false) = true) :
    outcome = .identified (candidateFormula outcome) := by
  cases outcome with
  | identified _term => rfl
  | failed _failure => cases found
  | unfinished => cases found

def formula : ProbabilityTerm signature :=
  candidateFormula (identifyGuardedConditionalKernel projection.observedGraph query)

theorem identified : identifyGuardedConditionalKernel projection.observedGraph query = .identified formula :=
  identified_of_tag _ (by decide +kernel)

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
