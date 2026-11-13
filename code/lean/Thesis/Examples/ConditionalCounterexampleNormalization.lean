import Thesis.CausalTransport.ConditionalCounterexampleNormalization
import Thesis.Examples.HedgeReadout

namespace Thesis
namespace Causality
namespace Examples
namespace ConditionalReverseNormalization

open Probability
open HedgePrivateReadout

/-!
# An irreducible conditional countermodel with unequal denominators

Reuse the actual positive models on `A → R → Y`, with `A ↔ R`, from
`HedgeReadout`.  The same private biased channel reads `R` into `Y` in
both models.  The new query is `P(R | do(A), Y)`, whose joint numerator
contains both `R` and `Y`.

The old regression already proves that the two `P(Y | do(A))` laws
differ.  Thus the matched-denominator adapter cannot apply to this pair.
Nevertheless `P(Y | do(A), R)` is identifiable: the actual conditional
program succeeds, and its checked certificate is interpreted by completed
soundness.  Two-way normalization therefore converts this same pair into
a countermodel for the requested conditional.

The source query has no exchangeable conditioner and its joint call fails.
This is a genuine irreducible terminal example, not a successful query,
an empty given-set, a difference in support, or a finite table disconnected
from SCM semantics.  No numerical equality or reverse-channel premise is
supplied to the new constructor.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton rootNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton outcomeNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

theorem no_exchange : conditionalExchangeStep? graph query = none := by decide +kernel

private def computedFailure : IdentificationFail signature :=
  match identifyConditionalKernel graph query with
  | .failed fail => fail
  | _ => ⟨NodeSet.empty, NodeSet.empty⟩

/-- The new conditional is actually rejected by the replacement program. -/
theorem query_failed : identifyConditionalKernel graph query = .failed computedFailure := rfl

/-- Keep the existing pair and enlarge only the queried numerator.  Equality
of its joint `R,Y` law would imply equality of its `Y` marginal, contradicting
the already checked real-SCM biased-readout separation. -/
noncomputable def jointCounterexample : CounterexampleIn (GraphModelClass.positive graph) query.jointNumerator where
  left := left
  right := right
  left_mem := ⟨left_compatible, left_positive⟩
  right_mem := ⟨right_compatible, right_positive⟩
  observationally_equal := observationally_equal
  query_separated := by
    intro equal
    have marginal := query.jointNumerator.valueEquivalent_restrictOutcome left right equal
      query.condition (NodeSet.subset_union_right query.outcome query.condition)
    exact originalCounterexample.query_separated marginal

/-- The denominator is provably unequal in these exact models.  This guards
against accidentally exercising the older matched-denominator theorem. -/
theorem denominator_not_equivalent :
    Not (query.jointDenominator.ValueEquivalent jointCounterexample.left jointCounterexample.right) :=
  originalCounterexample.query_separated

def reverseFormula : ProbabilityTerm signature :=
  match identifyConditionalKernel graph query.reverse with
  | .identified term => term
  | _ => .zero

theorem reverse_identified : identifyConditionalKernel graph query.reverse = .identified reverseFormula := rfl

/-- This common reverse conditional is established throughout the positive
compatible class by the existing success compiler, not assumed only for the
example.  The argument does not use a completeness interface. -/
theorem reverse_identifiable :
    (GraphModelClass.positive graph).conditionalIdentifiable query.reverse :=
  identifyConditionalKernel_identified_identifiable (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2) query.reverse reverse_identified

noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  ConditionalCounterexampleIn.ofJointNumeratorOfIdentifiableReverseConditional
    (C := GraphModelClass.positive graph) (fun member => member.2)
    query jointCounterexample reverse_identifiable

theorem same_left : counterexample.left = left := rfl
theorem same_right : counterexample.right = right := rfl

theorem conditional_not_identifiable :
    Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

end ConditionalReverseNormalization
end Examples
end Causality
end Thesis
