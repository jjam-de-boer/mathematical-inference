import Thesis.CausalTransport.ConditionalFailureHeadConnectivity

namespace Thesis
namespace Causality

variable {S : ObservedSignature.{0}}

/-!
# Positive countermodels at every irreducible conditional terminal

This is the constructive semantic leaf.  It reuses query and provenance
types through the existing conditional modules, but its model construction
does not appeal to published soundness, correctness of an identified formula,
or positivity transported from such a formula.  A terminal has exhausted the actual observation/
action exchange search and has a hedge for its unchanged joint numerator.
The all-Small stopped-flow scan exhausts every original Small source.  If one
complete approach avoids evidence, its existing positive countermodel closes
the query.  Otherwise the scan returns the genuine conditioned boundary.

At that boundary, the hedge's actual Small action root is an available source.
Its complete stopped approach ends at its first original conditioner.  The
negative exchange answer constructs a normalized path at that literal pivot,
and the retained-pivot graph construction supplies its common cut activation
forest.  The universal head/fork connectivity argument now proves the real
incidence search succeeds and constructs the supported direction, full parity
witness, and positive countermodels for the original alphabets and full query.

No matched denominator, readiness Boolean, all-Small-conditioned assumption,
unconditioned-source choice, or independently selected normalized path remains
as a caller obligation.  All branches return actual model data.  The proof
inspects a finite computed sum, never semantic identifiability or Prop EM.
-/

/-- Every actual no-exchange terminal with a numerator hedge has positive
original-query conditional countermodels.  The hedge's stored action root
supplies a real Small source even when every Small row is conditioned; a
zero-edge first-conditioned approach is handled by the same contact theorem.
Only the original value-rich alphabet and exhausted search are supplied. -/
noncomputable def HedgeWitness.conditionalCounterexampleOfNoExchange
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (exhausted : conditionalExchangeStep? graph query = none) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  cases w.conditionalCounterexampleOrSmallFlowBoundary rich with
  | inl counterexample => exact counterexample
  | inr boundary =>
      let approach := FirstConditionedSmallApproach.ofBoundary boundary w.actionRoot w.actionRoot_in_small
      exact conditionalCounterexampleOfFirstConditionedSmallApproach rich boundary approach
        (approach.normalForm exhausted) approach.cutForest

end Causality
end Thesis
