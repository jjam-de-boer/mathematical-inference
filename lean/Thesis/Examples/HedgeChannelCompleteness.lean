import Thesis.CausalTransport.HedgeChannelCompleteness
import Thesis.Examples.ConditionalCompilation
import Thesis.Examples.ConditionalFailureExtraction
import Thesis.Examples.ConditionalFailureFirstContact

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentHedgeChannelCompleteness

/-!
# Exercise the inhabited full package, genuine contacts, and recursive failures

These checks reuse real queries rather than introducing another disconnected
linear toy.  The outside-Small first-conditioned approach now succeeds by the
universal head/fork theorem, without its fixture-specific connected-head proof.
The failed chain with two exchanged conditioners and the irreducible nonempty-
condition chain both receive actual countermodels from the unrestricted public
failure constructor, without a matched-denominator or queried-root premise.

The successful exchange query tests the other direction: the now-inhabited
published package returns a conditional certificate from its existing semantic
identifiability proof.  Its joint and hedge fields are also exposed at their
exact original-query types.  All finite engine equations are reused from their
original regressions, so this module does not evaluate the opaque normalizer,
enumerate countermodel likelihoods, or rerun a large finite graph decision.
-/

namespace OutsideSmall

open CurrentConditionalFailureSmallPrefixDirection
open CurrentConditionalFailureFirstContact

/-- The genuine outside-Small case now uses the unconditional structural
connectivity theorem, not the earlier supplied singleton-head connection. -/
theorem actual_connection :
    actualNormal.forkOutcomeReachesSmallTest boundary approach.pivot actualForest signature.count = true :=
  approach.forkOutcomeReachesSmallTest boundary actualNormal actualForest

/-- Construct the same full-query positive countermodel class without
supplying a finite-search answer or a separate connected-head premise. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfFirstConditionedSmallApproach rich boundary approach actualNormal actualForest

end OutsideSmall

namespace Failure

open CurrentConditionalFailureExtraction

/-- Both actual recursive exchanges are handled by the public extractor
and the universal terminal family.  No empty-denominator conversion is a
regression input, even though this particular terminal has empty evidence. -/
noncomputable def twoExchangeCounterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) twoExchangeQuery :=
  graph.identifyConditionalKernel_failed_counterexample rich twoExchangeQuery two_exchanges_failed

theorem twoExchange_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable twoExchangeQuery :=
  twoExchangeCounterexample.not_identifiable

/-- A real irreducible terminal retains nonempty conditioning.  Only its
actual failed engine equation and original value-rich signature are supplied;
the older roots-in-outcome and outside-large denominator flags are not used. -/
noncomputable def irreducibleCounterexample : ConditionalCounterexampleIn (GraphModelClass.positive blockedGraph) blockedQuery :=
  blockedGraph.identifyConditionalKernel_failed_counterexample blockedRich blockedQuery blocked_conditional_failed

theorem irreducible_not_identifiable : ¬ (GraphModelClass.positive blockedGraph).conditionalIdentifiable blockedQuery :=
  irreducibleCounterexample.not_identifiable

end Failure

namespace Success

open CurrentConditionalCompilation

/-- The existing three-node exchange fixture uses the two original Bool
labels at every node.  This is alphabet data, not a completeness interface
or a semantic countermodel assumption. -/
def rich : ObservedSignature.ValueRich exchangeSignature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := by intro _; change false ∈ [false, true]; decide +kernel
  second_enumerated := by intro _; change true ∈ [false, true]; decide +kernel
  different := fun _ => Bool.false_ne_true

/-- The full record is inhabited for the actual exchange graph.  Its
conditional field is not left as an imported external theorem parameter. -/
noncomputable def published : PublishedCompleteness (GraphModelClass.positive exchangeGraph) :=
  exchangeGraph.publishedCompleteness rich

/-- Semantic identifiability of the successful exchange query now feeds
the genuine published conditional-completeness constructor. -/
noncomputable def conditionalCertificate :
    PublishedConditionalCertificate (GraphModelClass.positive exchangeGraph) exchangeGraph.dSeparationCorrectness exchangeQuery :=
  exchangeGraph.publishedConditionalCompleteness rich exchangeQuery exchange_identifiable

/-- The same full record's joint field retains its inspectable original-
query certificate type and proved separation correctness. -/
noncomputable def jointCertificate (query : JointKernelQuery exchangeSignature)
    (identifiable : (GraphModelClass.positive exchangeGraph).identifiable query) :
    PublishedJointCertificate (GraphModelClass.positive exchangeGraph) exchangeGraph.dSeparationCorrectness query :=
  published.joint_complete query identifiable

/-- The hedge field returns real models in the unchanged positive class,
not a flag that an independent countermodel family should later exist. -/
noncomputable def hedgeCounterexample (query : JointKernelQuery exchangeSignature) (w : HedgeWitness exchangeGraph query) :
    CounterexampleIn (GraphModelClass.positive exchangeGraph) query :=
  published.hedge_counterexample query w

end Success
end CurrentHedgeChannelCompleteness
end Examples
end Causality
end Thesis
