import Thesis.Causality.ConditionalUniqueness
import Thesis.CausalTransport.ConditionalFailureExtraction

namespace Thesis
namespace Causality

/-!
# Conditional countermodels without a matched conditioning marginal

The earlier matched-denominator adapter is sufficient when the two models
agree on `P(W | do(X))`.  A different sufficient condition is agreement on
the reverse conditional `P(W | do(X), Y)`.  Under observational positivity,
two-way conditional uniqueness shows that agreement also on the requested
`P(Y | do(X), W)` would force agreement on their joint numerator.

Consequently an existing joint countermodel with a common reverse
conditional is already a conditional countermodel, even when its
conditioning marginals differ.  The same two actual models, their class
membership, and their full observational equality are retained.  This
module neither invents a replacement pair nor assumes that a reverse
conditional is identifiable for every irreducible terminal.

The arbitrary-depth wrapper composes this terminal argument with the
existing checked exchange trace.  It adds no bounded failure unpacker and
does not change the remaining universal completeness obligations.
-/

/-- Transfer joint separation through a common reverse conditional in
the same positive countermodel pair.  Unlike the denominator adapter,
this constructor makes no assertion that the conditioning marginals agree. -/
noncomputable def ConditionalCounterexampleIn.ofJointNumeratorOfReverseConditionalEquivalent
    {S : ObservedSignature} {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S)
    (joint : CounterexampleIn C query.jointNumerator)
    (reverse : query.reverse.ValueEquivalent joint.left joint.right) :
    ConditionalCounterexampleIn C query where
  left := joint.left
  right := joint.right
  left_mem := joint.left_mem
  right_mem := joint.right_mem
  observationally_equal := joint.observationally_equal
  query_separated := fun forward => joint.query_separated
    (query.jointNumerator_valueEquivalent_of_twoWayConditionals joint.left joint.right
      (obsPositive joint.left_mem) (obsPositive joint.right_mem) forward reverse)

/-- Identifiability of the reverse conditional supplies its agreement in
the joint countermodel pair.  Only the completed success/soundness direction
is needed to establish such identifiability; no completeness interface is
used by this constructor. -/
noncomputable def ConditionalCounterexampleIn.ofJointNumeratorOfIdentifiableReverseConditional
    {S : ObservedSignature} {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S)
    (joint : CounterexampleIn C query.jointNumerator)
    (reverse : C.conditionalIdentifiable query.reverse) :
    ConditionalCounterexampleIn C query :=
  ConditionalCounterexampleIn.ofJointNumeratorOfReverseConditionalEquivalent
    obsPositive query joint (reverse joint.left joint.right joint.left_mem joint.right_mem
      joint.observationally_equal)

/-- Restore the original failed conditional at every exchange depth when
the terminal numerator's pair has a common reverse conditional.  The
reverse comparison belongs to the extracted terminal, not to a similar
query with a discarded or enlarged given-set. -/
noncomputable def ConditionalKernelFailure.counterexampleOfReverseConditionalEquivalent
    {S : ObservedSignature} {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure graph query fail)
    (joint : CounterexampleIn C failure.terminal.jointNumerator)
    (reverse : failure.terminal.reverse.ValueEquivalent joint.left joint.right) :
    ConditionalCounterexampleIn C query :=
  failure.counterexampleOfTerminal obsPositive
    (ConditionalCounterexampleIn.ofJointNumeratorOfReverseConditionalEquivalent
      obsPositive failure.terminal joint reverse)

/-- Class-level specialization of the arbitrary-depth reverse-conditional
adapter.  The supplied identifiability is for the exact irreducible terminal
reverse query; it does not assert that every reverse query is identifiable. -/
noncomputable def ConditionalKernelFailure.counterexampleOfIdentifiableReverseConditional
    {S : ObservedSignature} {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure graph query fail)
    (joint : CounterexampleIn C failure.terminal.jointNumerator)
    (reverse : C.conditionalIdentifiable failure.terminal.reverse) :
    ConditionalCounterexampleIn C query :=
  failure.counterexampleOfReverseConditionalEquivalent obsPositive joint
    (reverse joint.left joint.right joint.left_mem joint.right_mem joint.observationally_equal)

end Causality
end Thesis
