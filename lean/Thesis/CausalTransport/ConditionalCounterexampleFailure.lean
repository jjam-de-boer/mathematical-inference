import Thesis.CausalTransport.ConditionalCompilation

namespace Thesis
namespace Causality

/-!
# Actual IDC failure from an independently constructed conditional countermodel

A countermodel may be established semantically without re-evaluating every
graph decision inside the proof kernel.  Soundness excludes an identified
result, and the proved termination theorem excludes `unfinished`.  Matching
the actual program output therefore returns its actual failure record.

This is the easy, constructive direction.  It assumes an already constructed
countermodel and uses neither completeness nor a failed joint numerator to
claim that such a countermodel exists.  The returned record is data from the
finite program, not a choice from a propositional failure-existence theorem.

The Boolean corollary is useful for resource-limited regressions.  It still
certifies failure of the actual IDC entry point on the actual query; it does
not check the identity of the recorded forest sets or replace a path-search
regression.  Exact fail-record and path-code computations can remain separate
from semantic countermodel checks.
-/

/-- Return the failure record of the actual conditional program.  Common
support at every cell is supplied by the selected class's observational
positivity, as in the existing soundness compiler. -/
noncomputable def ConditionalCounterexampleIn.identifyConditionalKernelFail
    {S : ObservedSignature.{0}} {graph : ObservedGraph S} {C : GraphModelClass graph}
    {query : ConditionalKernelQuery S} (counterexample : ConditionalCounterexampleIn C query)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model) :
    {fail : IdentificationFail S // identifyConditionalKernel graph query = .failed fail} := by
  cases result : identifyConditionalKernel graph query with
  | identified term =>
      exact False.elim (counterexample.not_identifiable
        (identifyConditionalKernel_identified_identifiable graph.dSeparationCorrectness obsPositive query result))
  | failed fail => exact ⟨fail, rfl⟩
  | unfinished => exact False.elim (identifyConditionalKernel_ne_unfinished graph query result)

/-- The finite failure tag of an identification outcome.  Naming this
projection lets resource-limited semantic regressions state an actual-output
check without elaborating a fresh concrete match on the whole IDC program.
It changes neither the outcome nor the meaning of failure. -/
def IdentificationOutcome.isFailed {S : ObservedSignature} : IdentificationOutcome S -> Bool
  | .failed _ => true
  | _ => false

/-- A previously proved semantic non-identifiability theorem already forces
the actual IDC entry point to report failure.  This version does not take a
countermodel structure as an argument: clients may reuse an opaque semantic
theorem without expanding a large SCM construction during kernel checking.

Only the finite program result is inspected.  There is no decision of the
semantic proposition, no selection of countermodels, and no completeness
premise.  As before, this statement does not determine the recorded forests. -/
theorem identifyConditionalKernel_failed_of_not_identifiable
    {S : ObservedSignature.{0}} {graph : ObservedGraph S} {C : GraphModelClass graph}
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : ConditionalKernelQuery S) (notIdentifiable : Not (C.conditionalIdentifiable query)) :
    (identifyConditionalKernel graph query).isFailed = true := by
  cases result : identifyConditionalKernel graph query with
  | identified term =>
      exact False.elim (notIdentifiable
        (identifyConditionalKernel_identified_identifiable graph.dSeparationCorrectness obsPositive query result))
  | failed fail => rfl
  | unfinished => exact False.elim (identifyConditionalKernel_ne_unfinished graph query result)

/-- The actual entry point reports failure, independently of how its
countermodel was constructed.  This avoids a second large decision proof
while retaining the genuine program and original-query statement. -/
theorem ConditionalCounterexampleIn.identifyConditionalKernel_failed
    {S : ObservedSignature.{0}} {graph : ObservedGraph S} {C : GraphModelClass graph}
    {query : ConditionalKernelQuery S} (counterexample : ConditionalCounterexampleIn C query)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model) :
    (match identifyConditionalKernel graph query with
      | .failed _ => true
      | _ => false) = true := by
  let failure := counterexample.identifyConditionalKernelFail obsPositive
  rw [failure.property]

end Causality
end Thesis
