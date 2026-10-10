import Thesis.CausalTransport.HedgeChannelJointCompleteness
import Thesis.CausalTransport.ConditionalFailureExtraction
import Thesis.CausalTransport.ConditionalFailureTerminalCounterexample

namespace Thesis
namespace Causality

variable {S : ObservedSignature.{0}}

/-!
# Full published constructive completeness on value-rich finite signatures

The unrestricted hedge construction supplies the joint countermodel family.
`ConditionalFailureTerminalCounterexample` supplies the universal irreducible
conditional family without using soundness for its model construction.
Here, at the one-way certificate assembly boundary, the existing extraction
and exchange transport restore every failed conditional invocation's original
query.  The same positive original-label models traverse the whole trace.

The final package inhabits all three `PublishedCompleteness` fields:
joint certificates, conditional certificates, and original-query hedge
countermodels.  Both certificate constructors inspect the engine's actual
computed result.  Success uses the literal-output do-calculus/probability
compiler; failure contradicts the supplied identifiability proof using the
constructed models; public termination excludes the unfinished alternative.
There is no excluded-middle test of identifiability or choice of a derivation
from a merely propositional existence theorem.

The model class and alphabet assumptions are explicit and unchanged:
`GraphModelClass.positive graph` on a finite `ObservedSignature.ValueRich`
signature.  This does not assert completeness for singleton-label alphabets
or arbitrary selected subclasses.  Published soundness is already supplied
for arbitrary compatible models, independently in `Soundness`.
-/

/-- Restore the original conditional countermodel pair at every recursive
exchange depth.  The actual extracted terminal supplies its exhausted search
and original-numerator hedge; no denominator comparison is assumed. -/
noncomputable def ConditionalKernelFailure.positiveCounterexample
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure graph query fail) (rich : ObservedSignature.ValueRich S) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  failure.counterexampleOfTerminal (C := GraphModelClass.positive graph) (fun member => member.2)
    (failure.hedge.witness.conditionalCounterexampleOfNoExchange rich failure.no_exchange)

/-- Every failed public conditional invocation has an actual positive
counterexample for its unchanged original query, not merely for a terminal
numerator or an auxiliary normalized event. -/
noncomputable def ObservedGraph.identifyConditionalKernel_failed_counterexample
    (graph : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S) {fail : IdentificationFail S}
    (result : identifyConditionalKernel graph query = .failed fail) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  (identifyConditionalKernelFailed query result).positiveCounterexample rich

/-- A failed conditional invocation genuinely refutes identifiability in
the same full-alphabet positive model class.  This is the universal failure
direction, with the countermodel leaf now discharged internally. -/
theorem ObservedGraph.identifyConditionalKernel_failed_not_identifiable
    (graph : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S) {fail : IdentificationFail S}
    (result : identifyConditionalKernel graph query = .failed fail) :
    ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  (graph.identifyConditionalKernel_failed_counterexample rich query result).not_identifiable

/-- The full published completeness record for every value-rich finite
observed ADMG.  Both semantic countermodel families are actual constructions;
no soundness, hedge-mix, conditional-readiness or terminal-countermodel family
is an additional argument.  The general mechanical assembler supplies the
original-query certificates with the graph's proved separation correctness. -/
noncomputable def ObservedGraph.publishedCompleteness
    (graph : ObservedGraph S) (rich : ObservedSignature.ValueRich S) :
    PublishedCompleteness (GraphModelClass.positive graph) :=
  PublishedCompleteness.ofHedgeAndConditionalTerminalCounterexamples
    (C := GraphModelClass.positive graph) (fun member => member.2)
    (fun _ witness => HedgeChannelInstallation.counterexample witness rich)
    (fun _terminal _fail exhausted _failed witness => witness.conditionalCounterexampleOfNoExchange rich exhausted)

/-- Every identifiable original conditional kernel has an inspectable
published certificate in the positive value-rich class.  The certificate
uses the actual engine output and contains its do-calculus/probability
derivation; it is not merely a proposition asserting some formula exists. -/
noncomputable def ObservedGraph.publishedConditionalCompleteness
    (graph : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S)
    (identifiable : (GraphModelClass.positive graph).conditionalIdentifiable query) :
    PublishedConditionalCertificate (GraphModelClass.positive graph) graph.dSeparationCorrectness query :=
  (graph.publishedCompleteness rich).conditional_complete query identifiable

end Causality
end Thesis
