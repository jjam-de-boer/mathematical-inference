import Thesis.CausalTransport.GuardedConditionalSuccessCompilation
import Thesis.CausalTransport.GuardedKernelSoundness

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S} {correct : DSeparationCorrectness G}

/-!
# Local-data soundness of the actual guarded conditional program

The success compiler constructs every promoted-query rule tree and terminal
Bayes subtree.  This module applies the inhabited soundness package to that
constructed tree, then reads it in original finite hidden-DAG semantics.
The formula is the actual program output, with its literal denominator;
undefined conditioners are not given arbitrary values.

The native local data is presented through the actual, intervention-preserving
collapse.  Its full support tree is reconstructed in the original model by
`ofCollapsed`, so no canonical projected membership or global positivity is
assumed.  Arbitrary finite hidden and private-noise alphabets are allowed.

Two-model comparison deliberately requests local data on both sides.  The
conditional source and the dual causal/displayed prefix guards remain in
this raw recursive boundary; their transfer is not assumed merely because
the quotient leaves are observable.  `GuardedPrintedSoundness` instead uses
the uniform availability proof to construct data from transferred printed
support, retaining original conditional common support.  These theorems establish
support-qualified forward identification, not an unrestricted zero-class
success iff identifiability claim.
-/

/-- Interpret the constructed conditional tree with its exact compiled
graph criterion and local data, without an external soundness interface. -/
noncomputable def PublishedLocalConditionalCompilation.soundAt
    {query : ConditionalKernelQuery S} (input : PublishedLocalConditionalCompilation G correct query)
    (model : ExactModel S) (compatible : Compatible model G) (reference : S.Assignment)
    (data : input.Data model reference) : ProbabilityTerm.EquivalentAt model query.sourceTerm input.formula reference :=
  (input.derivation.compile correct).denotational_soundAt
    ((G.publishedSoundness.pathPrimitive model compatible).compile correct)
    (input.supported model reference data)

/-- The exact successful guarded IDC expression agrees with its original
conditional query whenever the recursively defined local boundary holds. -/
noncomputable def identifyGuardedConditionalKernel_soundAt
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel G query = .identified term)
    (model : ExactModel S) (compatible : Compatible model G) (reference : S.Assignment)
    (data : (identifyGuardedConditionalKernelLocalCompilation G.dSeparationCorrectness query result).aligned.Data
      model reference) : ProbabilityTerm.EquivalentAt model query.sourceTerm term reference :=
  (identifyGuardedConditionalKernelLocalCompilation G.dSeparationCorrectness query result).aligned.soundAt
    model compatible reference data

/-- A single recorded promotion needs support only of its original source.
SCM composition supplies the promoted endpoint before the actual rule-2
application is interpreted; no observational-overlap premise is introduced. -/
noncomputable def ConditionalExchangeStep.soundAt
    {query : ConditionalKernelQuery S} (step : ConditionalExchangeStep G query)
    (model : ExactModel S) (compatible : Compatible model G) (reference : S.Assignment)
    (sourceSupported : query.sourceTerm.SupportedAt model reference) :
    ProbabilityTerm.EquivalentAt model query.sourceTerm
      (query.exchangeCondition step.node step.selected).sourceTerm reference :=
  ProbabilityResult.symm ((G.publishedSoundness.pathPrimitive model compatible).doRule reference
    (step.pathRule G.dSeparationCorrectness)
    (query.exchangeCondition_supportedAt step.node step.selected model reference sourceSupported) sourceSupported)

section Native

variable {P : FiniteLatentProjection S}

/-- Original-DAG support survives a conditioner promotion even when the
factual action cylinder is null.  Literal collapse preservation transports
the intrinsic one-model composition proof; no canonical membership is used. -/
noncomputable def ConditionalKernelQuery.hiddenDAG_exchangeCondition_supportedAt
    (query : ConditionalKernelQuery S) (node : Fin S.count) (selected : query.condition node = true)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (sourceSupported : model.TermSupportedAt query.sourceTerm reference) :
    model.TermSupportedAt (query.exchangeCondition node selected).sourceTerm reference :=
  model.termSupportedAt_of_collapsed _ reference
    (query.exchangeCondition_supportedAt node selected model.toLatentRootSCM reference
      (model.termSupportedAt_to_collapsed _ reference sourceSupported))

/-- The graph-tested rule-2 leaf is sound in the actual hidden DAG whenever
the original conditional is supported.  The promoted endpoint is constructed
above, rather than requested separately or supplied by global positivity. -/
noncomputable def ConditionalExchangeStep.hiddenDAG_soundAt
    {query : ConditionalKernelQuery S} (step : ConditionalExchangeStep P.observedGraph query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (sourceSupported : model.TermSupportedAt query.sourceTerm reference) :
    model.TermEquivalentAt query.sourceTerm (query.exchangeCondition step.node step.selected).sourceTerm reference :=
  ProbabilityResult.symm (model.pathDoRule_soundAt reference
    (step.pathRule P.observedGraph.dSeparationCorrectness)
    (query.hiddenDAG_exchangeCondition_supportedAt step.node step.selected model reference sourceSupported) sourceSupported)

/-- Build the original hidden-DAG support tree from the compiled primitive
data.  This preserves every intermediate conditioner, finite marginal
variant and guarded subtree, not only the final endpoint values. -/
noncomputable def PublishedLocalConditionalCompilation.hiddenDAG_supportedAt
    {query : ConditionalKernelQuery S}
    (input : PublishedLocalConditionalCompilation P.observedGraph P.observedGraph.dSeparationCorrectness query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (data : input.Data model.toLatentRootSCM reference) :
    HiddenDAGLocalDerivationSupport model reference (input.derivation.compile P.observedGraph.dSeparationCorrectness) :=
  HiddenDAGLocalDerivationSupport.ofCollapsed (input.supported model.toLatentRootSCM reference data)

/-- Native interpretation uses the projected-graph path laws, which permit
noncanonical multi-child collapsed roots.  No model-class membership is
required beyond the actual full hidden-DAG record over this projection. -/
noncomputable def PublishedLocalConditionalCompilation.hiddenDAG_soundAt
    {query : ConditionalKernelQuery S}
    (input : PublishedLocalConditionalCompilation P.observedGraph P.observedGraph.dSeparationCorrectness query)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (data : input.Data model.toLatentRootSCM reference) :
    model.TermEquivalentAt query.sourceTerm input.formula reference :=
  input.derivation.hiddenDAG_denotational_soundAt (input.hiddenDAG_supportedAt model reference data)

/-- A successful guarded conditional program denotes its native original
query at its compiled local boundary.  Supported zero outcomes are included;
null conditional sources remain outside that boundary. -/
noncomputable def identifyGuardedConditionalKernel_hiddenDAG_soundAt
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel P.observedGraph query = .identified term)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (data : (identifyGuardedConditionalKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result).aligned.Data
      model.toLatentRootSCM reference) : model.TermEquivalentAt query.sourceTerm term reference :=
  (identifyGuardedConditionalKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result).aligned.hiddenDAG_soundAt
    model reference data

/-- Compare the native conditional values through one identical action-free
program output.  Both local boundaries are retained explicitly, rather than
deducing causal-support transfer from observational agreement alone. -/
noncomputable def identifyGuardedConditionalKernel_hiddenDAG_identifiableAt
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel P.observedGraph query = .identified term)
    (left right : FiniteHiddenDAGSCM S P) (observational : left.ObservationalAgreement right)
    (reference : S.Assignment)
    (leftData : (identifyGuardedConditionalKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result).aligned.Data
      left.toLatentRootSCM reference)
    (rightData : (identifyGuardedConditionalKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result).aligned.Data
      right.toLatentRootSCM reference) :
    ProbabilityResult.Equivalent (left.termDenote query.sourceTerm reference) (right.termDenote query.sourceTerm reference) :=
  ProbabilityResult.trans (identifyGuardedConditionalKernel_hiddenDAG_soundAt query result left reference leftData)
    (ProbabilityResult.trans
      (FiniteHiddenDAGSCM.actionFree_invariant left right observational term
        (identifyGuardedConditionalKernel_identified_actionFree P.observedGraph query result) reference)
      (ProbabilityResult.symm (identifyGuardedConditionalKernel_hiddenDAG_soundAt query result right reference rightData)))

end Native

end Causality
end Thesis
