import Thesis.CausalTransport.GuardedConditionalSoundness

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}

/-!
# Interpret successful guarded programs from defined printed expressions

The uniform ID and IDC availability inductions now construct all primitive
compiler data from the actual returned observational expression.  This
module interprets those constructed trees.  Callers no longer populate the
recursive `Data`, and no complete derivation-support tree is an assumption.

Joint identification needs the printed expression to be defined.  Conditional
identification also retains the original intervened conditioner's support:
printed support alone does not imply that a requested conditional source is
meaningful.  Both supported zero outcomes and skipped null-weight factors
remain allowed.  No arbitrary value is assigned to an undefined quotient.

The original hidden-DAG adapters use the actual intervention-preserving
collapse and its proved projected graph.  They do not require pairwise-root
canonical membership, or fixed hidden/private-noise alphabet sizes.  For
observationally equal models, action-free invariance transfers printed
support; conditional source support is still requested on both sides.

This closes the data-inhabitation boundary *given printed support*.  It does
not yet prove that the paper's independently specified action and conditioning
admissibility restrictions define every successful printed expression, or
assemble the final admissible-reference completeness package.
-/

/-- Interpret the literal public joint output after constructing all its
recursive data from printed support.  The graph premise is only the actual
projection; no canonical-root or observational-positivity premise is used. -/
noncomputable def identifyGuardedJointKernel_soundAt_of_printed_support
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedJointKernel G query = .identified term)
    (model : ExactModel S) (projected : HasProjectedGraph model G) (reference : S.Assignment)
    (printedSupported : term.SupportedAt model reference) :
    ProbabilityTerm.EquivalentAt model query.sourceTerm term reference := by
  let compiled := (identifyGuardedJointKernelLocalCompilation G.dSeparationCorrectness query result).aligned
  let available := identifyGuardedJointKernelLocalCompilation_printedAvailable G.dSeparationCorrectness query result
  let data := available model projected reference printedSupported
  exact (compiled.reduction.derivation.compile G.dSeparationCorrectness).denotational_soundAt
    (model.projectedLocalPrimitiveSoundness projected G.dSeparationCorrectness)
    (compiled.supported model reference data)

/-- The analogous conditional interpretation constructs promotion and Bayes
data from the defined original and printed endpoints.  The printed numerator
may be zero; only its actual Bayes denominator must be positive. -/
noncomputable def identifyGuardedConditionalKernel_soundAt_of_printed_support
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel G query = .identified term)
    (model : ExactModel S) (projected : HasProjectedGraph model G) (reference : S.Assignment)
    (sourceSupported : query.sourceTerm.SupportedAt model reference)
    (printedSupported : term.SupportedAt model reference) :
    ProbabilityTerm.EquivalentAt model query.sourceTerm term reference := by
  let compiled := (identifyGuardedConditionalKernelLocalCompilation G.dSeparationCorrectness query result).aligned
  let available := identifyGuardedConditionalKernelLocalCompilation_printedAvailable G.dSeparationCorrectness query result
  let data := available model projected reference sourceSupported printedSupported
  exact (compiled.derivation.compile G.dSeparationCorrectness).denotational_soundAt
    (model.projectedLocalPrimitiveSoundness projected G.dSeparationCorrectness)
    (compiled.supported model reference data)

section Native

variable {P : FiniteLatentProjection S}

/-- A defined literal joint expression constructs the actual collapsed local
data and hence the full original-DAG support tree.  Native soundness reads
that constructed tree; it does not replace the model by a canonical one. -/
noncomputable def identifyGuardedJointKernel_hiddenDAG_soundAt_of_printed_support
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedJointKernel P.observedGraph query = .identified term)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (printedSupported : model.TermSupportedAt term reference) :
    model.TermEquivalentAt query.sourceTerm term reference := by
  let available := identifyGuardedJointKernelLocalCompilation_printedAvailable P.observedGraph.dSeparationCorrectness query result
  let data := available model.toLatentRootSCM
    (fun first second => model.toLatentRootSCM_projectedGraph first second) reference
    (model.termSupportedAt_to_collapsed term reference printedSupported)
  exact identifyGuardedJointKernel_hiddenDAG_soundAt query result model reference data

/-- Native conditional soundness from defined original and printed endpoints.
Only endpoint support is transported through literal collapse preservation;
the complete recursive tree is constructed by the uniform IDC proof. -/
noncomputable def identifyGuardedConditionalKernel_hiddenDAG_soundAt_of_printed_support
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel P.observedGraph query = .identified term)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (sourceSupported : model.TermSupportedAt query.sourceTerm reference)
    (printedSupported : model.TermSupportedAt term reference) :
    model.TermEquivalentAt query.sourceTerm term reference := by
  let available := identifyGuardedConditionalKernelLocalCompilation_printedAvailable P.observedGraph.dSeparationCorrectness query result
  let data := available model.toLatentRootSCM
    (fun first second => model.toLatentRootSCM_projectedGraph first second) reference
    (model.termSupportedAt_to_collapsed query.sourceTerm reference sourceSupported)
    (model.termSupportedAt_to_collapsed term reference printedSupported)
  exact identifyGuardedConditionalKernel_hiddenDAG_soundAt query result model reference data

/-- Observational agreement transfers support of the action-free returned
expression.  Constructing data separately from that support in both models
then identifies the original joint effect.  No causal data-transfer theorem
or second printed-support premise is required. -/
noncomputable def identifyGuardedJointKernel_hiddenDAG_identifiableAt_of_printed_support
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedJointKernel P.observedGraph query = .identified term)
    (left right : FiniteHiddenDAGSCM S P) (observational : left.ObservationalAgreement right)
    (reference : S.Assignment) (printedSupported : left.TermSupportedAt term reference) :
    ProbabilityResult.Equivalent (left.termDenote query.sourceTerm reference) (right.termDenote query.sourceTerm reference) := by
  let agreement := FiniteHiddenDAGSCM.actionFree_invariant left right observational term
    (identifyGuardedJointKernel_identified_actionFree P.observedGraph query result) reference
  let rightSupported : right.TermSupportedAt term reference :=
    ⟨printedSupported.1, ProbabilityResult.trans (ProbabilityResult.symm agreement) printedSupported.2⟩
  exact ProbabilityResult.trans
    (identifyGuardedJointKernel_hiddenDAG_soundAt_of_printed_support query result left reference printedSupported)
    (ProbabilityResult.trans agreement
      (ProbabilityResult.symm
        (identifyGuardedJointKernel_hiddenDAG_soundAt_of_printed_support query result right reference rightSupported)))

/-- Compare conditional values on the original query's common source support.
Only one model supplies printed support: observational invariance transfers
it to the other.  Original causal conditioner support is not inferred from
observational agreement or from the displayed formula's definition. -/
noncomputable def identifyGuardedConditionalKernel_hiddenDAG_identifiableAt_of_printed_support
    (query : ConditionalKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedConditionalKernel P.observedGraph query = .identified term)
    (left right : FiniteHiddenDAGSCM S P) (observational : left.ObservationalAgreement right)
    (reference : S.Assignment)
    (leftSource : left.TermSupportedAt query.sourceTerm reference)
    (rightSource : right.TermSupportedAt query.sourceTerm reference)
    (printedSupported : left.TermSupportedAt term reference) :
    ProbabilityResult.Equivalent (left.termDenote query.sourceTerm reference) (right.termDenote query.sourceTerm reference) := by
  let agreement := FiniteHiddenDAGSCM.actionFree_invariant left right observational term
    (identifyGuardedConditionalKernel_identified_actionFree P.observedGraph query result) reference
  let rightSupported : right.TermSupportedAt term reference :=
    ⟨printedSupported.1, ProbabilityResult.trans (ProbabilityResult.symm agreement) printedSupported.2⟩
  exact ProbabilityResult.trans
    (identifyGuardedConditionalKernel_hiddenDAG_soundAt_of_printed_support query result left reference leftSource printedSupported)
    (ProbabilityResult.trans agreement
      (ProbabilityResult.symm
        (identifyGuardedConditionalKernel_hiddenDAG_soundAt_of_printed_support query result right reference rightSource rightSupported)))

end Native

end Causality
end Thesis
