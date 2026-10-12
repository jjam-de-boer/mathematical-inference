import Thesis.CausalTransport.GuardedKernelSuccessCompilation
import Thesis.CausalTransport.HiddenDAGSoundness

namespace Thesis
namespace Causality

open Probability

/-!
# Interpret the actual guarded-ID compilation at its local boundary

The recursive success compiler constructs a path derivation and its support
tree from primitive local data.  This module interprets that construction,
first in compatible latent-root models and then in the original full hidden
DAG records.  No external soundness theorem, caller-supplied complete support
tree, canonical-collapse assertion or global positivity is needed.

The native adapters accept the compilation's data in the actual collapsed
model.  This is an explicit presentation choice, not a restriction to a
selected model class: the proved collapse preserves every displayed kernel,
term, marginal variant and zero/undefined result.  `ofCollapsed` reconstructs
the literal native support tree before native soundness is applied.  Hidden
and private-noise alphabets may have arbitrary finite sizes.

For two observationally equal models, data is requested in both models.
Unlike a purely observational overlap premise, the current local boundary
also contains demanded causal-conditional support, so no unproved automatic
transfer of all its fields is asserted.  These are support-qualified forward
identification theorems, not zero-unrestricted ID success equivalences.
-/

variable {S : ObservedSignature} {G : ObservedGraph S} {correct : DSeparationCorrectness G}

/-- Construct support from the compiled local data and apply the inhabited
path soundness package with this compilation's exact separation criterion. -/
noncomputable def PublishedLocalKernelCompilation.soundAt
    {remaining externalAction : NodeSet S}
    (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (model : ExactModel S) (compatible : Compatible model G) (reference : S.Assignment)
    (data : input.Data model reference) :
    ProbabilityTerm.EquivalentAt model
      (.kernel ⟨remaining, externalAction, NodeSet.empty⟩) input.reduction.formula reference :=
  (input.reduction.derivation.compile correct).denotational_soundAt
    ((G.publishedSoundness.pathPrimitive model compatible).compile correct)
    (input.supported model reference data)

/-- The literal formula returned by public guarded ID denotes the requested
joint intervention whenever its recursively defined local data is provided.
The observational initializer and graph closure are internal to compilation. -/
noncomputable def identifyGuardedJointKernel_soundAt
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedJointKernel G query = .identified term)
    (model : ExactModel S) (compatible : Compatible model G) (reference : S.Assignment)
    (data : (identifyGuardedJointKernelLocalCompilation G.dSeparationCorrectness query result).aligned.Data
      model reference) : ProbabilityTerm.EquivalentAt model query.sourceTerm term reference :=
  (identifyGuardedJointKernelLocalCompilation G.dSeparationCorrectness query result).aligned.soundAt
    model compatible reference data

section Native

variable {P : FiniteLatentProjection S}

/-- Reconstruct the native tree from recursively constructed collapsed
support.  The model is the actual full-DAG record, not a positive or
canonical member chosen to stand in for it. -/
noncomputable def PublishedLocalKernelCompilation.hiddenDAG_supportedAt
    {remaining externalAction : NodeSet S}
    (input : PublishedLocalKernelCompilation P.observedGraph P.observedGraph.dSeparationCorrectness
      remaining externalAction)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (data : input.Data model.toLatentRootSCM reference) :
    HiddenDAGLocalDerivationSupport model reference
      (input.reduction.derivation.compile P.observedGraph.dSeparationCorrectness) :=
  HiddenDAGLocalDerivationSupport.ofCollapsed (input.supported model.toLatentRootSCM reference data)

/-- Read this compilation's source-to-formula equality in original hidden-
DAG semantics.  No membership in the canonical projected model class is
required; projected-graph path laws supply native soundness directly. -/
noncomputable def PublishedLocalKernelCompilation.hiddenDAG_soundAt
    {remaining externalAction : NodeSet S}
    (input : PublishedLocalKernelCompilation P.observedGraph P.observedGraph.dSeparationCorrectness
      remaining externalAction)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (data : input.Data model.toLatentRootSCM reference) :
    model.TermEquivalentAt (.kernel ⟨remaining, externalAction, NodeSet.empty⟩)
      input.reduction.formula reference :=
  input.reduction.derivation.hiddenDAG_denotational_soundAt (input.hiddenDAG_supportedAt model reference data)

/-- Every successful public guarded joint expression has its original-DAG
effect value at the compiled local boundary, including supported zero values.
This interprets the actual recursive program, not a hand-written formula. -/
noncomputable def identifyGuardedJointKernel_hiddenDAG_soundAt
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedJointKernel P.observedGraph query = .identified term)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (data : (identifyGuardedJointKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result).aligned.Data
      model.toLatentRootSCM reference) : model.TermEquivalentAt query.sourceTerm term reference :=
  (identifyGuardedJointKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result).aligned.hiddenDAG_soundAt
    model reference data

/-- Compare the actual native source values through the identical compiled
action-free expression.  Both local-data arguments are explicit because
observational agreement alone need not transfer causal-support fields. -/
noncomputable def identifyGuardedJointKernel_hiddenDAG_identifiableAt
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedJointKernel P.observedGraph query = .identified term)
    (left right : FiniteHiddenDAGSCM S P) (observational : left.ObservationalAgreement right)
    (reference : S.Assignment)
    (leftData : (identifyGuardedJointKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result).aligned.Data
      left.toLatentRootSCM reference)
    (rightData : (identifyGuardedJointKernelLocalCompilation P.observedGraph.dSeparationCorrectness query result).aligned.Data
      right.toLatentRootSCM reference) :
    ProbabilityResult.Equivalent (left.termDenote query.sourceTerm reference) (right.termDenote query.sourceTerm reference) :=
  ProbabilityResult.trans (identifyGuardedJointKernel_hiddenDAG_soundAt query result left reference leftData)
    (ProbabilityResult.trans
      (FiniteHiddenDAGSCM.actionFree_invariant left right observational term
        (identifyGuardedJointKernel_identified_actionFree P.observedGraph query result) reference)
      (ProbabilityResult.symm (identifyGuardedJointKernel_hiddenDAG_soundAt query result right reference rightData)))

end Native

end Causality
end Thesis
