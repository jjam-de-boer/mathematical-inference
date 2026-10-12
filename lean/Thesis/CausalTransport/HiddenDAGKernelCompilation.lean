import Thesis.CausalTransport.SupportAwareKernelCompilation
import Thesis.CausalTransport.HiddenDAGSemantics

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {P : FiniteLatentProjection S}
variable {remaining externalAction : NodeSet S}

/-!
# Local current-kernel compilation in original finite hidden DAGs

The marginal and prefix-quotient derivations retain their original projected
graph and formula syntax.  Their local support constructors are transported
through the already proved literal native-term preservation.  Every support
value and every finite marginal variant is retained; a null denominator does
not become a value, and a supported zero numerator stays supported.

No observational positivity or canonical membership of the collapsed model
is required.  The actual full hidden-DAG model can have any finite hidden or
private-noise domains, and its collapsed roots may have many children.  This
module constructs support only: it does not use denotational soundness to
obtain a positive denominator.  The caller supplies that exact native local
denominator datum for a quotient.  Existing native soundness interprets the
resulting ordinary support tree separately.
-/

namespace PublishedCurrentKernelReduction

/-- Start the native observational input at any cell, including a zero cell.
The support datum is internally constructed, not an assumed transfer law. -/
noncomputable def hiddenDAG_observational_supportedAt
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment) :
    HiddenDAGLocalDerivationSupport model reference
      ((observational P.observedGraph).derivation.compile P.observedGraph.dSeparationCorrectness) :=
  .ofCollapsed (observational_supportedAt P.observedGraph P.observedGraph.dSeparationCorrectness
    model.toLatentRootSCM reference)

/-- Native marginal support uses exactly the native input trees at its
enumerated variants.  External intervention coordinates remain fixed and
arbitrary zero summands are permitted. -/
noncomputable def hiddenDAG_marginal_supportedAt
    (input : PublishedCurrentKernelReduction P.observedGraph remaining externalAction)
    (kept : NodeSet S) (outside : NodeSet.Disjoint externalAction remaining)
    (keptSubset : NodeSet.Subset kept remaining)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (inputSupport : forall variant,
      variant ∈ ProbabilityTerm.marginalAssignments S (NodeSet.diff remaining kept) reference →
        HiddenDAGLocalDerivationSupport model variant
          (input.derivation.compile P.observedGraph.dSeparationCorrectness)) :
    HiddenDAGLocalDerivationSupport model reference
      ((input.marginal kept outside keptSubset).derivation.compile P.observedGraph.dSeparationCorrectness) :=
  .ofCollapsed (input.marginal_supportedAt P.observedGraph.dSeparationCorrectness
    kept outside keptSubset model.toLatentRootSCM reference
    (fun variant listed => (inputSupport variant listed).toCollapsed))

/-- The exact current-input quotient's native support boundary: source
support, the two finite sets of input subtrees, and positivity of this one
displayed native denominator.  No positivity of its numerator or of the
complete observed distribution is introduced by the adapter. -/
noncomputable def hiddenDAG_factor_supportedAt
    (input : PublishedCurrentKernelReduction P.observedGraph remaining externalAction)
    (outside : NodeSet.Disjoint externalAction remaining)
    (node : Fin S.count) (selected : remaining node = true)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (sourceSupported : model.TermSupportedAt
      (.kernel ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩) reference)
    (numeratorInputSupport : forall variant,
      variant ∈ ProbabilityTerm.marginalAssignments S
        (NodeSet.diff remaining (NodeSet.union (NodeSet.singleton node)
          (chainCondition remaining node))) reference →
        HiddenDAGLocalDerivationSupport model variant
          (input.derivation.compile P.observedGraph.dSeparationCorrectness))
    (denominatorInputSupport : forall variant,
      variant ∈ ProbabilityTerm.marginalAssignments S
        (NodeSet.diff remaining (chainCondition remaining node)) reference →
        HiddenDAGLocalDerivationSupport model variant
          (input.derivation.compile P.observedGraph.dSeparationCorrectness))
    (denominatorPositive : ProbabilityResult.PositiveSupportedValue
      (model.termDenote
        (.marginalize (NodeSet.diff remaining (chainCondition remaining node)) input.formula) reference)) :
    HiddenDAGLocalDerivationSupport model reference
      ((input.factorDerivation outside node selected).compile P.observedGraph.dSeparationCorrectness) := by
  have collapsedPositive : ProbabilityResult.PositiveSupportedValue
      ((ProbabilityTerm.marginalize (NodeSet.diff remaining (chainCondition remaining node))
        input.formula).denote model.toLatentRootSCM reference) := by
    rw [model.termDenote_preserved _ reference] at denominatorPositive
    exact denominatorPositive
  exact .ofCollapsed (input.factor_supportedAt P.observedGraph.dSeparationCorrectness
    outside node selected model.toLatentRootSCM reference
    (model.termSupportedAt_to_collapsed _ reference sourceSupported)
    (fun variant listed => (numeratorInputSupport variant listed).toCollapsed)
    (fun variant listed => (denominatorInputSupport variant listed).toCollapsed)
    collapsedPositive)

end PublishedCurrentKernelReduction
end Causality
end Thesis
