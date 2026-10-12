import Thesis.CausalTransport.GuardedComponentCompilation
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

Whole guarded components use the same boundary in the original DAG: both
prefix guards and every requested quotient datum refer to native records.
Their transport preserves the actual current expression and does not require
the collapsed roots to form a canonical pair-root model.
-/

/-! ## Native branch-local inputs for a whole guarded component -/

/-- Native data for an actually requested component quotient.  Its overlap
is one observational cylinder in the original DAG, its subtrees are native
input derivations at the two finite marginal enumerations, and its positive
denominator is the actual displayed native expression.  A zero numerator is
permitted; no whole-component support tree is assumed. -/
structure HiddenDAGGuardedComponentFactorInputs
    (input : PublishedCurrentKernelReduction P.observedGraph remaining externalAction)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (node : Fin S.count) where
  overlap : model.ObservationalCylinderPositiveAt
    (NodeSet.union externalAction (chainCondition remaining node)) reference
  numeratorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff remaining (NodeSet.union (NodeSet.singleton node)
        (chainCondition remaining node))) reference →
      HiddenDAGLocalDerivationSupport model variant
        (input.derivation.compile P.observedGraph.dSeparationCorrectness)
  denominatorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff remaining (chainCondition remaining node)) reference →
      HiddenDAGLocalDerivationSupport model variant
        (input.derivation.compile P.observedGraph.dSeparationCorrectness)
  denominatorPositive : ProbabilityResult.PositiveSupportedValue
    (model.termDenote
      (.marginalize (NodeSet.diff remaining (chainCondition remaining node)) input.formula) reference)

/-- Transport each supplied native datum literally.  The observational
record identity handles overlap, and term preservation handles the displayed
denominator; neither step invokes causal soundness to infer positivity. -/
noncomputable def HiddenDAGGuardedComponentFactorInputs.toCollapsed
    {input : PublishedCurrentKernelReduction P.observedGraph remaining externalAction}
    {model : FiniteHiddenDAGSCM S P} {reference : S.Assignment} {node : Fin S.count}
    (data : HiddenDAGGuardedComponentFactorInputs input model reference node) :
    GuardedComponentFactorInputs input P.observedGraph.dSeparationCorrectness
      model.toLatentRootSCM reference node where
  overlap := by
    change 0 < (model.toLatentRootSCM.observationalDist.probVal
      (Kernel.agreesOn (NodeSet.union externalAction (chainCondition remaining node)) reference)).num
    rw [model.toLatentRootSCM_observationalDist]
    exact data.overlap
  numeratorInputSupport := fun variant listed => (data.numeratorInputSupport variant listed).toCollapsed
  denominatorInputSupport := fun variant listed => (data.denominatorInputSupport variant listed).toCollapsed
  denominatorPositive := by
    have positive := data.denominatorPositive
    rw [model.termDenote_preserved _ reference] at positive
    exact positive

/-- Both branch tests are native: the causal component prefix and its
displayed compiled prefix.  A factor's inputs are required only when at least
one of these prefixes has positive mass.  A null branch is not assigned an
arbitrary conditional value. -/
def HiddenDAGGuardedComponentSupportConditions
    (input : PublishedCurrentKernelReduction P.observedGraph remaining externalAction)
    (component : NodeSet S) (model : FiniteHiddenDAGSCM S P)
    (reference : S.Assignment) : Type :=
  forall node, component node = true →
    Sum
      (ProbabilityResult.PositiveSupportedValue (model.termDenote
        (.kernel ⟨chainPrefix component node.val,
          componentExternalAction remaining externalAction component, NodeSet.empty⟩) reference))
      (ProbabilityResult.PositiveSupportedValue (model.termDenote
        (guardedComponentPrefixTerm remaining input.formula component node.val
          (Nat.le_of_lt node.isLt)) reference)) →
    HiddenDAGGuardedComponentFactorInputs input model reference node

/-- Translate the guards before asking for their native factor data.  This
preserves the direction of the local obligation, including skipped null
branches, rather than demanding support of every factor in advance. -/
noncomputable def HiddenDAGGuardedComponentSupportConditions.toCollapsed
    {input : PublishedCurrentKernelReduction P.observedGraph remaining externalAction}
    {component : NodeSet S} {model : FiniteHiddenDAGSCM S P} {reference : S.Assignment}
    (conditions : HiddenDAGGuardedComponentSupportConditions input component model reference) :
    GuardedComponentSupportConditions input P.observedGraph.dSeparationCorrectness component
      model.toLatentRootSCM reference := by
  intro node selected branch
  cases branch with
  | inl sourcePositive =>
      have nativePositive : ProbabilityResult.PositiveSupportedValue (model.termDenote
          (.kernel ⟨chainPrefix component node.val,
            componentExternalAction remaining externalAction component, NodeSet.empty⟩) reference) := by
        rw [model.termDenote_preserved _ reference]
        exact sourcePositive
      exact (conditions node selected (.inl nativePositive)).toCollapsed
  | inr targetPositive =>
      have nativePositive : ProbabilityResult.PositiveSupportedValue (model.termDenote
          (guardedComponentPrefixTerm remaining input.formula component node.val
            (Nat.le_of_lt node.isLt)) reference) := by
        rw [model.termDenote_preserved _ reference]
        exact targetPositive
      exact (conditions node selected (.inr nativePositive)).toCollapsed

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

/-- Assemble the whole guarded component's ordinary native support tree.
All hidden and private-noise alphabets may be finite and arbitrary, and a
collapsed root may have many observed children.  The adapter supplies no
new semantic leaf: it transports the already constructed projected tree,
with the exact original formula and the native branch-local inputs above. -/
noncomputable def hiddenDAG_guardedComponent_supportedAt
    (input : PublishedCurrentKernelReduction P.observedGraph remaining externalAction)
    (component : NodeSet S)
    (closed : P.observedGraph.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → P.observedGraph.bidirected source target = true → component target = true)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (conditions : HiddenDAGGuardedComponentSupportConditions input component model reference) :
    HiddenDAGLocalDerivationSupport model reference
      ((input.guardedComponent component closed componentSubset bidirectedClosed).derivation.compile
        P.observedGraph.dSeparationCorrectness) :=
  .ofCollapsed (input.guardedComponent_supportedAt P.observedGraph.dSeparationCorrectness
    component closed componentSubset bidirectedClosed model.toLatentRootSCM reference conditions.toCollapsed)

end PublishedCurrentKernelReduction
end Causality
end Thesis
