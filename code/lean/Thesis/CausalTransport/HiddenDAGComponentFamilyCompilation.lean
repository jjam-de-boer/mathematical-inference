import Thesis.CausalTransport.GuardedComponentFamilyCompilation
import Thesis.CausalTransport.HiddenDAGSemantics

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {P : FiniteLatentProjection S}
variable {remaining externalAction : NodeSet S}

/-!
# Guarded component-family assembly in original finite hidden DAGs

The projected derivation and its guarded host-order formula are unchanged.
All local inputs below refer to the original DAG's probability records:
component conditional support, one observable predecessor cylinder, the two
finite families of native input trees, and the actual displayed denominator.
Both prefix guards also use native term denotation.  Literal term and record
preservation transport these data, including defined zeros and missing
quotients, into the already proved component-family support constructor.

The final native tree is therefore constructed, not assumed as a transfer
interface.  Arbitrary finite hidden and private-noise domains are allowed,
and collapsed roots may have many children.  Neither canonical membership
nor global observational positivity is required.  No causal soundness theorem
is used to obtain support or a positive denominator; native soundness can
interpret the resulting ordinary tree separately.
-/

/-- Primitive native data for one actually demanded component quotient.
The selected proof accesses only its actual listed component reduction.
There is no field asserting whole-host or whole-family support. -/
structure HiddenDAGComponentFamilyFactorInputs
    (family : PublishedComponentKernelReductionFamily P.observedGraph remaining externalAction)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (node : Fin S.count) (selected : remaining node = true) where
  componentSupported : model.TermSupportedAt
    (.kernel ⟨NodeSet.singleton node,
      NodeSet.union externalAction (NodeSet.diff remaining (P.observedGraph.componentAt remaining node)),
      chainCondition (P.observedGraph.componentAt remaining node) node⟩) reference
  overlap : model.ObservationalCylinderPositiveAt
    (NodeSet.union externalAction (chainCondition remaining node)) reference
  numeratorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff (P.observedGraph.componentAt remaining node)
        (NodeSet.union (NodeSet.singleton node) (chainCondition (P.observedGraph.componentAt remaining node) node))) reference →
      HiddenDAGLocalDerivationSupport model variant
        ((family.reduction (P.observedGraph.componentAt remaining node)
          (P.observedGraph.componentAt_spec remaining node selected).1).derivation.compile
          P.observedGraph.dSeparationCorrectness)
  denominatorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff (P.observedGraph.componentAt remaining node)
        (chainCondition (P.observedGraph.componentAt remaining node) node)) reference →
      HiddenDAGLocalDerivationSupport model variant
        ((family.reduction (P.observedGraph.componentAt remaining node)
          (P.observedGraph.componentAt_spec remaining node selected).1).derivation.compile
          P.observedGraph.dSeparationCorrectness)
  denominatorPositive : ProbabilityResult.PositiveSupportedValue
    (model.termDenote
      (.marginalize
        (NodeSet.diff (P.observedGraph.componentAt remaining node)
          (chainCondition (P.observedGraph.componentAt remaining node) node))
        (family.reduction (P.observedGraph.componentAt remaining node)
          (P.observedGraph.componentAt_spec remaining node selected).1).formula) reference)

/-- Preserve each supplied native value and each enumerated input subtree.
The exact observational-record identity transports the overlap test; literal
term preservation transports the one displayed positive denominator. -/
noncomputable def HiddenDAGComponentFamilyFactorInputs.toCollapsed
    {family : PublishedComponentKernelReductionFamily P.observedGraph remaining externalAction}
    {model : FiniteHiddenDAGSCM S P} {reference : S.Assignment}
    {node : Fin S.count} {selected : remaining node = true}
    (data : HiddenDAGComponentFamilyFactorInputs family model reference node selected) :
    ComponentFamilyFactorInputs family P.observedGraph.dSeparationCorrectness
      model.toLatentRootSCM reference node selected where
  componentSupported := model.termSupportedAt_to_collapsed _ reference data.componentSupported
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

/-- Both guards are native.  A null prefix does not demand that component's
conditional, denominator or input trees merely because it occurs in the
symbolic formula.  Source and displayed guards remain separate, avoiding an
assumed semantic equality or a soundness-based positivity argument. -/
def HiddenDAGComponentFamilySupportConditions
    (family : PublishedComponentKernelReductionFamily P.observedGraph remaining externalAction)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment) : Type :=
  forall node (selected : remaining node = true),
    Sum
      (ProbabilityResult.PositiveSupportedValue (model.termDenote
        (.kernel ⟨chainPrefix remaining node.val, externalAction, NodeSet.empty⟩) reference))
      (ProbabilityResult.PositiveSupportedValue (model.termDenote
        (GuardedHostChain.prefixTerm remaining family.factor node.val (Nat.le_of_lt node.isLt)) reference)) →
    HiddenDAGComponentFamilyFactorInputs family model reference node selected

/-- Translate a positive collapsed prefix back to its literal native guard
before requesting any data.  In particular the direction of the guarded
obligation is retained, rather than requiring every component in advance. -/
noncomputable def HiddenDAGComponentFamilySupportConditions.toCollapsed
    {family : PublishedComponentKernelReductionFamily P.observedGraph remaining externalAction}
    {model : FiniteHiddenDAGSCM S P} {reference : S.Assignment}
    (conditions : HiddenDAGComponentFamilySupportConditions family model reference) :
    ComponentFamilySupportConditions family P.observedGraph.dSeparationCorrectness model.toLatentRootSCM reference := by
  intro node selected branch
  cases branch with
  | inl sourcePositive =>
      have nativePositive : ProbabilityResult.PositiveSupportedValue (model.termDenote
          (.kernel ⟨chainPrefix remaining node.val, externalAction, NodeSet.empty⟩) reference) := by
        rw [model.termDenote_preserved _ reference]
        exact sourcePositive
      exact (conditions node selected (.inl nativePositive)).toCollapsed
  | inr targetPositive =>
      have nativePositive : ProbabilityResult.PositiveSupportedValue (model.termDenote
          (GuardedHostChain.prefixTerm remaining family.factor node.val (Nat.le_of_lt node.isLt)) reference) := by
        rw [model.termDenote_preserved _ reference]
        exact targetPositive
      exact (conditions node selected (.inr nativePositive)).toCollapsed

namespace PublishedComponentKernelReductionFamily

/-- Construct one actual native factor tree through the reverse graph bridge
and its component input, retaining the formula-alignment wrapper as well. -/
noncomputable def hiddenDAG_factor_supportedAt
    (family : PublishedComponentKernelReductionFamily P.observedGraph remaining externalAction)
    (closed : P.observedGraph.KernelHostClosed remaining externalAction)
    (node : Fin S.count) (selected : remaining node = true)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (data : HiddenDAGComponentFamilyFactorInputs family model reference node selected) :
    HiddenDAGLocalDerivationSupport model reference
      ((family.factorDerivation closed node selected).compile P.observedGraph.dSeparationCorrectness) :=
  .ofCollapsed (family.factor_supportedAt P.observedGraph.dSeparationCorrectness closed node selected
    model.toLatentRootSCM reference data.toCollapsed)

/-- Assemble the full native host tree from only its branch-local component
data.  Every prefix and required quotient subtree is built by the core
constructor and transported literally; no whole-host transfer law or global
regularity field is assumed for the original finite hidden-DAG model. -/
noncomputable def hiddenDAG_guardedReduction_supportedAt
    (family : PublishedComponentKernelReductionFamily P.observedGraph remaining externalAction)
    (closed : P.observedGraph.KernelHostClosed remaining externalAction)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (conditions : HiddenDAGComponentFamilySupportConditions family model reference) :
    HiddenDAGLocalDerivationSupport model reference
      ((family.guardedReduction closed).derivation.compile P.observedGraph.dSeparationCorrectness) :=
  .ofCollapsed (family.guardedReduction_supportedAt P.observedGraph.dSeparationCorrectness closed
    model.toLatentRootSCM reference conditions.toCollapsed)

end PublishedComponentKernelReductionFamily
end Causality
end Thesis
