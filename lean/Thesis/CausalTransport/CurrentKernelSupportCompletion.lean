import Thesis.CausalTransport.GuardedComponentCompilation
import Thesis.CausalTransport.Soundness

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S}
variable {remaining externalAction : NodeSet S}

/-!
# Complete current-kernel factor support without factual overlap

The old sufficient component boundary requests an observed action/predecessor
cylinder.  That cylinder can be null even when the actual causal host
conditional is supported.  The primitive endpoint constructors already avoid
that restriction; here the remaining host support is constructed from the
current input's *completed* marginal trees and the displayed positive
denominator.

The dependency order matters.  First construct the denominator marginal's
tree from the inner input trees at its actual finite variants.  Only then
interpret that completed tree using the internally proved projected-graph
soundness theorem.  Its source is the actual unconditional predecessor
probability, so the positive displayed denominator supplies positive causal
conditioning.  Finally construct the new factor tree.  Soundness of the new
factor is not assumed or used to justify its own support.

There is no global positivity, canonical pairwise-root membership, arbitrary
completion of a null conditional, or extra semantic rule.  The input trees
are exactly the recursively preceding trees, not the factor's whole tree.
Projected-graph compatibility is structural data already available for every
original hidden-DAG model.  Positive countermodel constructions and the
existing positive completeness assembler do not import this interpretation
layer or use it to establish their model positivity.

This removes a sufficient-but-unnecessary overlap premise.  It does not yet
prove that every recursive input tree or displayed denominator requested by
a whole ID/IDC program is available from the published admissibility domain.
-/

private noncomputable def projectedPrimitives (model : ExactModel S)
    (projected : HasProjectedGraph model G) (correct : DSeparationCorrectness G) :
    LocalPrimitiveSoundness G model := by
  let witnesses := PathDoRulePartitionWitnesses.ofPathProjected G model projected
  exact (PathPrimitiveSoundness.ofDoRule model G
    witnesses.toProductCrossProductLaws.toDistributionLaws.toCrossProductSoundness.toDoRule).compile correct

namespace PublishedCurrentKernelReduction

/-- A completed marginal of the current input transfers positivity from its
displayed expression to the actual causal source.  All inner support trees
are supplied before soundness is applied; the new factor's support is not
a premise.  The returned rational witness is transported constructively. -/
noncomputable def marginal_source_positiveAt
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G) (kept : NodeSet S)
    (outside : NodeSet.Disjoint externalAction remaining) (subset : NodeSet.Subset kept remaining)
    (model : ExactModel S) (projected : HasProjectedGraph model G) (reference : S.Assignment)
    (inputSupport : forall variant,
      variant ∈ ProbabilityTerm.marginalAssignments S (NodeSet.diff remaining kept) reference →
        LocalDerivationSupport model variant (input.derivation.compile correct))
    (displayedPositive : ProbabilityResult.PositiveSupportedValue
      ((ProbabilityTerm.marginalize (NodeSet.diff remaining kept) input.formula).denote model reference)) :
    ProbabilityResult.PositiveSupportedValue
      ((ProbabilityTerm.kernel ⟨kept, externalAction, NodeSet.empty⟩).denote model reference) := by
  let marginal := input.marginal kept outside subset
  let completed := input.marginal_supportedAt correct kept outside subset model reference inputSupport
  let interpreted := (marginal.derivation.compile correct).denotational_soundAt
    (projectedPrimitives model projected correct) completed
  exact ProbabilityResult.PositiveSupportedValue.transport (ProbabilityResult.symm interpreted) displayedPositive

end PublishedCurrentKernelReduction

/-- Local quotient inputs with no observed-overlap field.  Graph accuracy is
structural, the two inner tree families are exactly the quotient's demanded
finite marginals, and only its displayed denominator must be positive. -/
structure CurrentKernelFactorInputs
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G) (model : ExactModel S)
    (reference : S.Assignment) (node : Fin S.count) where
  projected : HasProjectedGraph model G
  numeratorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff remaining (NodeSet.union (NodeSet.singleton node) (chainCondition remaining node))) reference →
      LocalDerivationSupport model variant (input.derivation.compile correct)
  denominatorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff remaining (chainCondition remaining node)) reference →
      LocalDerivationSupport model variant (input.derivation.compile correct)
  denominatorPositive : ProbabilityResult.PositiveSupportedValue
    ((ProbabilityTerm.marginalize (NodeSet.diff remaining (chainCondition remaining node)) input.formula).denote
      model reference)

/-- Build the host conditional and its exact quotient tree from preceding
input data.  Positivity of the completed predecessor marginal supplies its
causal conditioner, and the ordinary factor constructor retains all finite
numerator/denominator subtrees.  Zero outcomes remain supported. -/
noncomputable def CurrentKernelFactorInputs.host_supportedAt
    {input : PublishedCurrentKernelReduction G remaining externalAction}
    {correct : DSeparationCorrectness G} {model : ExactModel S}
    {reference : S.Assignment} {node : Fin S.count}
    (data : CurrentKernelFactorInputs input correct model reference node)
    (outside : NodeSet.Disjoint externalAction remaining) (selected : remaining node = true) :
    LocalDerivationSupport model reference ((input.factorDerivation outside node selected).compile correct) := by
  have subset : NodeSet.Subset (chainCondition remaining node) remaining :=
    fun _vertex present => (Bool.and_eq_true_iff.mp present).1
  let predecessor := input.marginal_source_positiveAt correct (chainCondition remaining node) outside subset
    model data.projected reference data.denominatorInputSupport data.denominatorPositive
  let source := Kernel.supportedAt_of_positive_unconditional_conditioner model (NodeSet.singleton node)
    externalAction (chainCondition remaining node) reference predecessor
  exact input.factor_supportedAt correct outside node selected model reference source
    data.numeratorInputSupport data.denominatorInputSupport data.denominatorPositive

/-- The two existing guards retain their exact roles.  Data is requested only
on positive causal or displayed prefixes; null branches request no quotient
or inner tree.  This boundary does not assume equality of the two prefixes. -/
def CurrentKernelComponentSupportConditions
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G) (component : NodeSet S)
    (model : ExactModel S) (reference : S.Assignment) : Type :=
  forall node, component node = true →
    Sum
      (ProbabilityResult.PositiveSupportedValue ((ProbabilityTerm.kernel
        ⟨chainPrefix component node.val, componentExternalAction remaining externalAction component, NodeSet.empty⟩).denote
          model reference))
      (ProbabilityResult.PositiveSupportedValue ((guardedComponentPrefixTerm remaining input.formula component node.val
        (Nat.le_of_lt node.isLt)).denote model reference)) →
    CurrentKernelFactorInputs input correct model reference node

namespace PublishedCurrentKernelReduction

/-- Construct the same guarded prefix derivation's support from the weaker
quotient-input boundary.  Promotion and later-intervention invariance supply
both component endpoints from the newly supported host factor; no extra
component-source or factual-overlap witness is required. -/
noncomputable def guardedComponentPrefix_supportedAt_of_quotient_inputs
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true)
    (model : ExactModel S) (reference : S.Assignment)
    (conditions : CurrentKernelComponentSupportConditions input correct component model reference) :
    (n : Nat) → (bound : n ≤ S.count) → LocalDerivationSupport model reference
      ((input.guardedComponentPrefixDerivation component closed componentSubset bidirectedClosed n bound).compile
        correct) :=
  GuardedHostChain.prefix_supportedAt correct component
    (componentExternalAction remaining externalAction component)
    (NodeSet.disjoint_union_left_of
      (NodeSet.disjoint_of_subset_right closed.action_disjoint componentSubset)
      (NodeSet.disjoint_diff_right remaining component))
    (chainFactorFrom remaining input.formula)
    (fun node selected => input.componentFactorDerivation component closed componentSubset bidirectedClosed node selected)
    model reference
    (fun node selected sourcePositive => input.componentFactor_supportedAt correct component closed componentSubset
      bidirectedClosed node selected model reference
      ((conditions node selected (.inl sourcePositive)).host_supportedAt closed.action_disjoint
        (componentSubset node selected)))
    (fun node selected targetPositive =>
      ((conditions node selected (.inr targetPositive)).host_supportedAt closed.action_disjoint
        (componentSubset node selected)).endpoints.2)

/-- The full component tree is constructed under the same weaker boundary.
The probability expression and derivation are literally those of the actual
guarded engine; this changes the support constructor, not its output syntax. -/
noncomputable def guardedComponent_supportedAt_of_quotient_inputs
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true)
    (model : ExactModel S) (reference : S.Assignment)
    (conditions : CurrentKernelComponentSupportConditions input correct component model reference) :
    LocalDerivationSupport model reference
      ((input.guardedComponent component closed componentSubset bidirectedClosed).derivation.compile correct) := by
  let prefixSupport := input.guardedComponentPrefix_supportedAt_of_quotient_inputs correct component closed componentSubset
    bidirectedClosed model reference conditions S.count (Nat.le_refl _)
  let source := Kernel.unconditional_supportedAt model component
    (componentExternalAction remaining externalAction component) reference
  dsimp [guardedComponent, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  exact ⟨source, ⟨prefixSupport.endpoints.2, prefixSupport⟩⟩

end PublishedCurrentKernelReduction

end Causality
end Thesis
