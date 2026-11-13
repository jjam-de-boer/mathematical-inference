import Thesis.CausalTransport.CurrentKernelSupportCompletion
import Thesis.CausalTransport.GuardedComponentFamilyCompilation

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S}
variable {remaining externalAction : NodeSet S}

/-!
# Complete component-family support from the actual quotient inputs

The family fold has two different reasons to request a factor.  A positive
causal host prefix requires its whole graph-rule tree; a positive displayed
prefix requires only the displayed quotient's value.  Treating both requests
as a demand for a complete factor tree unnecessarily asks the printed branch
for causal support and factual overlap.

Here the displayed branch constructs its quotient from the finite inner
numerator trees and the positive displayed denominator.  The causal branch
gets host support directly from its actual positive predecessor probability,
then constructs the component conditional from the independently compiled
child's completed denominator marginal.  Intrinsic promotion supplies the
exchange endpoint.  The reverse graph bridge and literal family-formula
alignment build the same factor derivation as before.

Neither a host-joint identification tree nor a complete family tree is an
input.  There is no observational-overlap or component-source-support field.
All inner trees precede the new factor, and their interpretation uses the
proved projected-graph semantics rather than an extra soundness interface.
Interleaved components and both zero-prefix guards remain unchanged.
-/

/-- The actual selected component's two finite marginal families and its
one positive displayed denominator.  The projected graph is structural
compatibility, not positivity of the observed distribution. -/
structure CurrentKernelFamilyFactorInputs
    (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (correct : DSeparationCorrectness G) (model : ExactModel S) (reference : S.Assignment)
    (node : Fin S.count) (selected : remaining node = true) where
  projected : HasProjectedGraph model G
  numeratorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S (NodeSet.diff (G.componentAt remaining node)
      (NodeSet.union (NodeSet.singleton node) (chainCondition (G.componentAt remaining node) node))) reference →
      LocalDerivationSupport model variant
        ((family.reduction (G.componentAt remaining node) (G.componentAt_spec remaining node selected).1).derivation.compile
          correct)
  denominatorInputSupport : forall variant,
    variant ∈ ProbabilityTerm.marginalAssignments S
      (NodeSet.diff (G.componentAt remaining node) (chainCondition (G.componentAt remaining node) node)) reference →
      LocalDerivationSupport model variant
        ((family.reduction (G.componentAt remaining node) (G.componentAt_spec remaining node selected).1).derivation.compile
          correct)
  denominatorPositive : ProbabilityResult.PositiveSupportedValue
    ((ProbabilityTerm.marginalize
      (NodeSet.diff (G.componentAt remaining node) (chainCondition (G.componentAt remaining node) node))
      (family.reduction (G.componentAt remaining node) (G.componentAt_spec remaining node selected).1).formula).denote
        model reference)

/-- Read the selected child's quotient inputs without requesting a reduction
of the whole host.  The component lookup and membership proof are the actual
ones used by the engine, not a separately chosen component. -/
noncomputable def CurrentKernelFamilyFactorInputs.toQuotientInputs
    {family : PublishedComponentKernelReductionFamily G remaining externalAction}
    {correct : DSeparationCorrectness G} {model : ExactModel S} {reference : S.Assignment}
    {node : Fin S.count} {selected : remaining node = true}
    (data : CurrentKernelFamilyFactorInputs family correct model reference node selected) :
    CurrentKernelFactorInputs
      (family.reduction (G.componentAt remaining node) (G.componentAt_spec remaining node selected).1)
      correct model reference node where
  projected := data.projected
  numeratorInputSupport := data.numeratorInputSupport
  denominatorInputSupport := data.denominatorInputSupport
  denominatorPositive := data.denominatorPositive

namespace CurrentKernelFamilyFactorInputs

/-- A printed positive-prefix branch needs only the printed quotient.
In particular, it must not request an unrelated causal host conditioner.
The exact child expression is transported along the stored syntax equality. -/
noncomputable def target_supportedAt
    {family : PublishedComponentKernelReductionFamily G remaining externalAction}
    {correct : DSeparationCorrectness G} {model : ExactModel S} {reference : S.Assignment}
    {node : Fin S.count} {selected : remaining node = true}
    (data : CurrentKernelFamilyFactorInputs family correct model reference node selected) :
    (family.factor node).SupportedAt model reference := by
  let component := G.componentAt remaining node
  let computed := G.componentAt_spec remaining node selected
  let input := family.reduction component computed.1
  let numerator := ProbabilityTerm.marginalize_supportedAt_of_mem model
    (NodeSet.diff component (NodeSet.union (NodeSet.singleton node) (chainCondition component node)))
    input.formula reference (fun variant listed => (data.numeratorInputSupport variant listed).endpoints.2)
  let quotient : (chainFactorFrom component input.formula node).SupportedAt model reference :=
    ProbabilityResult.divide_supported_of_positive_denominator numerator data.denominatorPositive
  exact ProbabilityTerm.SupportedAt.congr
    (congrArg (fun formula => chainFactorFrom component formula node) (family.formula_eq component computed.1)) quotient

/-- The causal branch supplies its host conditioner from its prefix before
this constructor is called.  The child quotient's completed inner trees
construct the component source; promotion constructs the exchange source.
No factual-overlap or separate component-support premise is introduced. -/
noncomputable def factor_supportedAt
    {family : PublishedComponentKernelReductionFamily G remaining externalAction}
    {correct : DSeparationCorrectness G} {model : ExactModel S} {reference : S.Assignment}
    {node : Fin S.count} {selected : remaining node = true}
    (data : CurrentKernelFamilyFactorInputs family correct model reference node selected)
    (closed : G.KernelHostClosed remaining externalAction)
    (hostSupported : (ProbabilityTerm.kernel
      ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩).SupportedAt model reference) :
    LocalDerivationSupport model reference ((family.factorDerivation closed node selected).compile correct) := by
  let component := G.componentAt remaining node
  let computed := G.componentAt_spec remaining node selected
  let input := family.reduction component computed.1
  let subset := cComponents_subset G remaining computed.1
  let outside : NodeSet.Disjoint (NodeSet.union externalAction (NodeSet.diff remaining component)) component :=
    NodeSet.disjoint_union_left_of (NodeSet.disjoint_of_subset_right closed.action_disjoint subset)
      (NodeSet.disjoint_diff_right remaining component)
  let childSupport := data.toQuotientInputs.host_supportedAt outside computed.2
  let innerSupport := Causality.hostFactorOfComponentDerivation_supportedAt correct remaining externalAction component
    closed subset (G.cComponents_bidirected_closed remaining computed.1) node computed.2
    (input.factorDerivation outside node computed.2) model reference hostSupported childSupport
  let target := ProbabilityTerm.SupportedAt.congr
    (congrArg (fun formula => chainFactorFrom component formula node) (family.formula_eq component computed.1))
    innerSupport.endpoints.2
  dsimp [PublishedComponentKernelReductionFamily.factorDerivation, PathDoCalculusDerivation.compile,
    DoCalculusDerivation.mapRules]
  exact ⟨innerSupport.endpoints.1, ⟨target, innerSupport⟩⟩

end CurrentKernelFamilyFactorInputs

/-- Positive causal and printed host prefixes request the same observable
quotient inputs, but their consumers differ as explained above.  A null
prefix does not request a component or any of its inner marginal variants. -/
def CurrentKernelFamilySupportConditions
    (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (correct : DSeparationCorrectness G) (model : ExactModel S) (reference : S.Assignment) : Type :=
  forall node (selected : remaining node = true),
    Sum
      (ProbabilityResult.PositiveSupportedValue ((ProbabilityTerm.kernel
        ⟨chainPrefix remaining node.val, externalAction, NodeSet.empty⟩).denote model reference))
      (ProbabilityResult.PositiveSupportedValue
        ((GuardedHostChain.prefixTerm remaining family.factor node.val (Nat.le_of_lt node.isLt)).denote model reference)) →
    CurrentKernelFamilyFactorInputs family correct model reference node selected

/-- Assemble the same host derivation from completed child quotients.
Source-prefix positivity constructs host support intrinsically; the printed
branch only constructs the printed quotient.  This separation removes the
old extra causal-support and observational-overlap fields from recursion. -/
noncomputable def PublishedComponentKernelReductionFamily.guardedReduction_supportedAt_of_quotient_inputs
    (family : PublishedComponentKernelReductionFamily G remaining externalAction)
    (correct : DSeparationCorrectness G) (closed : G.KernelHostClosed remaining externalAction)
    (model : ExactModel S) (reference : S.Assignment)
    (conditions : CurrentKernelFamilySupportConditions family correct model reference) :
    LocalDerivationSupport model reference ((family.guardedReduction closed).derivation.compile correct) :=
  GuardedHostChain.reduction_supportedAt correct remaining externalAction closed.action_disjoint family.factor
    family.factor_actionFree (family.factorDerivation closed) model reference
    (fun node selected sourcePositive =>
      (conditions node selected (.inl sourcePositive)).factor_supportedAt closed
        (Kernel.supportedAt_of_positive_unconditional_conditioner model (NodeSet.singleton node) externalAction
          (chainCondition remaining node) reference (by simpa only [chainCondition_eq_prefix] using sourcePositive)))
    (fun node selected targetPositive => (conditions node selected (.inr targetPositive)).target_supportedAt)

end Causality
end Thesis
