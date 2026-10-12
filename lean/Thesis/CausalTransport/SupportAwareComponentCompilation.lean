import Thesis.CausalTransport.ComponentCompilation
import Thesis.CausalTransport.SupportAwareKernelCompilation
import Thesis.Causality.ObservationalSupport

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {G : ObservedGraph S}
variable {remaining externalAction : NodeSet S}

/-!
# Component-factor extraction at explicit local support

The graph-only rule applications are shared with the established positive
compiler.  Parent closure and bidirected closure supply the same actual
rule-2 exchange and rule-3 deletion, without extra graph Booleans.  This
module composes those applications with the exact current-input prefix
derivation, independently of global observational positivity.

Support is a separate assignment-local construction.  It consumes support
of the component factor, the intervening exchange kernel and the host
factor's existing recursive tree.  No support is inferred merely because
a graph test succeeded, and no undefined conditional is completed.  A
proved observable predecessor-cylinder overlap suffices for the exchange
intermediate; it need not include the selected outcome cell.

These are factor-level ingredients for support-aware component extraction,
including unions of complete components.  They do not yet assemble a whole
guarded component product or discharge the full ID/IDC recursion.  The
ordinary derivation constructors and support tree are retained, rather than
adding an assumed semantic equality as a new rule.
-/

namespace PublishedCurrentKernelReduction

/-- Extract a component vertex's factor into the exact host-input quotient.
Later outside actions are deleted, earlier ones are exchanged for evidence,
and the unchanged host factor is reduced by its current-input derivation.
No positive-model certificate or assumed graph side condition is supplied. -/
noncomputable def componentFactorDerivation
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true)
    (node : Fin S.count) (nodeInside : component node = true) :
    PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.singleton node,
        NodeSet.union externalAction (NodeSet.diff remaining component), chainCondition component node⟩)
      (chainFactorFrom remaining input.formula node) := by
  let earlier := chainCondition component node
  let exchanged := NodeSet.diff (chainCondition remaining node) component
  let later := chainLaterOutside remaining component node
  let rules := ComponentFactorRuleApplications.ofClosed remaining externalAction component
    closed componentSubset bidirectedClosed node nodeInside
  let factor := input.factorDerivation closed.action_disjoint node (componentSubset node nodeInside)
  have hostEq : ProbabilityTerm.kernel
      (rule2Right externalAction (NodeSet.singleton node) exchanged earlier) =
      .kernel ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩ := by
    change ProbabilityTerm.kernel ⟨NodeSet.singleton node, externalAction,
      NodeSet.union exchanged earlier⟩ = _
    rw [chainCondition_outside_union_inside remaining component componentSubset node]
  let host : PathDoCalculusDerivation G
      (.kernel (rule2Right externalAction (NodeSet.singleton node) exchanged earlier))
      (chainFactorFrom remaining input.formula node) :=
    DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G) hostEq rfl factor
  let exchange := DoCalculusDerivation.trans (G := G) (separation := pathRuleSeparation G)
    (DoCalculusDerivation.doRule (G := G) (separation := pathRuleSeparation G) rules.exchange) host
  let deleted := DoCalculusDerivation.trans (G := G) (separation := pathRuleSeparation G)
    (DoCalculusDerivation.doRule (G := G) (separation := pathRuleSeparation G) rules.deletion) exchange
  have componentEq : ProbabilityTerm.kernel
      ⟨NodeSet.singleton node, NodeSet.union externalAction (NodeSet.diff remaining component), earlier⟩ =
      .kernel (rule3Left (NodeSet.union externalAction exchanged) (NodeSet.singleton node) later earlier) := by
    rw [chainOutside_eq_earlier_union_later remaining component node]
    simp only [rule3Left, NodeSet.union_assoc]
    rfl
  exact DoCalculusDerivation.eqCongr (G := G) (separation := pathRuleSeparation G)
    componentEq rfl deleted

/-- Observable support of exactly the host predecessor/action cylinder
supplies the exchange intermediate's causal conditioner.  Positivity of the
selected outcome or of later outside-component action values is not asked
for by this lemma.  It is a support fact, not a standalone identification
or whole-component coverage theorem. -/
noncomputable def componentFactor_middle_supportedAt_of_overlap
    (model : ExactModel S) (component : NodeSet S)
    (componentSubset : NodeSet.Subset component remaining)
    (node : Fin S.count) (reference : S.Assignment)
    (overlap : ObservationalCylinderPositiveAt model
      (NodeSet.union externalAction (chainCondition remaining node)) reference) :
    (ProbabilityTerm.kernel
      (rule2Left externalAction (NodeSet.singleton node)
        (NodeSet.diff (chainCondition remaining node) component) (chainCondition component node))).SupportedAt
      model reference := by
  apply Kernel.supportedAt_of_observational_overlap
  change ObservationalCylinderPositiveAt model
    (NodeSet.union (NodeSet.union externalAction (NodeSet.diff (chainCondition remaining node) component))
      (chainCondition component node)) reference
  rw [NodeSet.union_assoc,
    chainCondition_outside_union_inside remaining component componentSubset node]
  exact overlap

/-- Construct every endpoint and subtree of the extracted factor at this
reference.  The host tree contains its finite marginal subtrees and local
quotient denominator proof already; only the two preceding graph-rule
endpoint supports are added here.  Every supported value may have a zero
numerator.  No denotational soundness is used to manufacture support. -/
noncomputable def componentFactor_supportedAt
    (input : PublishedCurrentKernelReduction G remaining externalAction)
    (correct : DSeparationCorrectness G)
    (component : NodeSet S) (closed : G.KernelHostClosed remaining externalAction)
    (componentSubset : NodeSet.Subset component remaining)
    (bidirectedClosed : forall {source target}, component source = true →
      remaining target = true → G.bidirected source target = true → component target = true)
    (node : Fin S.count) (nodeInside : component node = true)
    (model : ExactModel S) (reference : S.Assignment)
    (componentSupported : (ProbabilityTerm.kernel
      ⟨NodeSet.singleton node, NodeSet.union externalAction (NodeSet.diff remaining component),
        chainCondition component node⟩).SupportedAt model reference)
    (middleSupported : (ProbabilityTerm.kernel
      (rule2Left externalAction (NodeSet.singleton node)
        (NodeSet.diff (chainCondition remaining node) component) (chainCondition component node))).SupportedAt
      model reference)
    (hostSupport : LocalDerivationSupport model reference
      ((input.factorDerivation closed.action_disjoint node (componentSubset node nodeInside)).compile correct)) :
    LocalDerivationSupport model reference
      ((input.componentFactorDerivation component closed componentSubset bidirectedClosed node nodeInside).compile
        correct) := by
  let earlier := chainCondition component node
  let exchanged := NodeSet.diff (chainCondition remaining node) component
  let later := chainLaterOutside remaining component node
  have hostEq : ProbabilityTerm.kernel
      (rule2Right externalAction (NodeSet.singleton node) exchanged earlier) =
      .kernel ⟨NodeSet.singleton node, externalAction, chainCondition remaining node⟩ := by
    change ProbabilityTerm.kernel ⟨NodeSet.singleton node, externalAction,
      NodeSet.union exchanged earlier⟩ = _
    rw [chainCondition_outside_union_inside remaining component componentSubset node]
  have componentEq : ProbabilityTerm.kernel
      ⟨NodeSet.singleton node, NodeSet.union externalAction (NodeSet.diff remaining component), earlier⟩ =
      .kernel (rule3Left (NodeSet.union externalAction exchanged) (NodeSet.singleton node) later earlier) := by
    rw [chainOutside_eq_earlier_union_later remaining component node]
    simp only [rule3Left, NodeSet.union_assoc]
    rfl
  let hostSource := ProbabilityTerm.SupportedAt.congr hostEq.symm hostSupport.endpoints.1
  let deletionSource := ProbabilityTerm.SupportedAt.congr componentEq componentSupported
  let targetSupported := hostSupport.endpoints.2
  dsimp [componentFactorDerivation, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  exact ⟨componentSupported, ⟨targetSupported,
    ⟨deletionSource, ⟨targetSupported,
      ⟨⟨deletionSource, ⟨middleSupported, ()⟩⟩,
        ⟨middleSupported, ⟨targetSupported,
          ⟨⟨middleSupported, ⟨hostSource, ()⟩⟩,
            ⟨hostSource, ⟨targetSupported, hostSupport⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end PublishedCurrentKernelReduction
end Causality
end Thesis
