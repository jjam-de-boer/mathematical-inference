import Thesis.CausalTransport.SupportAwareComponentCompilation
import Thesis.Examples.SupportAwareKernelCompilation

namespace Thesis
namespace Causality
namespace Examples
namespace ZeroCellComponentCompilation

open Probability ZeroCellChain ZeroCellLocalIdentification ZeroCellKernelCompilation

/-!
# Locally supported component extraction in a nonpositive model

Use the actual two-node edgeless model with constant `X = false` and unbiased
private `Y`.  The component is `{Y}`.  Its original factor fixes the outside
coordinate `X`; the graph-derived extraction exchanges that action for the
host predecessor observation and then uses the exact current-input quotient.

The reference selects the supported `X = false` cylinder.  The source and
exchange intermediate have constructive support, and the host quotient tree
is the one already constructed by the zero-aware kernel-input regression.
The complete observed law still has zeros.  No global positive-model class
or assumed semantic extraction identity is passed to this example.
-/

def component : NodeSet signature := NodeSet.singleton y

theorem component_subset : NodeSet.Subset component NodeSet.full :=
  fun _node _selected => rfl

theorem component_bidirected_closed : forall {source target}, component source = true →
    (NodeSet.full : NodeSet signature) target = true →
    graph.bidirected source target = true → component target = true := by
  decide +kernel

theorem y_inside : component y = true := by
  simp only [component, NodeSet.singleton, decide_true]

/-- Use the shared graph-only exchange/deletion construction, followed by
the actual current-input factor derivation, rather than a hand-written
adjustment formula or a positive-class certificate. -/
noncomputable def derivation : PathDoCalculusDerivation graph
    (.kernel ⟨NodeSet.singleton y, NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full component),
      chainCondition component y⟩) (chainFactorFrom NodeSet.full input.formula y) :=
  input.componentFactorDerivation component (ObservedGraph.KernelHostClosed.full graph)
    component_subset component_bidirected_closed y y_inside

/-- The original component factor is supported at this actual outside
action value.  Its support is constructed from observable local overlap. -/
noncomputable def component_supported : (ProbabilityTerm.kernel
    ⟨NodeSet.singleton y, NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full component),
      chainCondition component y⟩).SupportedAt model supportedReference :=
  Kernel.supportedAt_of_observational_overlap model _ supportedReference (by
    unfold ObservationalCylinderPositiveAt
    decide +kernel)

/-- The exchange intermediate uses only the host predecessor/action
cylinder.  It does not require the complete joint to become positive. -/
noncomputable def middle_supported : (ProbabilityTerm.kernel
    (rule2Left NodeSet.empty (NodeSet.singleton y)
      (NodeSet.diff (chainCondition NodeSet.full y) component) (chainCondition component y))).SupportedAt
    model supportedReference :=
  PublishedCurrentKernelReduction.componentFactor_middle_supportedAt_of_overlap
    (remaining := NodeSet.full) (externalAction := NodeSet.empty)
    model component component_subset y supportedReference (by
      unfold ObservationalCylinderPositiveAt
      decide +kernel)

/-- Assemble the ordinary recursive support tree of every actual graph rule
and prefix-quotient subtree.  The host tree includes the finite input
variants and the displayed local denominator proof, not global positivity. -/
noncomputable def supported : LocalDerivationSupport model supportedReference
    (derivation.compile graph.dSeparationCorrectness) :=
  input.componentFactor_supportedAt graph.dSeparationCorrectness component
    (ObservedGraph.KernelHostClosed.full graph) component_subset component_bidirected_closed
    y y_inside model supportedReference component_supported secondFactor_supported

/-- The existing full derivation-soundness theorem interprets the assembled
tree in the actual compatible nonpositive SCM. -/
noncomputable def sound : ProbabilityTerm.EquivalentAt model
    (.kernel ⟨NodeSet.singleton y, NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full component),
      chainCondition component y⟩) (chainFactorFrom NodeSet.full input.formula y) supportedReference :=
  (derivation.compile graph.dSeparationCorrectness).denotational_soundAt
    (graph.publishedSoundness.primitive model compatible) supported

end ZeroCellComponentCompilation

namespace ZeroCellReverseComponentCompilation

open Probability ZeroCellChain ZeroCellLocalIdentification ZeroCellKernelCompilation

/-!
# Reverse component extraction with a supported zero outcome

Identify the private component `{X}` independently under actions on its
outside host coordinate.  Rule 3 first removes that action; the existing
observational marginal reduction supplies the exact compound expression
`marginalize (V \ {X}) P(V)`.  This construction is valid at every cell even
though `X = true` is impossible.

The reverse bridge then reduces the full host's `X` factor using the prefix
quotient of this component expression.  It receives no reduction of the
whole intervened host.  Its support uses the actual component input trees,
the displayed unit denominator and observable empty-predecessor overlap.
Ordinary published soundness interprets the resulting complete tree.
-/

def component : NodeSet signature := NodeSet.singleton x

theorem component_subset : NodeSet.Subset component NodeSet.full := fun _node _inside => rfl

theorem component_bidirected_closed : forall {source target}, component source = true →
    (NodeSet.full : NodeSet signature) target = true → graph.bidirected source target = true →
    component target = true := by
  decide +kernel

theorem x_inside : component x = true := by
  simp only [component, NodeSet.singleton, decide_true]

private def action : NodeSet signature := NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full component)

private def componentQuery : JointKernelQuery signature :=
  ⟨component, action, NodeSet.disjoint_union_left_of (NodeSet.disjoint_empty_left _)
    (NodeSet.disjoint_diff_right NodeSet.full component)⟩

private theorem separated : PathSpecification.PathDSeparated graph (.bar action)
    component action NodeSet.empty :=
  graph.dSeparated_implies_pathDSeparated (.bar action) component action NodeSet.empty (by decide +kernel)

/-- The component input is an actual compound reduction.  Action deletion
and observational marginalization are explicit syntax, not assumed equalities. -/
noncomputable def componentInput : PublishedCurrentKernelReduction graph component action where
  formula := xMarginal.formula
  actionFree := xMarginal.actionFree
  derivation := DoCalculusDerivation.trans (G := graph) (separation := pathRuleSeparation graph)
    (deleteActionRule3Derivation componentQuery separated) xMarginal.derivation

/-- All component marginal variants have ordinary support, including the
impossible `X = true` variants.  Their explicit values come from unconditional
cylinders; no whole joint positivity is used. -/
noncomputable def componentInput_supported (variant : signature.Assignment) :
    LocalDerivationSupport model variant (componentInput.derivation.compile graph.dSeparationCorrectness) := by
  let sourceSupported := Kernel.unconditional_supportedAt model component action variant
  let observationalSupported := Kernel.unconditional_supportedAt model component NodeSet.empty variant
  let ruleSupported := ProbabilityTerm.SupportedAt.congr
    (JointKernelQuery.sourceTerm_eq_rule3Left_empty_xw componentQuery) sourceSupported
  let marginalSupport := input.marginal_supportedAt graph.dSeparationCorrectness (NodeSet.singleton x)
    (NodeSet.disjoint_empty_left _) (fun _node _inside => rfl) model variant
    (fun next _listed => input_supported next)
  dsimp [componentInput, deleteActionRule3Derivation, PathDoCalculusDerivation.compile,
    DoCalculusDerivation.mapRules]
  exact ⟨sourceSupported, ⟨marginalSupport.endpoints.2,
    ⟨⟨sourceSupported, ⟨observationalSupported, ⟨ruleSupported, ⟨observationalSupported, ()⟩⟩⟩⟩,
      marginalSupport⟩⟩⟩

private theorem firstCondition_empty : chainCondition component x = NodeSet.empty := by
  funext node
  simp only [chainCondition, x, Nat.not_lt_zero, decide_false, Bool.and_false, NodeSet.empty]

/-- Positivity concerns only the displayed component-prefix denominator.
The nested marginal input remains unchanged and its outcome may be zero. -/
def denominator_positive : ProbabilityResult.PositiveSupportedValue
    ((ProbabilityTerm.marginalize (NodeSet.diff component (chainCondition component x))
      componentInput.formula).denote model reference) := by
  refine ⟨QProb.one, .value ?_, ?_⟩ <;> decide +kernel

noncomputable def derivation : PathDoCalculusDerivation graph
    (.kernel ⟨NodeSet.singleton x, NodeSet.empty, chainCondition NodeSet.full x⟩)
    (chainFactorFrom component componentInput.formula x) :=
  componentInput.hostFactorOfComponentDerivation (ObservedGraph.KernelHostClosed.full graph)
    component_subset component_bidirected_closed x x_inside

/-- Build the reverse graph-rule trees and both actual finite marginal
families.  The component conditional is unconditional at this first vertex,
so its explicit causal value is supported zero at the chosen reference. -/
noncomputable def supported : LocalDerivationSupport model reference
    (derivation.compile graph.dSeparationCorrectness) := by
  have componentSupported : (ProbabilityTerm.kernel
      ⟨NodeSet.singleton x, action, chainCondition component x⟩).SupportedAt model reference := by
    simpa only [firstCondition_empty] using Kernel.unconditional_supportedAt model (NodeSet.singleton x) action reference
  exact componentInput.hostFactorOfComponent_supportedAt graph.dSeparationCorrectness
    (ObservedGraph.KernelHostClosed.full graph) component_subset component_bidirected_closed x x_inside
    model reference componentSupported (by unfold ObservationalCylinderPositiveAt; decide +kernel)
    (fun variant _listed => componentInput_supported variant)
    (fun variant _listed => componentInput_supported variant) denominator_positive

noncomputable def sound : ProbabilityTerm.EquivalentAt model
    (.kernel ⟨NodeSet.singleton x, NodeSet.empty, chainCondition NodeSet.full x⟩)
    (chainFactorFrom component componentInput.formula x) reference :=
  (derivation.compile graph.dSeparationCorrectness).denotational_soundAt
    (graph.publishedSoundness.primitive model compatible) supported

theorem reverse_quotient_is_supported_zero :
    ((chainFactorFrom component componentInput.formula x).denote model reference).map (fun value => value.num) = some 0 := by
  decide +kernel

end ZeroCellReverseComponentCompilation
end Examples
end Causality
end Thesis
