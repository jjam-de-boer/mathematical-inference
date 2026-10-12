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
    y y_inside model supportedReference component_supported middle_supported secondFactor_supported

/-- The existing full derivation-soundness theorem interprets the assembled
tree in the actual compatible nonpositive SCM. -/
noncomputable def sound : ProbabilityTerm.EquivalentAt model
    (.kernel ⟨NodeSet.singleton y, NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full component),
      chainCondition component y⟩) (chainFactorFrom NodeSet.full input.formula y) supportedReference :=
  (derivation.compile graph.dSeparationCorrectness).denotational_soundAt
    (graph.publishedSoundness.primitive model compatible) supported

end ZeroCellComponentCompilation
end Examples
end Causality
end Thesis
