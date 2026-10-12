import Thesis.CausalTransport.HiddenDAGKernelCompilation
import Thesis.Examples.HiddenDAGIdentification

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGKernelCompilation

open Probability HiddenDAGCollapse

/-!
# Native local input compilation with a noncanonical collapse and zeros

Reuse the original five-node hidden relay, not its positive mechanism variant.
Its observed `Y = true` event is null and its collapse has a three-child root.
The current observational input and its `Y` marginal nevertheless have native
recursive support.  Existing native soundness interprets the actual marginal
derivation in that full-DAG model without a canonical-membership proof.

The `Y` prefix quotient is checked as well.  Its displayed denominator is
the positive `X = true` cylinder while its `Y = true` numerator is zero.
All native input subtrees are supplied by the general zero-permitting
initializer.  Only the small original fixture's denominator is numerically
checked; construction of the support trees uses the general theorems.
-/

def input : PublishedCurrentKernelReduction projection.observedGraph NodeSet.full NodeSet.empty :=
  PublishedCurrentKernelReduction.observational projection.observedGraph

noncomputable def input_supported (reference : signature.Assignment) :
    HiddenDAGLocalDerivationSupport model reference
      (input.derivation.compile projection.observedGraph.dSeparationCorrectness) :=
  PublishedCurrentKernelReduction.hiddenDAG_observational_supportedAt model reference

def yMarginal : PublishedCurrentKernelReduction projection.observedGraph
    (NodeSet.singleton y) NodeSet.empty :=
  input.marginal (NodeSet.singleton y) (NodeSet.disjoint_empty_left _)
    (fun _node _selected => rfl)

/-- The reference has zero mass for the requested outcome, but the native
unconditional marginal and its full recursive derivation remain supported. -/
noncomputable def zero_marginal_supported :
    HiddenDAGLocalDerivationSupport model HiddenDAGSoundness.reference
      (yMarginal.derivation.compile projection.observedGraph.dSeparationCorrectness) :=
  input.hiddenDAG_marginal_supportedAt (NodeSet.singleton y) (NodeSet.disjoint_empty_left _)
    (fun _node _selected => rfl) model HiddenDAGSoundness.reference
    (fun variant _listed => input_supported variant)

noncomputable def zero_marginal_sound : model.TermEquivalentAt
    (.kernel ⟨NodeSet.singleton y, NodeSet.empty, NodeSet.empty⟩)
    yMarginal.formula HiddenDAGSoundness.reference :=
  (yMarginal.derivation.compile projection.observedGraph.dSeparationCorrectness).hiddenDAG_denotational_soundAt
    zero_marginal_supported

/-- Local positivity of this displayed denominator is checked directly in
the original finite record.  The full observed law remains nonpositive. -/
def denominator_positive : ProbabilityResult.PositiveSupportedValue
    (model.termDenote
      (.marginalize (NodeSet.diff (NodeSet.full : NodeSet signature) (chainCondition NodeSet.full y))
        input.formula) HiddenDAGSoundness.reference) := by
  refine ⟨⟨1, 2, by decide⟩, .value ?_, ?_⟩
  · decide +kernel
  · decide +kernel

/-- The native prefix factor is supported from this one denominator and
the enumerated native input subtrees.  Its outcome mass may still be zero. -/
noncomputable def zero_factor_supported :
    HiddenDAGLocalDerivationSupport model HiddenDAGSoundness.reference
      ((input.factorDerivation (NodeSet.disjoint_empty_left _) y rfl).compile
        projection.observedGraph.dSeparationCorrectness) := by
  let kernel : Kernel signature :=
    ⟨NodeSet.singleton y, NodeSet.empty, chainCondition NodeSet.full y⟩
  have source := model.kernelSupportedAt_of_observational_overlap kernel HiddenDAGSoundness.reference (by
    unfold FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt
    decide +kernel)
  exact input.hiddenDAG_factor_supportedAt (NodeSet.disjoint_empty_left _) y rfl
    model HiddenDAGSoundness.reference source (fun variant _listed => input_supported variant)
    (fun variant _listed => input_supported variant) denominator_positive

/-- Native soundness interprets the constructed zero-permitting prefix
derivation, without a canonical compatibility or positive-model premise. -/
noncomputable def zero_factor_sound : model.TermEquivalentAt
    (.kernel ⟨NodeSet.singleton y, NodeSet.empty, chainCondition NodeSet.full y⟩)
    (chainFactorFrom NodeSet.full input.formula y) HiddenDAGSoundness.reference :=
  ((input.factorDerivation (NodeSet.disjoint_empty_left _) y rfl).compile
    projection.observedGraph.dSeparationCorrectness).hiddenDAG_denotational_soundAt
      zero_factor_supported

/-- The tested original full-DAG model really is outside the positive
adapter's class.  This reuses the existing concrete null-cylinder proof. -/
theorem model_is_not_positive : ¬ model.ObservationallyPositive :=
  HiddenDAGIdentification.zero_model_not_positive

end HiddenDAGKernelCompilation
end Examples
end Causality
end Thesis
