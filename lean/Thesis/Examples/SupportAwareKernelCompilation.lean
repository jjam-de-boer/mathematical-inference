import Thesis.CausalTransport.SupportAwareKernelCompilation
import Thesis.Examples.LocalSupportIdentification

namespace Thesis
namespace Causality
namespace Examples
namespace ZeroCellKernelCompilation

open Probability ZeroCellChain ZeroCellLocalIdentification

/-!
# Local recursive-input compilation in a genuinely nonpositive SCM

The actual model has constant `X = false` and independent unbiased `Y`.
Reuse the proved compatibility and nonpositivity facts from the local-rule
regression.  This file instead exercises the recursive input machinery:
whole-host input, a marginal with zero summands, and the engine's exact
prefix quotients with separately constructed local support trees.

At `X = true` the first quotient has a supported zero numerator and a
positive unit denominator.  At `X = false`, the second quotient has a
positive displayed prefix denominator.  At `X = true`, that same second
quotient remains undefined.  Thus the local compiler neither requires a
positive complete observed joint nor invents a null conditional value.
-/

/-- Initial syntax is obtained by the general constructor, not from a
certificate confined to the positive model class. -/
def input : PublishedCurrentKernelReduction graph NodeSet.full NodeSet.empty :=
  PublishedCurrentKernelReduction.observational graph

/-- Every observed joint cell is supported, including zero cells.  These
are explicit local values of the actual SCM; positivity is not assumed. -/
noncomputable def input_supported (variant : signature.Assignment) :
    LocalDerivationSupport model variant (input.derivation.compile graph.dSeparationCorrectness) := by
  let supported := Kernel.unconditional_supportedAt model NodeSet.full NodeSet.empty variant
  dsimp [input, PublishedCurrentKernelReduction.observational,
    PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  exact ⟨supported, ⟨supported, ()⟩⟩

/-- Marginalizing the actual whole-host expression does not require its
zero summands to become positive.  The reduction retains its exact syntax. -/
def xMarginal : PublishedCurrentKernelReduction graph (NodeSet.singleton x) NodeSet.empty :=
  input.marginal (NodeSet.singleton x) (NodeSet.disjoint_empty_left _)
    (fun _node _selected => rfl)

noncomputable def zero_marginal_supported :
    LocalDerivationSupport model reference (xMarginal.derivation.compile graph.dSeparationCorrectness) :=
  input.marginal_supportedAt graph.dSeparationCorrectness (NodeSet.singleton x)
    (NodeSet.disjoint_empty_left _) (fun _node _selected => rfl) model reference
    (fun variant _listed => input_supported variant)

/-- The first node has an empty host prefix.  This is a finite Boolean-set
identity, not a decidable-equality instance for arbitrary function types. -/
private theorem firstCondition_empty : chainCondition (NodeSet.full : NodeSet signature) x = NodeSet.empty := by
  funext node
  simp only [chainCondition, NodeSet.full, x, Bool.true_and, Nat.not_lt_zero,
    decide_false, NodeSet.empty]

/-- Read the first exact quotient's unit denominator at the impossible
outcome reference.  Only that denominator is positive; its numerator is zero. -/
def first_denominator_positive : ProbabilityResult.PositiveSupportedValue
    ((ProbabilityTerm.marginalize
      (NodeSet.diff (NodeSet.full : NodeSet signature) (chainCondition NodeSet.full x))
      input.formula).denote model reference) := by
  refine ⟨QProb.one, .value ?_, ?_⟩
  · decide +kernel
  · decide +kernel

noncomputable def firstFactor_supported :
    LocalDerivationSupport model reference
      ((input.factorDerivation (NodeSet.disjoint_empty_left _) x rfl).compile
        graph.dSeparationCorrectness) := by
  have source : (ProbabilityTerm.kernel
      ⟨NodeSet.singleton x, NodeSet.empty, chainCondition (NodeSet.full : NodeSet signature) x⟩).SupportedAt
      model reference := by
    simpa only [firstCondition_empty] using
      Kernel.unconditional_supportedAt model (NodeSet.singleton x) NodeSet.empty reference
  exact input.factor_supportedAt graph.dSeparationCorrectness (NodeSet.disjoint_empty_left _)
    x rfl model reference source (fun variant _listed => input_supported variant)
    (fun variant _listed => input_supported variant) first_denominator_positive

/-- The generic published soundness theorem interprets the constructed tree.
This does not substitute a bespoke numerical identity for the derivation. -/
noncomputable def zero_factor_sound : ProbabilityTerm.EquivalentAt model
    (.kernel ⟨NodeSet.singleton x, NodeSet.empty, chainCondition NodeSet.full x⟩)
    (chainFactorFrom NodeSet.full input.formula x) reference :=
  ((input.factorDerivation (NodeSet.disjoint_empty_left _) x rfl).compile
    graph.dSeparationCorrectness).denotational_soundAt
      (graph.publishedSoundness.primitive model compatible) firstFactor_supported

theorem first_factor_is_supported_zero :
    ((chainFactorFrom NodeSet.full input.formula x).denote model reference).map (fun value => value.num) =
      some 0 := by
  decide +kernel

/-- At the supported `X = false` reference the second displayed denominator
is positive despite zeros in the complete observational law. -/
def second_denominator_positive : ProbabilityResult.PositiveSupportedValue
    ((ProbabilityTerm.marginalize
      (NodeSet.diff (NodeSet.full : NodeSet signature) (chainCondition NodeSet.full y))
      input.formula).denote model supportedReference) := by
  refine ⟨QProb.one, .value ?_, ?_⟩
  · decide +kernel
  · decide +kernel

noncomputable def secondFactor_supported :
    LocalDerivationSupport model supportedReference
      ((input.factorDerivation (NodeSet.disjoint_empty_left _) y rfl).compile
        graph.dSeparationCorrectness) := by
  have source : (ProbabilityTerm.kernel
      ⟨NodeSet.singleton y, NodeSet.empty, chainCondition (NodeSet.full : NodeSet signature) y⟩).SupportedAt
      model supportedReference :=
    Kernel.supportedAt_of_observational_overlap model _ supportedReference (by
      unfold ObservationalCylinderPositiveAt
      decide +kernel)
  exact input.factor_supportedAt graph.dSeparationCorrectness (NodeSet.disjoint_empty_left _)
    y rfl model supportedReference source (fun variant _listed => input_supported variant)
    (fun variant _listed => input_supported variant) second_denominator_positive

/-- At the null prefix the same literal second quotient still has no value.
The local support constructor is deliberately not invoked at this reference. -/
theorem second_factor_at_null_prefix_is_undefined :
    (chainFactorFrom NodeSet.full input.formula y).denote model reference = none := by
  have checked : ((chainFactorFrom NodeSet.full input.formula y).denote model reference).isNone = true := by
    decide +kernel
  cases result : (chainFactorFrom NodeSet.full input.formula y).denote model reference with
  | none => rfl
  | some value => simp only [result, Option.isNone, Bool.false_eq_true] at checked

end ZeroCellKernelCompilation
end Examples
end Causality
end Thesis
