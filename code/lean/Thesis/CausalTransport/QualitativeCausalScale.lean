import Thesis.CausalTransport.QualitativeDoCalculus
import Thesis.Causality.QualitativeCausalScale

namespace Thesis
namespace Causality

open Probability
open Probability.ClaytonWaddington
open Probability.ClaytonWaddington.UrnRatio
open QualitativeDoCalculus
open QualitativeCausalScale

/-!
Support-aware kernel comparison for the qualitative causal scale.

An induced scale's kernel plausibility is the existing 2a kernel plausibility.
This does not derive Pearl's rules from the abstract causal sentences: those
rules remain theorems of compatible finite SCMs, transported along urn
representation.  Abstract mutilated-Markov-from-axioms is Unresolved.
-/

namespace QualitativeCausalScale

theorem kernelUrnOf_induced (Q : QualitativeUrnScale) (model : ExactModel S)
    (kernel : Kernel S) (reference : S.Assignment) :
    kernelUrnOf (inducedCausal model Q) kernel reference =
      kernelUrn model kernel reference := by
  rw [kernelUrnOf, kernelUrn, inducedCausal_slice, interventionalUrn,
    Kernel.distribution_eq_interventional]
  rfl

theorem kernelRatioOf_induced (Q : QualitativeUrnScale) (model : ExactModel S)
    (kernel : Kernel S) (reference : S.Assignment)
    (hpos : 0 < (kernelUrnOf (inducedCausal model Q) kernel reference).probNum
      (kernel.conditionEvent reference)) :
    kernelRatioOf (inducedCausal model Q) kernel reference hpos =
      kernelRatio model kernel reference (by
        simpa [kernelUrnOf_induced] using hpos) := by
  simp [kernelRatioOf, kernelRatio, kernelUrnOf_induced]

theorem kernelPlausOf_eq_kernelPlaus (Q : QualitativeUrnScale)
    (model : ExactModel S) (kernel : Kernel S) (reference : S.Assignment) :
    kernelPlausOf (inducedCausal model Q) kernel reference =
      kernelPlaus Q model kernel reference := by
  by_cases hpos : 0 < (kernelUrnOf (inducedCausal model Q) kernel reference).probNum
      (kernel.conditionEvent reference)
  · have hpos' : 0 < (kernelUrn model kernel reference).probNum
        (kernel.conditionEvent reference) := by
      simpa [kernelUrnOf_induced] using hpos
    simp [kernelPlausOf, kernelPlaus, hpos, hpos']
    rw [kernelRatioOf_induced]
    rfl
  · have hpos' : ¬ (0 < (kernelUrn model kernel reference).probNum
        (kernel.conditionEvent reference)) := by
      simpa [kernelUrnOf_induced] using hpos
    simp [kernelPlausOf, kernelPlaus, hpos, hpos']
    rfl

/-- Failed support on an induced causal scale is not a completed zero. -/
theorem kernelPlausOf_undefined_not_zero_ratio (Q : QualitativeUrnScale)
    (model : ExactModel S) (kernel : Kernel S) (reference : S.Assignment)
    (hnone : kernelPlausOf (inducedCausal model Q) kernel reference = none) :
    ¬ KernelPlausEqv Q
        (kernelPlausOf (inducedCausal model Q) kernel reference)
        (some (Q.ratioPlaus ⟨1, 0, Nat.succ_pos 0, Nat.zero_le 1⟩)) := by
  rw [kernelPlausOf_eq_kernelPlaus] at hnone ⊢
  exact kernelPlaus_undefined_not_zero_ratio Q model kernel reference hnone

end QualitativeCausalScale

end Causality
end Thesis
