import Thesis.Causality.SupportAwareTerms
import Thesis.CausalTransport.SupportAwareProbability

namespace Thesis
namespace Causality

open Probability

/-!
# Kernel chains across zero conditioning cells

This is the first kernel-level use of the guarded expression constructor.
The whole chain is an identity in one finite SCM, with its original action
and base conditioner retained.  It is not an identification theorem and does
not replace a graph-dependent do-rule.  No global positivity, compatibility,
or externally assumed probability identity is used.

All three kernels share the same intervened distribution.  Their numerators
and conditioners are then aligned with three actual cylinder events.  Event
containment discharges the zero-middle premise of `weightedDivide_chain`.
Thus a zero middle cylinder under a supported base contributes zero, while
a zero base leaves both complete kernels undefined.  The intervened
distribution may contain arbitrary zeros.
-/

namespace ProbabilityTerm

/-- Recover `P(Y,Z | do(X),W)` by weighting `P(Y | do(X),Z,W)` with
`P(Z | do(X),W)`.  Weight order matters: the first operand is the conditioning
cell mass.  The conditional factor itself is not made defined at null cells.

The equality includes the unsupported-base case, so it does not even need
an endpoint-support hypothesis.  Disjoint query sets are required by causal
derivation constructors elsewhere; this probability identity also holds for
overlapping cylinder sets. -/
noncomputable def weightedChain_soundAt
    (model : FiniteLatentSCM S) (x y z w : NodeSet S)
    (reference : S.Assignment) :
    EquivalentAt model
      (.kernel ⟨NodeSet.union y z, x, w⟩)
      (.weightedMultiply
        (.kernel ⟨z, x, w⟩)
        (.kernel ⟨y, x, NodeSet.union z w⟩)) reference := by
  let jointKernel : Kernel S := ⟨NodeSet.union y z, x, w⟩
  let conditionalKernel : Kernel S := ⟨y, x, NodeSet.union z w⟩
  let weightKernel : Kernel S := ⟨z, x, w⟩
  let distribution := jointKernel.distribution model reference
  let jointEvent : Event S.Assignment := fun sample =>
    Kernel.agreesOn y reference sample &&
      Kernel.agreesOn z reference sample &&
      Kernel.agreesOn w reference sample
  let middleEvent : Event S.Assignment := fun sample =>
    Kernel.agreesOn z reference sample && Kernel.agreesOn w reference sample
  let baseEvent : Event S.Assignment := Kernel.agreesOn w reference
  let numerator := distribution.probVal jointEvent
  let middle := distribution.probVal middleEvent
  let base := distribution.probVal baseEvent
  have conditionalDistribution :
      conditionalKernel.distribution model reference = distribution :=
    Kernel.distribution_eq_of_action model
      y (NodeSet.union y z) x (NodeSet.union z w) w reference
  have weightDistribution :
      weightKernel.distribution model reference = distribution :=
    Kernel.distribution_eq_of_action model
      z (NodeSet.union y z) x w w reference
  have jointNumerator : QProb.Equiv
      ((jointKernel.distribution model reference).probVal
        (jointKernel.numeratorEvent reference)) numerator := by
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [jointKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have jointBase : QProb.Equiv
      ((jointKernel.distribution model reference).probVal
        (jointKernel.conditionEvent reference)) base :=
    QProb.equiv_refl _
  have conditionalNumerator : QProb.Equiv
      ((conditionalKernel.distribution model reference).probVal
        (conditionalKernel.numeratorEvent reference)) numerator := by
    rw [conditionalDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [conditionalKernel, jointEvent, Kernel.numeratorEvent,
      Kernel.agreesOn_union, Bool.and_assoc]
  have conditionalMiddle : QProb.Equiv
      ((conditionalKernel.distribution model reference).probVal
        (conditionalKernel.conditionEvent reference)) middle := by
    rw [conditionalDistribution]
    apply FiniteProbRecord.probVal_congr
    intro sample
    simp [conditionalKernel, middleEvent, Kernel.conditionEvent,
      Kernel.agreesOn_union]
  have weightMiddle : QProb.Equiv
      ((weightKernel.distribution model reference).probVal
        (weightKernel.numeratorEvent reference)) middle := by
    rw [weightDistribution]
    exact QProb.equiv_refl _
  have weightBase : QProb.Equiv
      ((weightKernel.distribution model reference).probVal
        (weightKernel.conditionEvent reference)) base := by
    rw [weightDistribution]
    exact QProb.equiv_refl _
  let jointCanonical : ProbabilityResult.Equivalent
      (jointKernel.denote model reference)
      (ProbabilityResult.divide (some numerator) (some base)) :=
    ProbabilityResult.divide_congr (.value jointNumerator) (.value jointBase)
  let weightedCanonical : ProbabilityResult.Equivalent
      (ProbabilityResult.weightedMultiply
        (weightKernel.denote model reference)
        (conditionalKernel.denote model reference))
      (ProbabilityResult.weightedMultiply
        (ProbabilityResult.divide (some middle) (some base))
        (ProbabilityResult.divide (some numerator) (some middle))) :=
    ProbabilityResult.weightedMultiply_congr
      (ProbabilityResult.divide_congr (.value weightMiddle) (.value weightBase))
      (ProbabilityResult.divide_congr
        (.value conditionalNumerator) (.value conditionalMiddle))
  have dominated : QProb.LE numerator middle :=
    Nat.mul_le_mul_right distribution.den
      (FiniteProbRecord.eventMass_mono distribution.atoms jointEvent middleEvent
        (fun _ selected => by
          exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp selected).1).2,
            (Bool.and_eq_true_iff.mp selected).2⟩))
  exact ProbabilityResult.trans jointCanonical
    (ProbabilityResult.symm (ProbabilityResult.trans weightedCanonical
      (ProbabilityResult.weightedDivide_chain_of_le numerator middle base dominated)))

end ProbabilityTerm
end Causality
end Thesis
