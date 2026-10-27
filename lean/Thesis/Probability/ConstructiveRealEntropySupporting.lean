import Thesis.Probability.ConstructiveRealDyadicSegment
import Thesis.Probability.ConstructiveRealEntropyFirstVariation

namespace Thesis.Probability.ConstructiveReal

private theorem difference_add_cancel (first second : ConstructiveReal) : Equiv (add (sub first second) second) first :=
  equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _)
    (equiv_trans (add_comm _ _) (add_neg second))) (add_zero first))

/-- Midpoint concavity gives an exact lower secant bound at every dyadic
sample, with no positivity requirement on the competing endpoint. -/
theorem UnitIntervalValue.towards_entropy_lower (reference target : UnitIntervalValue) (n : Nat) :
    LE (add reference.entropy (mul (ofSignedRatio (dyadicPrecision n).toSignedRatio) (sub target.entropy reference.entropy)))
      (reference.towards target n).entropy := by
  induction n with
  | zero => exact (affine_one reference.entropy target.entropy).1
  | succ n ih =>
      have halfPositive : LE zero (ofSignedRatio (⟨1, 2, by decide⟩ : SignedRatio)) := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
      have compared := mul_le_mul_nonnegative_right halfPositive (add_le_add (le_refl reference.entropy) ih)
      have concavity := reference.entropy_midpoint_concave (reference.towards target n)
      have collected := equiv_trans (midpoint_affine reference.entropy target.entropy (ofSignedRatio (dyadicPrecision n).toSignedRatio))
        (add_congr (equiv_refl _) (mul_congr (equiv_symm (dyadicPrecision_half n)) (equiv_refl _)))
      exact (le_congr collected (equiv_refl _)).mp (le_trans compared concavity)

/-- The positive-reference entropy tangent bounds the entire closed unit
interval, including a zero competing mass. Dyadic midpoint concavity and
the proved effective derivative remainder establish the global bound; no
logarithm or sign/equality decision at the competing mass is introduced. -/
theorem UnitIntervalValue.entropy_supporting (observed reference : UnitIntervalValue) (lower : PositiveRatio)
    (positive : LE (ofSignedRatio lower.toSignedRatio) reference.value) :
    LE observed.entropy (add reference.entropy
      (mul (sub observed.value reference.value) (entropyBitGradient reference.value lower positive))) := by
  let gradient := entropyBitGradient reference.value lower positive
  have inside : entropyPositiveDomain lower.half reference.value :=
    ⟨positive_half_lower reference.value reference.value lower positive (within_refl _ _), reference.bounded⟩
  have sameGradient : Equiv (neg (add (reference.value.positiveLog2 lower.half inside.1) RationalLogSecant.limit)) gradient :=
    neg_congr (add_congr (positiveLog2_congr (equiv_refl _) lower.half lower inside.1 positive) (equiv_refl _))
  let derivative := (realEntropyTerm_hasDerivativeWithinAt reference.value lower.half inside).slope_congr sameGradient
  let directionSlope := mul (sub observed.value reference.value) gradient
  have gapBound : LE (sub observed.entropy reference.entropy) directionSlope := by
    apply le_of_forall_rational_error
    intro epsilon
    let n := (derivative.modulus epsilon).den
    let radius := dyadicPrecision n
    let sample := reference.towards observed n
    have positiveSample : LE (ofSignedRatio lower.half.toSignedRatio) sample.value :=
      reference.towards_positive observed lower positive n (derivative.modulus epsilon).den_pos
    have close := reference.towards_within observed n
    have remainder := derivative.remainder epsilon radius (dyadicPrecision_small (derivative.modulus epsilon))
      sample.value ⟨positiveSample, sample.bounded⟩ close
    have secant := reference.towards_entropy_lower observed n
    have increment : Equiv (sub sample.value reference.value)
        (mul (ofSignedRatio radius.toSignedRatio) (sub observed.value reference.value)) :=
      equiv_trans (add_congr (reference.towards_affine observed n) (equiv_refl (neg reference.value))) (add_sub_cancel _ _)
    have tangent : Equiv (mul (sub sample.value reference.value) gradient) (mul (ofSignedRatio radius.toSignedRatio) directionSlope) :=
      equiv_trans (mul_congr increment (equiv_refl _)) (mul_assoc _ _ _)
    have errorProduct : Equiv (ofSignedRatio (QProb.mul epsilon.toQProb radius.toQProb).toSignedRatio)
        (mul (ofSignedRatio radius.toSignedRatio) (ofSignedRatio epsilon.toSignedRatio)) := by
      rw [QProb.toSignedRatio_mul]
      exact equiv_trans (equiv_symm (ofSignedRatio_mul _ _)) (mul_comm _ _)
    have prediction : Equiv
        (add (add reference.entropy (mul (sub sample.value reference.value) gradient))
          (ofSignedRatio (QProb.mul epsilon.toQProb radius.toQProb).toSignedRatio))
        (add reference.entropy (mul (ofSignedRatio radius.toSignedRatio) (add directionSlope (ofSignedRatio epsilon.toSignedRatio)))) :=
      equiv_trans (add_congr (add_congr (equiv_refl _) tangent) errorProduct)
        (equiv_trans (add_assoc _ _ _) (add_congr (equiv_refl _) (equiv_symm (mul_add _ _ _))))
    have combined := (le_congr (equiv_refl _) prediction).mp (le_trans secant remainder.1)
    have canceled := (add_le_add_right_iff _ _ reference.entropy).mp
      ((le_congr (add_comm _ _) (add_comm _ _)).mp combined)
    exact (mul_le_mul_positive_iff (ofSignedRatio radius.toSignedRatio) radius (le_refl _) _ _).mp canceled
  have restored := add_le_add gapBound (le_refl reference.entropy)
  exact (le_congr (difference_add_cancel observed.entropy reference.entropy) (add_comm _ _)).mp restored

end Thesis.Probability.ConstructiveReal
