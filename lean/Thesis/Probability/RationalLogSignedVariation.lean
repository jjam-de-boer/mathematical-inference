import Thesis.Probability.RationalLogLeftVariation
import Thesis.Probability.ConstructiveRealLogarithm

namespace Thesis.Probability.RationalLogSecant
open ConstructiveReal

/-- One rational radius valid on both sides of one. Both component radii
have unit numerator, so adding their denominators gives a smaller radius. -/
def variationModulus (precision : PositiveRatio) : PositiveRatio :=
  ⟨1, (rightModulus precision).den + (leftModulus precision).den, by decide,
    Nat.add_pos_left (rightModulus precision).den_pos _⟩

private theorem variationModulus_right (precision : PositiveRatio) :
    PositiveRatio.LE (variationModulus precision) (rightModulus precision) := by
  simp only [PositiveRatio.LE, PositiveRatio.toQProb, QProb.LE, variationModulus, rightModulus, Nat.one_mul]
  omega

private theorem variationModulus_left (precision : PositiveRatio) :
    PositiveRatio.LE (variationModulus precision) (leftModulus precision) := by
  simp only [PositiveRatio.LE, PositiveRatio.toQProb, QProb.LE, variationModulus, leftModulus, Nat.one_mul]
  omega

private theorem int_gap (a b : Nat) (ordered : b ≤ a) : (a : Int) + -(b : Int) = ((a - b : Nat) : Int) := by
  have recovered := congrArg (fun n : Nat => (n : Int)) (Nat.sub_add_cancel ordered)
  simp only [Int.natCast_add] at recovered
  omega

private theorem magnitude_positive (step : PositiveRatio) :
    QProb.Equiv step.toSignedRatio.magnitude step.toQProb := by
  simp only [SignedRatio.magnitude, PositiveRatio.toSignedRatio, PositiveRatio.toQProb, QProb.toSignedRatio, Int.natAbs_natCast]
  exact QProb.equiv_refl _

private theorem rational_increment (value : PositiveRatio) :
    Equiv (sub (ofSignedRatio value.toSignedRatio) one)
      (ofSignedRatio (SignedRatio.sub value.toSignedRatio SignedRatio.one)) :=
  ofSignedRatio_sub _ _

/-- Certified first variation at one for every positive rational argument,
including values below one and exactly one. Only natural numerator/denominator
comparisons select the proof cases; real order is never decided. -/
theorem rational_variation (precision radius value : PositiveRatio)
    (small : PositiveRatio.LE radius (variationModulus precision))
    (close : QProb.LE (SignedRatio.sub value.toSignedRatio SignedRatio.one).magnitude radius.toQProb) :
    Within (QProb.mul precision.toQProb radius.toQProb) (rationalLog2 value)
      (mul (sub (ofSignedRatio value.toSignedRatio) one) limit) := by
  by_cases above : value.den < value.num
  · let step : PositiveRatio := ⟨value.num - value.den, value.den, by omega, value.den_pos⟩
    have increment : SignedRatio.Equiv (SignedRatio.sub value.toSignedRatio SignedRatio.one) step.toSignedRatio := by
      simp only [SignedRatio.Equiv, SignedRatio.sub, SignedRatio.add, SignedRatio.neg, SignedRatio.one,
        PositiveRatio.toSignedRatio, PositiveRatio.toQProb, QProb.toSignedRatio, step,
        Int.natCast_one, Int.mul_one, Int.neg_mul, Int.one_mul, Nat.mul_one]
      rw [int_gap value.num value.den (by omega)]
    have stepBound : PositiveRatio.LE step radius :=
      QProb.le_congr (QProb.equiv_trans (SignedRatio.magnitude_congr increment) (magnitude_positive step))
        (QProb.equiv_refl _) close
    have same : offsetPoint step = value := by
      apply PositiveRatio.ext
      · simp only [offsetPoint, step]
        omega
      · rfl
    have estimate := right_variation precision step
      (PositiveRatio.le_trans stepBound (PositiveRatio.le_trans small (variationModulus_right precision)))
    rw [same] at estimate
    have linear := mul_congr (equiv_trans (rational_increment value) ((ofSignedRatio_equiv_iff _ _).mpr increment)) (equiv_refl limit)
    exact (within_congr (equiv_refl _) (equiv_symm linear)).mp
      (within_mono estimate (QProb.mul_le_mul (QProb.le_refl _) stepBound))
  · by_cases below : value.num < value.den
    · let step : PositiveRatio := ⟨value.den - value.num, value.den, by omega, value.den_pos⟩
      have increment : SignedRatio.Equiv (SignedRatio.sub value.toSignedRatio SignedRatio.one) (SignedRatio.neg step.toSignedRatio) := by
        simp only [SignedRatio.Equiv, SignedRatio.sub, SignedRatio.add, SignedRatio.neg, SignedRatio.one,
          PositiveRatio.toSignedRatio, PositiveRatio.toQProb, QProb.toSignedRatio, step,
          Int.natCast_one, Int.mul_one, Int.neg_mul, Int.one_mul, Nat.mul_one]
        have opposite := int_gap value.den value.num (by omega)
        have negative : (value.num : Int) + -(value.den : Int) = -((value.den - value.num : Nat) : Int) := by omega
        rw [negative, Int.neg_mul]
      have stepBound : PositiveRatio.LE step radius :=
        QProb.le_congr (QProb.equiv_trans (SignedRatio.magnitude_congr increment)
          (QProb.equiv_trans (SignedRatio.magnitude_neg _) (magnitude_positive step))) (QProb.equiv_refl _) close
      have stepSmall := PositiveRatio.le_trans stepBound (PositiveRatio.le_trans small (variationModulus_left precision))
      let half := PositiveRatio.le_trans stepSmall (leftModulus_le_half precision)
      have same : retreat step half = value := by
        apply PositiveRatio.ext
        · simp only [retreat, step]
          omega
        · rfl
      have estimate := left_variation precision step stepSmall
      rw [same] at estimate
      have embedded : Equiv (ofSignedRatio (SignedRatio.sub value.toSignedRatio SignedRatio.one))
          (ofSignedRatio (SignedRatio.neg step.toSignedRatio)) := (ofSignedRatio_equiv_iff _ _).mpr increment
      have incReal : Equiv (sub (ofSignedRatio value.toSignedRatio) one) (neg (ofSignedRatio step.toSignedRatio)) :=
        equiv_trans (rational_increment value) (equiv_trans embedded (equiv_symm (ofSignedRatio_neg step.toSignedRatio)))
      have linear : Equiv (mul (sub (ofSignedRatio value.toSignedRatio) one) limit)
          (neg (mul (ofSignedRatio step.toSignedRatio) limit)) :=
        equiv_trans (mul_congr incReal (equiv_refl limit)) (neg_mul (ofSignedRatio step.toSignedRatio) limit)
      exact (within_congr (equiv_refl _) (equiv_symm linear)).mp
        (within_mono estimate (QProb.mul_le_mul (QProb.le_refl _) stepBound))
    · have equal : value.num = value.den := by omega
      have same : PositiveRatio.Equiv value PositiveRatio.one := by
        simp only [PositiveRatio.Equiv, PositiveRatio.toQProb, PositiveRatio.one, QProb.Equiv, Nat.mul_one, Nat.one_mul]
        exact equal
      have realSame := (ofSignedRatio_equiv_iff _ _).mpr (QProb.toSignedRatio_congr same)
      have logarithm : Equiv (rationalLog2 value) zero :=
        equiv_trans (rationalLog2_congr same) (ExactLog.interpret_ofSignedRatio SignedRatio.zero)
      have linear : Equiv (mul (sub (ofSignedRatio value.toSignedRatio) one) limit) zero :=
        equiv_trans (mul_congr ((sub_equiv_zero_iff _ _).mpr realSame) (equiv_refl limit)) (zero_mul _)
      exact (within_congr logarithm linear).mpr (within_refl _ zero)

end Thesis.Probability.RationalLogSecant
