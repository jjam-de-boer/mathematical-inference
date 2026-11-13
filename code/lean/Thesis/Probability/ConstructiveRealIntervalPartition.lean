import Thesis.Probability.ConstructiveRealDistanceScaling
import Thesis.Probability.ConstructiveRealRationalScaling

namespace Thesis.Probability.ConstructiveReal

/-- Rational partition coefficients are auxiliary arithmetic, not probability
weights of a new law. Every coefficient is constructed with a positive denominator. -/
def intervalCoefficient (parts : Nat) (positive : 0 < parts) (index : Nat) : QProb := ⟨index, parts, positive⟩

def intervalPoint (a b : ConstructiveReal) (parts : Nat) (positive : 0 < parts) (index : Nat) : ConstructiveReal :=
  add a (mul (ofSignedRatio (intervalCoefficient parts positive index).toSignedRatio) (sub b a))

private theorem add_interval_width (a b : ConstructiveReal) : Equiv (add a (sub b a)) b :=
  equiv_trans (add_comm _ _) (equiv_trans (add_assoc b (neg a) a)
    (equiv_trans (add_congr (equiv_refl _) (equiv_trans (add_comm _ _) (add_neg a))) (add_zero b)))

/-- Unit-interval endpoint bounds control the interval width without
requiring an order decision between those endpoints. -/
theorem interval_width_le_one (a b : ConstructiveReal) (nonnegativeA : LE zero a) (unitB : LE b one) :
    LE (sub b a) one := by
  have negativeA : LE (neg a) zero :=
    (le_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))).mp ((neg_le_neg_iff zero a).mpr nonnegativeA)
  exact le_trans ((le_congr (equiv_refl _) (add_zero b)).mp (add_le_add (le_refl b) negativeA)) unitB

theorem intervalPoint_zero (a b : ConstructiveReal) (parts : Nat) (positive : 0 < parts) :
    Equiv (intervalPoint a b parts positive 0) a := by
  have coefficient : Equiv (ofSignedRatio (intervalCoefficient parts positive 0).toSignedRatio) zero :=
    (ofSignedRatio_equiv_iff _ _).mpr (by simp only [SignedRatio.Equiv, intervalCoefficient, QProb.toSignedRatio, SignedRatio.zero, Int.natCast_zero, Int.zero_mul])
  exact equiv_trans (add_congr (equiv_refl _) (equiv_trans (mul_congr coefficient (equiv_refl _)) (zero_mul _))) (add_zero a)

theorem intervalPoint_last (a b : ConstructiveReal) (parts : Nat) (positive : 0 < parts) :
    Equiv (intervalPoint a b parts positive parts) b := by
  have coefficient : Equiv (ofSignedRatio (intervalCoefficient parts positive parts).toSignedRatio) one :=
    (ofSignedRatio_equiv_iff _ _).mpr (by simp only [SignedRatio.Equiv, intervalCoefficient, QProb.toSignedRatio, SignedRatio.one, Int.natCast_one, Int.mul_one, Int.one_mul])
  exact equiv_trans (add_congr (equiv_refl _) (equiv_trans (mul_congr coefficient (equiv_refl _)) (one_mul _))) (add_interval_width a b)

/-- Every enumerated partition point remains in the original closed interval. -/
theorem intervalPoint_bounds (a b : ConstructiveReal) (ordered : LE a b) (parts : Nat) (positive : 0 < parts)
    (index : Nat) (bounded : index ≤ parts) :
    LE a (intervalPoint a b parts positive index) ∧ LE (intervalPoint a b parts positive index) b := by
  let coefficient := intervalCoefficient parts positive index
  have nonnegative : LE zero (ofSignedRatio coefficient.toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le coefficient))
  have atMostOne : LE (ofSignedRatio coefficient.toSignedRatio) one :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff coefficient QProb.one).mpr
      (by simpa only [QProb.LE, QProb.one, intervalCoefficient, coefficient, Nat.one_mul, Nat.mul_one] using bounded))
  have widthNonnegative := (zero_le_sub_iff b a).mpr ordered
  have productNonnegative := mul_nonnegative nonnegative widthNonnegative
  have productUpper := (le_congr (equiv_refl _) (one_mul (sub b a))).mp
    (mul_le_mul_nonnegative_right widthNonnegative atMostOne)
  exact ⟨(le_congr (add_zero a) (equiv_refl _)).mp (add_le_add (le_refl a) productNonnegative),
    (le_congr (equiv_refl _) (add_interval_width a b)).mp (add_le_add (le_refl a) productUpper)⟩

theorem intervalPoint_next (a b : ConstructiveReal) (parts : Nat) (positive : 0 < parts) (index : Nat) :
    Equiv (intervalPoint a b parts positive (index + 1))
      (add (intervalPoint a b parts positive index)
        (mul (ofSignedRatio (intervalCoefficient parts positive 1).toSignedRatio) (sub b a))) := by
  have coefficient : Equiv (ofSignedRatio (intervalCoefficient parts positive (index + 1)).toSignedRatio)
      (add (ofSignedRatio (intervalCoefficient parts positive index).toSignedRatio) (ofSignedRatio (intervalCoefficient parts positive 1).toSignedRatio)) := by
    have rational := (QProb.toSignedRatio_equiv_iff _ _).mpr (QProb.equiv_symm (QProb.add_mk_same_den parts positive index 1))
    rw [QProb.toSignedRatio_add] at rational
    exact equiv_trans ((ofSignedRatio_equiv_iff _ _).mpr rational) (equiv_symm (ofSignedRatio_add _ _))
  exact equiv_trans (add_congr (equiv_refl a) (mul_congr coefficient (equiv_refl _)))
    (equiv_trans (add_congr (equiv_refl a) (add_mul _ _ _)) (equiv_symm (add_assoc _ _ _)))

theorem intervalPoint_increment (a b : ConstructiveReal) (parts : Nat) (positive : 0 < parts) (index : Nat) :
    Equiv (sub (intervalPoint a b parts positive (index + 1)) (intervalPoint a b parts positive index))
      (mul (ofSignedRatio (intervalCoefficient parts positive 1).toSignedRatio) (sub b a)) :=
  equiv_trans (add_congr (intervalPoint_next a b parts positive index) (equiv_refl _)) (add_sub_cancel _ _)

/-- On an interval of width at most one, each partition increment is within
the rational radius 1/parts. No comparison of the real width is decided. -/
theorem intervalPoint_within (a b : ConstructiveReal) (ordered : LE a b) (width : LE (sub b a) one)
    (parts : Nat) (positive : 0 < parts) (index : Nat) :
    Within (intervalCoefficient parts positive 1) (intervalPoint a b parts positive index) (intervalPoint a b parts positive (index + 1)) := by
  let radius := intervalCoefficient parts positive 1
  let r := ofSignedRatio radius.toSignedRatio
  let increment := mul r (sub b a)
  have radiusPositive : LE zero r :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le radius))
  have incrementPositive : LE zero increment := mul_nonnegative radiusPositive ((zero_le_sub_iff b a).mpr ordered)
  have incrementBound : LE increment r :=
    (le_congr (equiv_refl _) (mul_one r)).mp (mul_le_mul_nonnegative radiusPositive width)
  have close : Within radius increment zero :=
    ⟨(le_congr (equiv_refl _) (zero_add r)).mpr incrementBound,
      (le_congr (zero_add zero) (equiv_refl _)).mp (add_le_add incrementPositive radiusPositive)⟩
  have shifted := (within_add_left_iff radius (intervalPoint a b parts positive index) zero increment).mpr (within_symm close)
  exact (within_congr (add_zero _) (equiv_symm (intervalPoint_next a b parts positive index))).mp shifted

end Thesis.Probability.ConstructiveReal
