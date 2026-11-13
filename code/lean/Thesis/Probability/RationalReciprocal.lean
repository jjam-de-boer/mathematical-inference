import Thesis.Probability.RationalNorm

namespace Thesis.Probability.PositiveRatio

/-- Convert a signed rational only with a proof of strict positivity. -/
def ofSignedPositive (value : SignedRatio) (positive : 0 < value.num) : PositiveRatio :=
  ⟨value.num.toNat, value.den, by omega, value.den_pos⟩

theorem ofSignedPositive_value (value : SignedRatio) (positive : 0 < value.num) :
    SignedRatio.Equiv (ofSignedPositive value positive).toSignedRatio value := by
  have cast := Int.toNat_of_nonneg (Int.le_of_lt positive)
  simp only [SignedRatio.Equiv, ofSignedPositive, toSignedRatio, toQProb, QProb.toSignedRatio, cast]

theorem signed_magnitude (value : PositiveRatio) : QProb.Equiv value.toSignedRatio.magnitude value.toQProb := by
  simp only [QProb.Equiv, SignedRatio.magnitude, toSignedRatio, toQProb, QProb.toSignedRatio, Int.natAbs_natCast]

theorem signed_mul_inv (value : PositiveRatio) :
    SignedRatio.Equiv (SignedRatio.mul value.toSignedRatio value.inv.toSignedRatio) SignedRatio.one := by
  simp only [SignedRatio.Equiv, SignedRatio.mul, toSignedRatio, toQProb, QProb.toSignedRatio, inv,
    SignedRatio.one, Int.natCast_mul, Int.natCast_one, Int.mul_one, Int.one_mul]
  ac_rfl

/-- A positive rational lower bound gives a computable natural upper bound
on reciprocals. No normalized fraction representation is needed. -/
theorem inverse_bound (lower value : PositiveRatio) (bounded : LE lower value) :
    QProb.LE value.inv.toQProb (QProb.ofNat lower.den) := by
  apply QProb.le_trans ((inv_le_inv_iff value lower).mpr bounded)
  change lower.den * 1 ≤ lower.den * lower.num
  rw [Nat.mul_one]
  exact Nat.le_mul_of_pos_right lower.den lower.num_pos

/-- The reciprocal difference identity, before any absolute-error estimate. -/
theorem inverse_difference (a b : PositiveRatio) :
    SignedRatio.Equiv (SignedRatio.sub a.inv.toSignedRatio b.inv.toSignedRatio)
      (SignedRatio.mul (SignedRatio.sub b.toSignedRatio a.toSignedRatio)
        (SignedRatio.mul a.inv.toSignedRatio b.inv.toSignedRatio)) := by
  have left : SignedRatio.Equiv
      (SignedRatio.mul b.toSignedRatio (SignedRatio.mul a.inv.toSignedRatio b.inv.toSignedRatio)) a.inv.toSignedRatio :=
    SignedRatio.equiv_trans (SignedRatio.mul_comm _ _)
      (SignedRatio.equiv_trans (SignedRatio.mul_assoc _ _ _)
        (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
          (SignedRatio.equiv_trans (SignedRatio.mul_comm _ _) (signed_mul_inv b))) (SignedRatio.mul_one _)))
  have right : SignedRatio.Equiv
      (SignedRatio.mul a.toSignedRatio (SignedRatio.mul a.inv.toSignedRatio b.inv.toSignedRatio)) b.inv.toSignedRatio :=
    SignedRatio.equiv_trans (SignedRatio.equiv_symm (SignedRatio.mul_assoc _ _ _))
      (SignedRatio.equiv_trans (SignedRatio.mul_congr (signed_mul_inv a) (SignedRatio.equiv_refl _)) (SignedRatio.one_mul _))
  exact SignedRatio.equiv_symm (SignedRatio.equiv_trans (SignedRatio.sub_mul _ _ _)
    (SignedRatio.add_congr left (SignedRatio.neg_congr right)))

/-- Explicit reciprocal stability on a fixed positive rational half-line. -/
theorem inverse_error_bound (lower a b : PositiveRatio) (first : LE lower a) (second : LE lower b) :
    QProb.LE (SignedRatio.sub a.inv.toSignedRatio b.inv.toSignedRatio).magnitude
      (QProb.mul (SignedRatio.sub a.toSignedRatio b.toSignedRatio).magnitude (QProb.ofNat (lower.den * lower.den))) := by
  have identity := inverse_difference a b
  have sizes : QProb.LE
      (QProb.mul a.inv.toSignedRatio.magnitude b.inv.toSignedRatio.magnitude) (QProb.ofNat (lower.den * lower.den)) :=
    QProb.mul_le_mul
      (QProb.le_congr (QProb.equiv_symm (signed_magnitude _)) (QProb.equiv_refl _) (inverse_bound lower a first))
      (QProb.le_congr (QProb.equiv_symm (signed_magnitude _)) (QProb.equiv_refl _) (inverse_bound lower b second))
  have absolute := QProb.equiv_trans (SignedRatio.magnitude_congr identity)
    (QProb.equiv_trans (SignedRatio.magnitude_mul _ _)
      (QProb.mul_congr (SignedRatio.magnitude_sub_symm _ _) (SignedRatio.magnitude_mul _ _)))
  exact QProb.le_congr (QProb.equiv_symm absolute) (QProb.equiv_refl _)
    (QProb.mul_le_mul (QProb.le_refl _) sizes)

end Thesis.Probability.PositiveRatio

namespace Thesis.Probability.SignedRatio

/-- A signed rational above a supplied strictly positive rational has a
strictly positive numerator, which makes reciprocal conversion executable. -/
theorem positive_of_lower (lower : PositiveRatio) (value : SignedRatio) (bounded : LE lower.toSignedRatio value) : 0 < value.num := by
  have compared := (le_iff_cross _ _).mp bounded
  have firstPositive : 0 < (lower.num : Int) * (value.den : Int) :=
    Int.mul_pos (by have h := lower.num_pos; omega) (by have h := value.den_pos; omega)
  by_cases positive : 0 < value.num
  · exact positive
  · have negative : value.num ≤ 0 := by omega
    have impossible := Int.mul_nonpos_of_nonpos_of_nonneg negative (Int.natCast_nonneg lower.den)
    change (lower.num : Int) * (value.den : Int) ≤ value.num * (lower.den : Int) at compared
    omega

end Thesis.Probability.SignedRatio
