import Thesis.Probability.ConstructiveRealRing
import Thesis.Probability.ConstructiveRealScaling

namespace Thesis.Probability.SignedRatio

/-- Division by a positive natural cannot increase an absolute difference. -/
theorem divideNat_error_le (a b : SignedRatio) (n : Nat) (positive : 0 < n) :
    QProb.LE (sub (divideNat a n positive) (divideNat b n positive)).magnitude (sub a b).magnitude := by
  have same : Equiv (divideNat (sub a b) n positive) (sub (divideNat a n positive) (divideNat b n positive)) :=
    divideNat_add a (neg b) n positive
  have contracted : QProb.LE (divideNat (sub a b) n positive).magnitude (sub a b).magnitude := by
    change (sub a b).num.natAbs * (sub a b).den ≤ (sub a b).num.natAbs * ((sub a b).den * n)
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_right ((sub a b).num.natAbs * (sub a b).den) positive
  exact QProb.le_congr (magnitude_congr same) (QProb.equiv_refl _) contracted

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.ConstructiveReal

/-- The earlier repeated-addition scalar action agrees with real products. -/
theorem scaleNat_mul (n : Nat) (x : ConstructiveReal) :
    Equiv (scaleNat n x) (mul (ofSignedRatio (QProb.ofNat n).toSignedRatio) x) := by
  induction n with
  | zero => exact equiv_symm (zero_mul x)
  | succ n ih =>
      have raised : Equiv (add (ofSignedRatio (QProb.ofNat n).toSignedRatio) one)
          (ofSignedRatio (QProb.ofNat (n + 1)).toSignedRatio) := by
        apply equiv_trans (ofSignedRatio_add _ _)
        apply (ofSignedRatio_equiv_iff _ _).mpr
        simp only [SignedRatio.Equiv, SignedRatio.add, QProb.ofNat, QProb.toSignedRatio,
          SignedRatio.one, Nat.mul_one, Int.natCast_one, Int.mul_one, Int.natCast_add]
      exact equiv_trans (add_congr ih (equiv_symm (one_mul x)))
        (equiv_trans (equiv_symm (add_mul _ _ _)) (mul_congr raised (equiv_refl _)))

/-- Natural division agrees with multiplication by its exact rational
reciprocal. This is an identity for every real presentation. -/
theorem divideNat_mul (x : ConstructiveReal) (n : Nat) (positive : 0 < n) :
    Equiv (divideNat x n positive) (mul x (ofSignedRatio (QProb.toSignedRatio ⟨1, n, positive⟩))) := by
  let reciprocal := ofSignedRatio (QProb.toSignedRatio ⟨1, n, positive⟩)
  have products : Equiv (mul x reciprocal) (divideNat x n positive).rationalApproximation.limit := by
    apply RegularRationalApproximation.limit_equiv_of_error_bound _ _ n
    intro left right
    let selected := RegularRationalApproximation.productPrecision x.rationalApproximation reciprocal.rationalApproximation left
    let refined := right.mul (PositiveRatio.ofNat n positive)
    have productSame : SignedRatio.Equiv
        (SignedRatio.mul (x.rationalApproximation.value selected) (QProb.toSignedRatio ⟨1, n, positive⟩))
        (SignedRatio.divideNat (x.rationalApproximation.value selected) n positive) := by
      simp only [SignedRatio.Equiv, SignedRatio.mul, SignedRatio.divideNat, QProb.toSignedRatio,
        Int.natCast_one, Int.mul_one]
    have differenceSame := SignedRatio.add_congr productSame
      (SignedRatio.equiv_refl (SignedRatio.neg (SignedRatio.divideNat (x.rationalApproximation.value refined) n positive)))
    have contracted := SignedRatio.divideNat_error_le (x.rationalApproximation.value selected)
      (x.rationalApproximation.value refined) n positive
    have errors := x.rationalApproximation.error_bound selected refined
    have repeated : QProb.LE left.toQProb (QProb.mul left.toQProb (QProb.ofNat n)) := by
      change left.num * (left.den * 1) ≤ (left.num * n) * left.den
      simpa only [Nat.mul_one, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.le_mul_of_pos_right (left.num * left.den) positive
    have expanded := QProb.add_le_add
      (QProb.le_trans (RegularRationalApproximation.productPrecision_le x.rationalApproximation reciprocal.rationalApproximation left) repeated)
      (QProb.le_refl refined.toQProb)
    have collect : QProb.Equiv
        (QProb.add (QProb.mul left.toQProb (QProb.ofNat n)) refined.toQProb)
        (QProb.mul (QProb.ofNat n) (QProb.add left.toQProb right.toQProb)) := by
      simp only [QProb.Equiv, QProb.add, QProb.mul, QProb.ofNat, PositiveRatio.toQProb,
        refined, PositiveRatio.mul, PositiveRatio.ofNat, Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.add_mul]
      ac_rfl
    exact QProb.le_congr (QProb.equiv_symm (SignedRatio.magnitude_congr differenceSame)) collect
      (QProb.le_trans contracted (QProb.le_trans errors expanded))
  exact equiv_symm (equiv_trans products (rationalApproximation_limit _))

/-- The rational-scaling interface used by entropy interpretation agrees
with multiplication by the embedded rational coefficient. -/
theorem scaleRatio_mul (weight : QProb) (x : ConstructiveReal) :
    Equiv (scaleRatio weight x) (mul (ofSignedRatio weight.toSignedRatio) x) := by
  let numerator := ofSignedRatio (QProb.ofNat weight.num).toSignedRatio
  let reciprocal := ofSignedRatio (QProb.toSignedRatio ⟨1, weight.den, weight.den_pos⟩)
  have collected : Equiv (mul (mul numerator x) reciprocal) (mul (mul numerator reciprocal) x) :=
    equiv_trans (mul_assoc _ _ _) (equiv_trans (mul_congr (equiv_refl _) (mul_comm _ _)) (equiv_symm (mul_assoc _ _ _)))
  have coefficient : Equiv (mul numerator reciprocal) (ofSignedRatio weight.toSignedRatio) := by
    apply equiv_trans (ofSignedRatio_mul _ _)
    apply (ofSignedRatio_equiv_iff _ _).mpr
    simp only [SignedRatio.Equiv, SignedRatio.mul, QProb.ofNat, QProb.toSignedRatio,
      Int.natCast_one, Int.mul_one, Nat.one_mul]
  exact equiv_trans (divideNat_mul _ _ _)
    (equiv_trans (mul_congr (scaleNat_mul _ _) (equiv_refl _))
      (equiv_trans collected (mul_congr coefficient (equiv_refl _))))

end Thesis.Probability.ConstructiveReal
