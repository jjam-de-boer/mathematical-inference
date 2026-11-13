import Thesis.Probability.RationalExponentialAddition
import Thesis.Probability.ConstructiveRealExpLimits
import Thesis.Probability.RationalApproximationSequence
import Thesis.Probability.ConstructiveRealDifferenceLimits

namespace Thesis.Probability.ConstructiveReal

/-- The natural exponential addition law for arbitrary constructive reals.
It is the effective-limit transfer of the proved finite Taylor product law. -/
theorem exp_add (x y : ConstructiveReal) : Equiv (exp (add x y)) (mul x.exp y.exp) := by
  let first := x.rationalSequence
  let second := y.rationalSequence
  let left := (first.add second).mapExp
  let right := first.mapExp.mul second.mapExp
  have same (n : Nat) : Equiv (left.value n) (right.value n) := by
    let a := x.rationalApproximation.value (PositiveRatio.unitPrecision n)
    let b := y.rationalApproximation.value (PositiveRatio.unitPrecision n)
    exact equiv_trans (exp_congr (ofSignedRatio_add a b))
      (equiv_trans (exp_ofSignedRatio (SignedRatio.add a b))
        (equiv_trans (RationalExponential.exp_add a b)
          (mul_congr (equiv_symm (exp_ofSignedRatio a)) (equiv_symm (exp_ofSignedRatio b)))))
  have inputLimit : Equiv (first.add second).limit (add x y) :=
    equiv_trans (RealCauchySequence.add_limit first second) (add_congr x.rationalSequence_limit y.rationalSequence_limit)
  have leftLimit : Equiv left.limit (exp (add x y)) :=
    equiv_trans (RealCauchySequence.mapExp_limit _) (exp_congr inputLimit)
  have firstLimit : Equiv first.mapExp.limit x.exp :=
    equiv_trans first.mapExp_limit (exp_congr x.rationalSequence_limit)
  have secondLimit : Equiv second.mapExp.limit y.exp :=
    equiv_trans second.mapExp_limit (exp_congr y.rationalSequence_limit)
  have rightLimit : Equiv right.limit (mul x.exp y.exp) :=
    equiv_trans (RealCauchySequence.mul_limit _ _) (mul_congr firstLimit secondLimit)
  exact equiv_trans (equiv_symm leftLimit) (equiv_trans (RealCauchySequence.limit_congr left right same) rightLimit)

/-- Opposite exponential arguments multiply to one. This follows from
addition and the Taylor value at zero, rather than an assumed reciprocal law. -/
theorem exp_mul_exp_neg (x : ConstructiveReal) : Equiv (mul x.exp (neg x).exp) one :=
  equiv_trans (equiv_symm (exp_add x (neg x))) (equiv_trans (exp_congr (add_neg x)) exp_zero)


/-- Finite repeated addition becomes the corresponding exponential power. -/
theorem exp_scaleNat (x : ConstructiveReal) (n : Nat) : Equiv (exp (scaleNat n x)) (pow x.exp n) := by
  induction n with
  | zero => exact exp_zero
  | succ n ih =>
      exact equiv_trans (exp_add (scaleNat n x) x) (mul_congr ih (equiv_refl x.exp))

end Thesis.Probability.ConstructiveReal
