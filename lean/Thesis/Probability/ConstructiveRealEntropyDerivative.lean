import Thesis.Probability.ConstructiveRealEntropyFormula
import Thesis.Probability.ConstructiveDerivativeWithinProduct
import Thesis.Probability.ConstructiveDerivativeAlgebra

namespace Thesis.Probability.ConstructiveReal

/-- A positive part of the entropy domain. Both membership proofs are
explicit; no total extension or comparison with zero is introduced. -/
def entropyPositiveDomain (lower : PositiveRatio) (x : ConstructiveReal) : Prop :=
  LE (ofSignedRatio lower.toSignedRatio) x ∧ LE x one

def entropyPositiveNonnegative (lower : PositiveRatio) (x : ConstructiveReal) (inside : entropyPositiveDomain lower x) : LE zero x :=
  le_trans ((ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr lower.signed_nonnegative)) inside.1

/-- Effective entropy first variation in bits. The derivative is
`-log₂(p) - 1/ln(2)` on every supplied positive part of [0,1]. Its error
modulus is constructed from the proved logarithm and product remainders.
This does not assert differentiability at zero or multiplier existence. -/
def realEntropyTerm_hasDerivativeWithinAt (point : ConstructiveReal) (lower : PositiveRatio)
    (inside : entropyPositiveDomain lower point) :
    HasDerivativeWithinAt (entropyPositiveDomain lower)
      (fun y admitted => y.realEntropyTerm (entropyPositiveNonnegative lower y admitted) admitted.2) point inside
      (neg (add (point.positiveLog2 lower inside.1) RationalLogSecant.limit)) := by
  let identity := (HasDerivativeAt.identity point).restrict (entropyPositiveDomain lower) inside
  let logarithm := (positiveLog2_hasDerivativeWithinAt point lower inside.1).restrict
    (entropyPositiveDomain lower) inside (fun _ admitted => admitted.1)
  let product := (identity.mul logarithm).neg
  have converted : HasDerivativeWithinAt (entropyPositiveDomain lower)
      (fun y admitted => y.realEntropyTerm (entropyPositiveNonnegative lower y admitted) admitted.2) point inside
      (neg (add (mul one (point.positiveLog2 lower inside.1))
        (mul point (mul RationalLogSecant.limit (point.positiveInverse lower inside.1))))) :=
    product.function_congr (fun y admitted =>
      equiv_symm (realEntropyTerm_formula y (entropyPositiveNonnegative lower y admitted) admitted.2 lower admitted.1))
  have scaled : Equiv (mul point (mul RationalLogSecant.limit (point.positiveInverse lower inside.1))) RationalLogSecant.limit :=
    equiv_trans (mul_congr (equiv_refl _) (mul_comm _ _))
      (equiv_trans (equiv_symm (mul_assoc _ _ _))
        (equiv_trans (mul_congr (point.mul_positiveInverse lower inside.1) (equiv_refl _)) (one_mul _)))
  exact converted.slope_congr (neg_congr (add_congr (one_mul _) scaled))

/-- In natural units the same proved first variation has slope `-ln(p)-1`.
The unit coefficient follows from the established Taylor-exp/log calibration. -/
def naturalEntropyTerm_hasDerivativeWithinAt (point : ConstructiveReal) (lower : PositiveRatio)
    (inside : entropyPositiveDomain lower point) :
    HasDerivativeWithinAt (entropyPositiveDomain lower)
      (fun y admitted => y.naturalEntropyTerm (entropyPositiveNonnegative lower y admitted) admitted.2) point inside
      (neg (add (point.positiveLn lower inside.1) one)) := by
  let derivative := (realEntropyTerm_hasDerivativeWithinAt point lower inside).mul_constant lnTwo
  have slope : Equiv (mul (neg (add (point.positiveLog2 lower inside.1) RationalLogSecant.limit)) lnTwo)
      (neg (add (point.positiveLn lower inside.1) one)) :=
    equiv_trans (neg_mul _ lnTwo) (neg_congr (equiv_trans (add_mul _ _ lnTwo)
      (add_congr (equiv_refl _) coefficient_mul_lnTwo)))
  exact derivative.slope_congr slope

end Thesis.Probability.ConstructiveReal
