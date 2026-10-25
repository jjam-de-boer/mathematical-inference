import Thesis.Probability.ConstructiveRealEntropyFormula
import Thesis.Probability.CrossEntropyValue

namespace Thesis.Probability.ConstructiveReal

/-- A real KL contribution against an explicitly positive reference. The
cross-entropy-minus-entropy expression is continuous at zero observed mass;
it requires no logarithm or equality test at that coordinate. -/
def realRelativeEntropyTerm (observed : ConstructiveReal) (nonnegative : LE zero observed) (bounded : LE observed one)
    (reference : ConstructiveReal) (lower : PositiveRatio) (referencePositive : LE (ofSignedRatio lower.toSignedRatio) reference) : ConstructiveReal :=
  sub (neg (mul observed (reference.positiveLog2 lower referencePositive))) (observed.realEntropyTerm nonnegative bounded)

/-- Equivalent presentations and independent positive reference witnesses
produce equivalent KL values. No positivity proof for the observed mass is needed. -/
theorem realRelativeEntropyTerm_congr {observed observed' reference reference' : ConstructiveReal}
    (sameObserved : Equiv observed observed') (sameReference : Equiv reference reference')
    (nonnegative : LE zero observed) (nonnegative' : LE zero observed') (bounded : LE observed one) (bounded' : LE observed' one)
    (lower lower' : PositiveRatio) (positive : LE (ofSignedRatio lower.toSignedRatio) reference)
    (positive' : LE (ofSignedRatio lower'.toSignedRatio) reference') :
    Equiv (observed.realRelativeEntropyTerm nonnegative bounded reference lower positive)
      (observed'.realRelativeEntropyTerm nonnegative' bounded' reference' lower' positive') :=
  add_congr (neg_congr (mul_congr sameObserved (positiveLog2_congr sameReference lower lower' positive positive')))
    (neg_congr (realEntropyTerm_congr sameObserved nonnegative nonnegative' bounded bounded'))

/-- On positive observed mass, the extension is exactly the usual KL product. -/
theorem realRelativeEntropyTerm_formula (observed : ConstructiveReal) (nonnegative : LE zero observed) (bounded : LE observed one)
    (reference : ConstructiveReal) (lower : PositiveRatio) (referencePositive : LE (ofSignedRatio lower.toSignedRatio) reference)
    (observedLower : PositiveRatio) (observedPositive : LE (ofSignedRatio observedLower.toSignedRatio) observed) :
    Equiv (observed.realRelativeEntropyTerm nonnegative bounded reference lower referencePositive)
      (mul observed (sub (observed.positiveLog2 observedLower observedPositive) (reference.positiveLog2 lower referencePositive))) :=
  equiv_trans (add_congr (equiv_refl _) (neg_congr (observed.realEntropyTerm_formula nonnegative bounded observedLower observedPositive)))
    (equiv_trans (add_congr (equiv_refl _) (neg_neg _))
      (equiv_trans (add_comm _ _) (equiv_symm (mul_sub _ _ _))))

/-- Zero observed mass contributes zero for every positive reference. -/
theorem realRelativeEntropyTerm_zero (nonnegative : LE zero zero) (bounded : LE zero one)
    (reference : ConstructiveReal) (lower : PositiveRatio) (referencePositive : LE (ofSignedRatio lower.toSignedRatio) reference) :
    Equiv (zero.realRelativeEntropyTerm nonnegative bounded reference lower referencePositive) zero :=
  equiv_trans (add_congr (neg_congr (zero_mul _)) (neg_congr (realEntropyTerm_zero nonnegative bounded)))
    (equiv_trans (add_congr (equiv_symm (ofSignedRatio_neg SignedRatio.zero)) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero zero))

/-- Rational KL, including zero observations, is recovered by the real
extension. The reference need only be positive; it need not be normalized. -/
theorem realRelativeEntropyTerm_ofQProb (observed reference : QProb)
    (nonnegative : LE zero (ofSignedRatio observed.toSignedRatio)) (bounded : LE (ofSignedRatio observed.toSignedRatio) one)
    (referencePositive : 0 < reference.num) (lower : PositiveRatio)
    (lowerBound : LE (ofSignedRatio lower.toSignedRatio) (ofSignedRatio reference.toSignedRatio)) :
    Equiv ((ofSignedRatio observed.toSignedRatio).realRelativeEntropyTerm nonnegative bounded
      (ofSignedRatio reference.toSignedRatio) lower lowerBound)
      (Thesis.Probability.relativeEntropyTerm observed reference referencePositive).interpret := by
  let ref : PositiveRatio := ⟨reference.num, reference.den, referencePositive, reference.den_pos⟩
  have cross : Equiv (Thesis.Probability.crossEntropyTerm observed reference referencePositive).interpret
      (neg (mul (ofSignedRatio observed.toSignedRatio) (rationalLog2 ref))) :=
    equiv_trans (ExactLog.interpret_scaleRatio _ _)
      (equiv_trans (scaleRatio_mul _ _) (equiv_trans
        (mul_congr (equiv_refl _) (rationalLog2_inv ref)) (mul_neg _ _)))
  have exactDecomposition : Equiv
      (Thesis.Probability.relativeEntropyTerm observed reference referencePositive).interpret
      (sub (neg (mul (ofSignedRatio observed.toSignedRatio) (rationalLog2 ref))) (rationalEntropyTerm observed)) :=
    equiv_trans (ExactLog.interpret_congr (relativeEntropyTerm_cross_sub observed reference referencePositive))
      (equiv_trans (ExactLog.interpret_add _ _) (add_congr cross (ExactLog.interpret_neg _)))
  have converted : Equiv
      ((ofSignedRatio observed.toSignedRatio).realRelativeEntropyTerm nonnegative bounded
        (ofSignedRatio reference.toSignedRatio) lower lowerBound)
      (sub (neg (mul (ofSignedRatio observed.toSignedRatio) (rationalLog2 ref))) (rationalEntropyTerm observed)) :=
    add_congr (neg_congr (mul_congr (equiv_refl _) (positiveLog2_ofPositiveRatio ref lower lowerBound)))
      (neg_congr (realEntropyTerm_ofQProb observed nonnegative bounded))
  exact equiv_trans converted (equiv_symm exactDecomposition)

/-- The natural-unit KL contribution is the bit contribution times ln(2),
with the conversion calibrated by the proved Taylor-exponential inverse laws. -/
def naturalRelativeEntropyTerm (observed : ConstructiveReal) (nonnegative : LE zero observed) (bounded : LE observed one)
    (reference : ConstructiveReal) (lower : PositiveRatio) (referencePositive : LE (ofSignedRatio lower.toSignedRatio) reference) : ConstructiveReal :=
  mul (observed.realRelativeEntropyTerm nonnegative bounded reference lower referencePositive) lnTwo

theorem naturalRelativeEntropyTerm_formula (observed : ConstructiveReal) (nonnegative : LE zero observed) (bounded : LE observed one)
    (reference : ConstructiveReal) (lower : PositiveRatio) (referencePositive : LE (ofSignedRatio lower.toSignedRatio) reference)
    (observedLower : PositiveRatio) (observedPositive : LE (ofSignedRatio observedLower.toSignedRatio) observed) :
    Equiv (observed.naturalRelativeEntropyTerm nonnegative bounded reference lower referencePositive)
      (mul observed (sub (observed.positiveLn observedLower observedPositive) (reference.positiveLn lower referencePositive))) :=
  equiv_trans (mul_congr (observed.realRelativeEntropyTerm_formula nonnegative bounded reference lower referencePositive observedLower observedPositive) (equiv_refl lnTwo))
    (equiv_trans (mul_assoc observed _ lnTwo) (mul_congr (equiv_refl observed) (sub_mul _ _ lnTwo)))

end Thesis.Probability.ConstructiveReal
