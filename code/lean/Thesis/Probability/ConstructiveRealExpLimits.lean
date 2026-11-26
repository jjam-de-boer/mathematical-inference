import Thesis.Probability.ConstructiveRealExpContinuity
import Thesis.Probability.ConstructiveRealProductLimits

/-!
# Exponentials of effective real Cauchy sequences

The original sequence and its limit provide a common bound for sufficiently
late terms. This bound and the proved exponential modulus construct a
Cauchy schedule for pointwise exponentiation. The same estimates identify
its limit with the exponential of the original limit. No extra analytic
boundedness or an existential choice of indices is needed.
-/

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal

/-- Exponentiation preserves effective real Cauchy convergence. The uniform
bound needed for its modulus is derived from the original limit presentation;
there is no additional boundedness assumption or hidden parameter fitting. -/
def mapExp (sequence : RealCauchySequence) : RealCauchySequence where
  value n := (sequence.value n).exp
  modulus precision := max (sequence.modulus (RationalExponential.inputPrecision sequence.tailMagnitudeBound precision))
    (sequence.modulus PositiveRatio.one.half.half)
  cauchy precision n m left right := by
    exact exp_within_of_close sequence.tailMagnitudeBound precision
      (sequence.cauchy _ n m (Nat.le_trans (Nat.le_max_left _ _) left) (Nat.le_trans (Nat.le_max_left _ _) right))
      (sequence.tail_magnitude_bounded n (Nat.le_trans (Nat.le_max_right _ _) left))
      (sequence.tail_magnitude_bounded m (Nat.le_trans (Nat.le_max_right _ _) right))

/-- The effective limit of pointwise exponentials is the exponential of the
effective limit. All approximation indices are computed from supplied moduli. -/
theorem mapExp_limit (sequence : RealCauchySequence) :
    Equiv sequence.mapExp.limit sequence.limit.exp := by
  apply limit_unique _ _ (fun precision => max
    (sequence.modulus (RationalExponential.inputPrecision sequence.tailMagnitudeBound precision).half.half)
    (sequence.modulus PositiveRatio.one.half.half))
  intro precision n later
  exact exp_within_of_close sequence.tailMagnitudeBound precision
    (sequence.tail_within _ n (Nat.le_trans (Nat.le_max_left _ _) later))
    (sequence.tail_magnitude_bounded n (Nat.le_trans (Nat.le_max_right _ _) later))
    sequence.limit_magnitude_bounded

end Thesis.Probability.RealCauchySequence
