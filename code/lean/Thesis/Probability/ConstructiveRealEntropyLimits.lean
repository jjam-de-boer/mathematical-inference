import Thesis.Probability.ConstructiveRealEntropyContinuity
import Thesis.Probability.ConstructiveRealCauchyOrder

/-!
# Effective limits of continuous entropy contributions

The same closed unit-interval entropy modulus controls both Cauchy tails
and agreement with the entropy of their limit. Closed order supplies the
unit-interval witnesses at the limit. The modulus applies even to terms
approaching zero, so this proof does not need lower floors on the sequence.
The convergence schedule is computed by composing the sequence modulus
with the entropy input radius.
-/

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal

/-- Entropy preserves effective Cauchy convergence on the closed unit
interval, including sequences approaching zero. The uniform modulus uses no
positive lower bound on the sequence or its limit. -/
def mapEntropy (sequence : RealCauchySequence)
    (nonnegative : ∀ n, LE zero (sequence.value n)) (bounded : ∀ n, LE (sequence.value n) one) : RealCauchySequence where
  value n := (sequence.value n).realEntropyTerm (nonnegative n) (bounded n)
  modulus precision := sequence.modulus (entropyInputPrecision precision).half
  cauchy precision n m left right :=
    realEntropyTerm_within _ _ (nonnegative n) (nonnegative m) (bounded n) (bounded m) precision
      (sequence.cauchy (entropyInputPrecision precision).half n m left right)

/-- The continuous zero convention commutes with effective limits. Closed
order derives both unit-interval witnesses for the limit from the sequence. -/
theorem mapEntropy_limit (sequence : RealCauchySequence)
    (nonnegative : ∀ n, LE zero (sequence.value n)) (bounded : ∀ n, LE (sequence.value n) one) :
    Equiv (sequence.mapEntropy nonnegative bounded).limit
      (sequence.limit.realEntropyTerm (sequence.le_limit zero nonnegative) (sequence.limit_le one bounded)) := by
  apply limit_unique _ _ (fun precision => sequence.modulus (entropyInputPrecision precision).half.half.half)
  intro precision n later
  exact realEntropyTerm_within _ _ (nonnegative n) (sequence.le_limit zero nonnegative) (bounded n)
    (sequence.limit_le one bounded) precision (sequence.tail_within (entropyInputPrecision precision).half n later)

end Thesis.Probability.RealCauchySequence
