import Thesis.Probability.ConstructiveRealUnitApproximation
import Thesis.Probability.ConstructiveRealRationalEntropy
import Thesis.Probability.ConstructiveRealCauchyOrder

namespace Thesis.Probability.ConstructiveReal

/-- Entropy contributions of scalar rational unit-interval approximants.
The rational modulus includes the boundary at zero, so the real argument's
zero status and sign never need to be decided. -/
def entropyTermSequence (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one) : RealCauchySequence where
  value n := rationalEntropyTerm (x.unitCenter (PositiveRatio.unitPrecision n))
  modulus precision := (entropyInputPrecision precision).half.den
  cauchy precision n m left right := by
    let unitN := PositiveRatio.unitPrecision n
    let unitM := PositiveRatio.unitPrecision m
    have inputs := within_triangle (within_symm (x.unitCenter_within nonnegative unitN)) (x.unitCenter_within nonnegative unitM)
    have errorBound := QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.half_sum (entropyInputPrecision precision))
      (QProb.add_le_add (PositiveRatio.unitPrecision_le _ n left) (PositiveRatio.unitPrecision_le _ m right))
    exact rationalEntropyTerm_within precision _ _ (x.unitCenter_bounded nonnegative bounded unitN)
      (x.unitCenter_bounded nonnegative bounded unitM) ((within_ofSignedRatio_iff _ _ _).mp (within_mono inputs errorBound))

/-- The continuous real entropy contribution in bits on the closed unit
interval. Every requested enclosure is computed from finite rational data.
No value of log(0) or test of real equality to zero is introduced. -/
def realEntropyTerm (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one) : ConstructiveReal :=
  (x.entropyTermSequence nonnegative bounded).limit

/-- The extension recovers every existing rational entropy contribution,
including unreduced fractions and explicit zero masses. -/
theorem realEntropyTerm_ofQProb (mass : QProb) (nonnegative : LE zero (ofSignedRatio mass.toSignedRatio))
    (bounded : LE (ofSignedRatio mass.toSignedRatio) one) :
    Equiv ((ofSignedRatio mass.toSignedRatio).realEntropyTerm nonnegative bounded) (rationalEntropyTerm mass) := by
  apply RealCauchySequence.limit_unique _ _ (fun _ => 0)
  intro precision n _
  change Within precision.toQProb
    (rationalEntropyTerm ((ofSignedRatio mass.toSignedRatio).unitCenter (PositiveRatio.unitPrecision n))) (rationalEntropyTerm mass)
  rw [unitCenter_ofQProb]
  exact within_refl _ _

/-- Equivalent real presentations and different domain witnesses yield the
same entropy value. The comparison uses explicit common approximation indices. -/
theorem realEntropyTerm_congr {x y : ConstructiveReal} (same : Equiv x y)
    (nonnegativeX : LE zero x) (nonnegativeY : LE zero y) (boundedX : LE x one) (boundedY : LE y one) :
    Equiv (x.realEntropyTerm nonnegativeX boundedX) (y.realEntropyTerm nonnegativeY boundedY) := by
  let first := x.entropyTermSequence nonnegativeX boundedX
  let second := y.entropyTermSequence nonnegativeY boundedY
  have terms (precision : PositiveRatio) (n : Nat) (later : (entropyInputPrecision precision).half.den ≤ n) :
      Within precision.toQProb (first.value n) (second.value n) := by
    let unit := PositiveRatio.unitPrecision n
    have left := (within_congr (equiv_refl _) same).mp (within_symm (x.unitCenter_within nonnegativeX unit))
    have inputs := within_triangle left (y.unitCenter_within nonnegativeY unit)
    have bound := PositiveRatio.unitPrecision_le (entropyInputPrecision precision).half n later
    have errorBound := QProb.le_congr (QProb.equiv_refl _) (PositiveRatio.half_sum (entropyInputPrecision precision))
      (QProb.add_le_add bound bound)
    exact rationalEntropyTerm_within precision _ _ (x.unitCenter_bounded nonnegativeX boundedX unit)
      (y.unitCenter_bounded nonnegativeY boundedY unit) ((within_ofSignedRatio_iff _ _ _).mp (within_mono inputs errorBound))
  apply first.limit_unique second.limit (fun precision => max (entropyInputPrecision precision.half).half.den
    (second.modulus precision.half.half.half))
  intro precision n later
  exact within_triangle_halves precision
    (terms precision.half n (Nat.le_trans (Nat.le_max_left _ _) later))
    (second.tail_within precision.half n (Nat.le_trans (Nat.le_max_right _ _) later))

theorem realEntropyTerm_zero (nonnegative : LE zero zero) (bounded : LE zero one) :
    Equiv (zero.realEntropyTerm nonnegative bounded) zero := by
  have rational : Equiv (rationalEntropyTerm QProb.zero) zero := by
    change Equiv (Thesis.Probability.entropyTerm QProb.zero).interpret zero
    rw [entropyTerm_zero_num QProb.zero rfl]
    exact ExactLog.interpret_ofSignedRatio SignedRatio.zero
  exact equiv_trans (realEntropyTerm_ofQProb QProb.zero nonnegative bounded) rational

theorem realEntropyTerm_one (nonnegative : LE zero one) (bounded : LE one one) :
    Equiv (one.realEntropyTerm nonnegative bounded) zero :=
  equiv_trans (realEntropyTerm_ofQProb QProb.one nonnegative bounded)
    (equiv_trans (ExactLog.interpret_congr (by decide +kernel : ExactLog.Equiv (Thesis.Probability.entropyTerm QProb.one) ExactLog.zero))
      (ExactLog.interpret_ofSignedRatio SignedRatio.zero))

/-- Entropy contributions are nonnegative throughout the closed interval. -/
theorem realEntropyTerm_nonnegative (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one) :
    LE zero (x.realEntropyTerm nonnegative bounded) := by
  apply RealCauchySequence.le_limit _ zero
  intro n
  let mass := x.unitCenter (PositiveRatio.unitPrecision n)
  have massBound : QProb.LE mass QProb.one := by
    simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using x.unitCenter_bounded nonnegative bounded (PositiveRatio.unitPrecision n)
  exact (le_congr (ExactLog.interpret_ofSignedRatio SignedRatio.zero) (equiv_refl _)).mp
    (ExactLog.interpret_mono (entropyTerm_nonnegative mass massBound))

end Thesis.Probability.ConstructiveReal
