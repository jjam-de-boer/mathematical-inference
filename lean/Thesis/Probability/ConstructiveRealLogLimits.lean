import Thesis.Probability.ConstructiveRealLogOrder
import Thesis.Probability.ConstructiveRealCauchyOrder

namespace Thesis.Probability.ConstructiveReal

/-- A sequence of positive rational values converging effectively to the
real input, with every value above the supplied positive lower bound. -/
def positiveSequence (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : RealCauchySequence where
  value n := ofSignedRatio (x.positiveCenter lower (PositiveRatio.unitPrecision n)).toSignedRatio
  modulus precision := precision.half.den
  cauchy precision n m left right := by
    apply (within_ofSignedRatio_iff _ _ _).mpr
    have errors := (x.positiveApproximation lower bounded).error_bound (PositiveRatio.unitPrecision n) (PositiveRatio.unitPrecision m)
    have small := QProb.add_le_add (PositiveRatio.unitPrecision_le precision.half n left) (PositiveRatio.unitPrecision_le precision.half m right)
    exact QProb.le_trans errors (QProb.le_congr (QProb.equiv_refl _) precision.half_sum small)

theorem positiveSequence_lower (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) (n : Nat) :
    LE (ofSignedRatio lower.toSignedRatio) ((x.positiveSequence lower bounded).value n) :=
  (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (x.positiveCenter_lower lower _))

theorem positiveSequence_limit (x : ConstructiveReal) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) x) : Equiv (x.positiveSequence lower bounded).limit x := by
  apply RealCauchySequence.limit_unique _ _ (fun precision => precision.den)
  intro precision n later
  exact within_mono (within_symm (x.positiveCenter_within lower bounded (PositiveRatio.unitPrecision n)))
    (PositiveRatio.unitPrecision_le precision n later)

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal

/-- A uniform positive lower bound lets the proved logarithm modulus turn
any effective real Cauchy sequence into another effective Cauchy sequence. -/
def mapLog2 (sequence : RealCauchySequence) (lower : PositiveRatio)
    (bounded : ∀ n, LE (ofSignedRatio lower.toSignedRatio) (sequence.value n)) : RealCauchySequence where
  value n := (sequence.value n).positiveLog2 lower (bounded n)
  modulus precision := sequence.modulus (lower.logInputPrecision precision).half
  cauchy precision n m left right :=
    positiveLog2_within _ _ lower (bounded n) (bounded m) precision
      (sequence.cauchy (lower.logInputPrecision precision).half n m left right)

/-- Logarithms commute with effective limits on a positive half-line. The
limit's domain certificate follows from closed order, rather than being an
additional assumption left to a caller. -/
theorem mapLog2_limit (sequence : RealCauchySequence) (lower : PositiveRatio)
    (bounded : ∀ n, LE (ofSignedRatio lower.toSignedRatio) (sequence.value n)) :
    Equiv (sequence.mapLog2 lower bounded).limit
      (sequence.limit.positiveLog2 lower (sequence.le_limit _ bounded)) := by
  apply limit_unique _ _ (fun precision => sequence.modulus (lower.logInputPrecision precision).half.half.half)
  intro precision n later
  exact positiveLog2_within _ _ lower (bounded n) (sequence.le_limit _ bounded) precision
    (sequence.tail_within (lower.logInputPrecision precision).half n later)

end Thesis.Probability.RealCauchySequence
