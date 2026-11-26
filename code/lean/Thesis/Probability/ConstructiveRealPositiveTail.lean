import Thesis.Probability.ConstructiveRealLogLimits
import Thesis.Probability.ConstructiveRealSequenceShift
import Thesis.Probability.ConstructiveRealPositiveNeighborhood

/-!
# Computing a usable positive tail from a positive effective limit

An explicit floor at the limit and its convergence modulus select a
tail where each term retains half the floor. Earlier terms can have any
sign. The shortened sequence has a common domain for taking logarithms,
and its logarithm limit agrees with the original limit's logarithm.
No decision about arbitrary real signs is required.
-/

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal

/-- A proved positive lower bound on an effective limit computes a tail
whose terms all exceed half that bound. No sign comparison is performed. -/
theorem positive_tail_lower (sequence : RealCauchySequence) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) sequence.limit) (n : Nat)
    (later : sequence.modulus lower.half.half.half ≤ n) : LE (ofSignedRatio lower.half.toSignedRatio) (sequence.value n) :=
  positive_half_lower sequence.limit (sequence.value n) lower bounded (within_symm (sequence.tail_within lower.half n later))

/-- Discard only the explicitly computed finite prefix needed for a common
positive logarithm domain. The original sequence may have nonpositive early terms. -/
def positiveTail (sequence : RealCauchySequence) (lower : PositiveRatio) : RealCauchySequence :=
  sequence.shift (sequence.modulus lower.half.half.half)

theorem positiveTail_lower (sequence : RealCauchySequence) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) sequence.limit) (n : Nat) :
    LE (ofSignedRatio lower.half.toSignedRatio) ((sequence.positiveTail lower).value n) :=
  sequence.positive_tail_lower lower bounded _ (by omega)

def mapLog2Tail (sequence : RealCauchySequence) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) sequence.limit) : RealCauchySequence :=
  (sequence.positiveTail lower).mapLog2 lower.half (sequence.positiveTail_lower lower bounded)

/-- Taking logarithms along the computed positive tail converges to the
logarithm of the original limit. No uniform positivity premise on the whole
original sequence is left to a caller. -/
theorem mapLog2Tail_limit (sequence : RealCauchySequence) (lower : PositiveRatio)
    (bounded : LE (ofSignedRatio lower.toSignedRatio) sequence.limit) :
    Equiv (sequence.mapLog2Tail lower bounded).limit (sequence.limit.positiveLog2 lower bounded) :=
  equiv_trans (RealCauchySequence.mapLog2_limit _ lower.half (sequence.positiveTail_lower lower bounded))
    (positiveLog2_congr (sequence.shift_limit _) lower.half lower
      ((sequence.positiveTail lower).le_limit _ (sequence.positiveTail_lower lower bounded)) bounded)

end Thesis.Probability.RealCauchySequence
