import Thesis.Probability.ConstructiveRealCauchy

namespace Thesis.Probability.RealCauchySequence
open ConstructiveReal

/-- Discarding a fixed finite prefix preserves an effective Cauchy modulus. -/
def shift (sequence : RealCauchySequence) (offset : Nat) : RealCauchySequence where
  value n := sequence.value (offset + n)
  modulus := sequence.modulus
  cauchy precision n m left right := sequence.cauchy precision (offset + n) (offset + m) (by omega) (by omega)

theorem shift_limit (sequence : RealCauchySequence) (offset : Nat) : Equiv (sequence.shift offset).limit sequence.limit := by
  apply limit_unique _ _ (fun precision => sequence.modulus precision.half.half)
  intro precision n later
  exact sequence.tail_within precision (offset + n) (by omega)

end Thesis.Probability.RealCauchySequence
