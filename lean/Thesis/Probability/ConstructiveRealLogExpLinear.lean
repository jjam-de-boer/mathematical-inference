import Thesis.Probability.ConstructiveRealLogExp
import Thesis.Probability.ConstructiveRealPositiveTail

namespace Thesis.Probability.ConstructiveReal

/-- Continuity of the actual logarithm-exponential composite extends its
proved rational linearity to every real input. The logarithm domain on the
approximating sequence is constructed from its positive limit. -/
theorem expLog2_linear (x : ConstructiveReal) : Equiv x.expLog2 (mul x one.expLog2) := by
  let inputs := x.rationalSequence
  let outputs := inputs.mapExp
  have outputLimit : Equiv outputs.limit x.exp :=
    equiv_trans inputs.mapExp_limit (exp_congr x.rationalSequence_limit)
  have bounded : LE (ofSignedRatio x.expLower.toSignedRatio) outputs.limit :=
    (le_congr (equiv_refl _) (equiv_symm outputLimit)).mp x.exp_lower
  let offset := outputs.modulus x.expLower.half.half.half
  let logs := outputs.mapLog2Tail x.expLower bounded
  let linear := (inputs.shift offset).mul (RealCauchySequence.constant one.expLog2)
  have same (n : Nat) : Equiv (logs.value n) (linear.value n) := by
    let q := x.rationalApproximation.value (PositiveRatio.unitPrecision (offset + n))
    have witness : Equiv (logs.value n) (ofSignedRatio q).expLog2 :=
      positiveLog2_congr (equiv_refl _) x.expLower.half (ofSignedRatio q).expLower
        (outputs.positiveTail_lower x.expLower bounded n) (ofSignedRatio q).exp_lower
    exact equiv_trans witness (expLog2_ofSignedRatio q)
  have logLimit : Equiv logs.limit x.expLog2 :=
    equiv_trans (outputs.mapLog2Tail_limit x.expLower bounded)
      (positiveLog2_congr outputLimit x.expLower x.expLower bounded x.exp_lower)
  have inputLimit : Equiv (inputs.shift offset).limit x :=
    equiv_trans (inputs.shift_limit offset) x.rationalSequence_limit
  have linearLimit : Equiv linear.limit (mul x one.expLog2) :=
    equiv_trans (RealCauchySequence.mul_limit _ _) (mul_congr inputLimit (RealCauchySequence.constant_limit _))
  exact equiv_trans (equiv_symm logLimit) (equiv_trans (RealCauchySequence.limit_congr logs linear same) linearLimit)

end Thesis.Probability.ConstructiveReal
