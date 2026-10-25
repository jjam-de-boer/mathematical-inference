import Thesis.Probability.ConstructiveRealEntropyContinuity
import Thesis.Probability.ConstructiveRealPositiveTail
import Thesis.Probability.ConstructiveRealProductLimits
import Thesis.Probability.ConstructiveRealNaturalLog

namespace Thesis.Probability.ConstructiveReal

/-- The continuous extension has the usual product formula at every
explicitly positive real input. Positivity of the rational approximants is
proved only on a computed tail; it is not assumed for the original sequence. -/
theorem realEntropyTerm_formula (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one)
    (lower : PositiveRatio) (positive : LE (ofSignedRatio lower.toSignedRatio) x) :
    Equiv (x.realEntropyTerm nonnegative bounded) (neg (mul x (x.positiveLog2 lower positive))) := by
  let inputs := x.unitSequence nonnegative
  have inputsLimit : Equiv inputs.limit x := x.unitSequence_limit nonnegative
  have lowerLimit : LE (ofSignedRatio lower.toSignedRatio) inputs.limit :=
    (le_congr (equiv_refl _) inputsLimit).mpr positive
  let tail := inputs.positiveTail lower
  let logs := inputs.mapLog2Tail lower lowerLimit
  let products := (tail.mul logs).neg
  let offset := inputs.modulus lower.half.half.half
  let entropies := (x.entropyTermSequence nonnegative bounded).shift offset
  have terms (n : Nat) : Equiv (entropies.value n) (products.value n) := by
    let mass := x.unitCenter (PositiveRatio.unitPrecision (offset + n))
    have massLower : LE (ofSignedRatio lower.half.toSignedRatio) (ofSignedRatio mass.toSignedRatio) :=
      inputs.positiveTail_lower lower lowerLimit n
    have massPositive : 0 < mass.num := by
      have signed := SignedRatio.positive_of_lower lower.half mass.toSignedRatio ((ofSignedRatio_le_iff _ _).mp massLower)
      change (0 : Int) < (mass.num : Int) at signed
      omega
    exact rationalEntropyTerm_formula mass massPositive lower.half massLower
  have tailLimit : Equiv tail.limit x := equiv_trans (inputs.shift_limit offset) inputsLimit
  have logsLimit : Equiv logs.limit (x.positiveLog2 lower positive) :=
    equiv_trans (inputs.mapLog2Tail_limit lower lowerLimit) (positiveLog2_congr inputsLimit lower lower lowerLimit positive)
  have productLimit : Equiv products.limit (neg (mul x (x.positiveLog2 lower positive))) :=
    equiv_trans (RealCauchySequence.neg_limit _) (neg_congr (equiv_trans (RealCauchySequence.mul_limit tail logs)
      (mul_congr tailLimit logsLimit)))
  exact equiv_trans (equiv_symm ((x.entropyTermSequence nonnegative bounded).shift_limit offset))
    (equiv_trans (RealCauchySequence.limit_congr entropies products terms) productLimit)

/-- Entropy in natural units uses the independently calibrated logarithm
conversion. Rational probability weights remain rational. -/
def naturalEntropyTerm (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one) : ConstructiveReal :=
  mul (x.realEntropyTerm nonnegative bounded) lnTwo

theorem naturalEntropyTerm_formula (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one)
    (lower : PositiveRatio) (positive : LE (ofSignedRatio lower.toSignedRatio) x) :
    Equiv (x.naturalEntropyTerm nonnegative bounded) (neg (mul x (x.positiveLn lower positive))) :=
  equiv_trans (mul_congr (x.realEntropyTerm_formula nonnegative bounded lower positive) (equiv_refl lnTwo))
    (equiv_trans (neg_mul _ lnTwo) (neg_congr (mul_assoc x _ lnTwo)))

theorem naturalEntropyTerm_zero (nonnegative : LE zero zero) (bounded : LE zero one) :
    Equiv (zero.naturalEntropyTerm nonnegative bounded) zero :=
  equiv_trans (mul_congr (realEntropyTerm_zero nonnegative bounded) (equiv_refl lnTwo)) (zero_mul lnTwo)

end Thesis.Probability.ConstructiveReal
