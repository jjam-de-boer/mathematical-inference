import Thesis.Probability.ExactLogRational
import Thesis.Probability.ExactLogLinear
import Thesis.Probability.ExactLogRoots
import Thesis.Probability.SignedRatioFiniteSum

namespace Thesis.Probability.ExactLog

private theorem signed_parts (value : Int) :
    (value.toNat : Int) - ((-value).toNat : Int) = value := by
  cases value with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

/-- The exact rational-bit embedding preserves addition, including signed
values whose two positive/negative exponent presentations differ. -/
theorem ofSignedRatio_add (a b : SignedRatio) :
    Equiv (add (ofSignedRatio a) (ofSignedRatio b)) (ofSignedRatio (SignedRatio.add a b)) := by
  simp only [Equiv, ofSignedRatio, add, PositiveRatio.Equiv, PositiveRatio.toQProb,
    PositiveRatio.mul, PositiveRatio.pow, QProb.Equiv, ← Nat.pow_mul, ← Nat.pow_add]
  apply congrArg (fun exponent => 2 ^ exponent)
  apply Int.ofNat_inj.mp
  simp only [Int.natCast_add, Int.natCast_mul, SignedRatio.add]
  have first := congrArg (fun value : Int => value * (b.den : Int) * ((a.den * b.den : Nat) : Int)) (signed_parts a.num)
  have second := congrArg (fun value : Int => value * (a.den : Int) * ((a.den * b.den : Nat) : Int)) (signed_parts b.num)
  have total := congrArg (fun value : Int => value * ((a.den * b.den : Nat) : Int))
    (signed_parts (a.num * (b.den : Int) + b.num * (a.den : Int)))
  simp only [Int.natCast_mul, Int.mul_sub, Int.mul_add,
    Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at first second total ⊢
  omega

/-- Negation exchanges the two natural powers in a signed-bit presentation. -/
theorem ofSignedRatio_neg (value : SignedRatio) : ofSignedRatio (SignedRatio.neg value) = neg (ofSignedRatio value) := by
  apply ext
  · apply PositiveRatio.ext <;> simp only [ofSignedRatio, SignedRatio.neg, neg, PositiveRatio.inv, Int.neg_neg]
  · rfl

theorem scaleNat_succ (n : Nat) (x : ExactLog) :
    Equiv (scaleNat (n + 1) x) (add (scaleNat n x) x) := by
  have roots := root_add_equiv (x.argument.pow n) x.argument x.degree x.degree_pos
  have power : PositiveRatio.mul (x.argument.pow n) x.argument = x.argument.pow (n + 1) := by
    rw [PositiveRatio.pow_add, PositiveRatio.pow_one]
  rw [power] at roots
  exact equiv_symm roots

theorem ofSignedRatio_divideNat (value : SignedRatio) (n : Nat) (positive : 0 < n) :
    ofSignedRatio (SignedRatio.divideNat value n positive) = divideNat (ofSignedRatio value) n positive := rfl

/-- Natural amplification of a rational number of bits. -/
theorem scaleNat_ofSignedRatio (n : Nat) (value : SignedRatio) :
    Equiv (scaleNat n (ofSignedRatio value)) (ofSignedRatio (SignedRatio.scaleNat n value)) := by
  induction n with
  | zero =>
      have same : SignedRatio.Equiv (SignedRatio.scaleNat 0 value) SignedRatio.zero := by
        simp only [SignedRatio.Equiv, SignedRatio.scaleNat, Int.natCast_zero, Int.zero_mul, SignedRatio.zero]
      exact equiv_trans (scaleNat_zero _) (equiv_symm (ofSignedRatio_congr same))
  | succ n ih =>
      have added : SignedRatio.Equiv (SignedRatio.add (SignedRatio.scaleNat n value) value)
          (SignedRatio.scaleNat (n + 1) value) := by
        simp only [SignedRatio.Equiv, SignedRatio.add, SignedRatio.scaleNat, Int.natCast_add,
          Int.natCast_one, Int.add_mul, Int.one_mul, Int.natCast_mul]
        ac_rfl
      exact equiv_trans (scaleNat_succ n (ofSignedRatio value))
        (equiv_trans (add_congr ih (equiv_refl _))
          (equiv_trans (ofSignedRatio_add _ _) (ofSignedRatio_congr added)))

end Thesis.Probability.ExactLog
