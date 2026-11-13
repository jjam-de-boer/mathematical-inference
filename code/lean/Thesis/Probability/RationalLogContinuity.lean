import Thesis.Probability.EntropyInterpretation
import Thesis.Probability.EntropySmallMass
import Thesis.Probability.RationalPrecision
import Thesis.Probability.ConstructiveRealDistance

namespace Thesis.Probability.PositiveRatio

/-- A conservative explicit input modulus for base-two logarithms on the
half-line starting at `lower`. Only rational arithmetic is performed. -/
def logInputPrecision (lower precision : PositiveRatio) : PositiveRatio :=
  lower.divideNat (2 * precision.den) (Nat.mul_pos (by decide) precision.den_pos)

end Thesis.Probability.PositiveRatio

namespace Thesis.Probability

/-- A one-sided logarithm continuity bound derived from the finite Bernoulli
power bound, rather than a derivative or an analytic logarithm axiom. -/
theorem rational_log_modulus_bound (lower a b precision : PositiveRatio) (bLower : PositiveRatio.LE lower b)
    (close : SignedRatio.LE a.toSignedRatio (SignedRatio.add b.toSignedRatio (lower.logInputPrecision precision).toSignedRatio)) :
    ExactLog.LE (ExactLog.log a) (ExactLog.add (ExactLog.log b) (ExactLog.ofSignedRatio precision.toSignedRatio)) := by
  let factor := 2 * precision.den
  have factorPositive : 0 < factor := Nat.mul_pos (by decide) precision.den_pos
  let ratio : PositiveRatio := ⟨factor + 1, factor, Nat.zero_lt_succ _, factorPositive⟩
  have divided : SignedRatio.LE (lower.logInputPrecision precision).toSignedRatio
      (SignedRatio.divideNat b.toSignedRatio factor factorPositive) :=
    (SignedRatio.divideNat_le_iff _ _ factor factorPositive).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr bLower)
  have collect : SignedRatio.Equiv (SignedRatio.add b.toSignedRatio (SignedRatio.divideNat b.toSignedRatio factor factorPositive))
      (b.mul ratio).toSignedRatio := by
    simp only [SignedRatio.Equiv, SignedRatio.add, SignedRatio.divideNat, PositiveRatio.toSignedRatio, PositiveRatio.toQProb,
      QProb.toSignedRatio, PositiveRatio.mul, ratio, Int.natCast_mul, Int.natCast_add, Int.natCast_one,
      Int.mul_add, Int.add_mul, Int.mul_one]
    ac_rfl
  have ratioOrder : PositiveRatio.LE a (b.mul ratio) :=
    (SignedRatio.toSignedRatio_le_iff _ _).mp ((SignedRatio.le_congr (SignedRatio.equiv_refl _) collect).mp
      (SignedRatio.le_trans close (SignedRatio.add_le_add (SignedRatio.le_refl _) divided)))
  have logRatio := log_inverse_complement_bound (factor + 1) precision.den (by omega) precision.den_pos (by omega)
  have binaryUnit : ExactLog.divideNat (ExactLog.log (PositiveRatio.ofNat 2 (by decide))) precision.den precision.den_pos =
      ExactLog.ofSignedRatio (QProb.toSignedRatio ⟨1, precision.den, precision.den_pos⟩) := by
    apply ExactLog.ext
    · rfl
    · exact Nat.one_mul _
  have smallError : ExactLog.LE (ExactLog.log ratio) (ExactLog.ofSignedRatio precision.toSignedRatio) := by
    apply ExactLog.le_trans (show ExactLog.LE (ExactLog.log ratio)
      (ExactLog.divideNat (ExactLog.log (PositiveRatio.ofNat 2 (by decide))) precision.den precision.den_pos) from by
        simpa only [Nat.add_sub_cancel] using logRatio)
    rw [binaryUnit]
    apply (ExactLog.ofSignedRatio_le_iff _ _).mpr
    apply (SignedRatio.le_iff_cross _ _).mp
    apply (SignedRatio.toSignedRatio_le_iff _ _).mpr
    change 1 * precision.den ≤ precision.num * precision.den
    rw [Nat.one_mul]
    exact Nat.le_mul_of_pos_left _ precision.num_pos
  have monotone := (ExactLog.log_le_log_iff a (b.mul ratio)).mpr ratioOrder
  rw [← ExactLog.log_mul] at monotone
  exact ExactLog.le_trans monotone (ExactLog.add_le_add (ExactLog.le_refl _) smallError)

/-- The one-sided finite bound transfers to analytic logarithm values. -/
theorem rationalLog2_le_add_of_close (lower a b precision : PositiveRatio) (bLower : PositiveRatio.LE lower b)
    (close : SignedRatio.LE a.toSignedRatio (SignedRatio.add b.toSignedRatio (lower.logInputPrecision precision).toSignedRatio)) :
    ConstructiveReal.LE (ConstructiveReal.rationalLog2 a)
      (ConstructiveReal.add (ConstructiveReal.rationalLog2 b) (ConstructiveReal.ofSignedRatio precision.toSignedRatio)) :=
  (ConstructiveReal.le_congr (ConstructiveReal.equiv_refl _)
    (ConstructiveReal.equiv_trans (ExactLog.interpret_add _ _)
      (ConstructiveReal.add_congr (ConstructiveReal.equiv_refl _) (ExactLog.interpret_ofSignedRatio _)))).mp
    (ExactLog.interpret_mono (rational_log_modulus_bound lower a b precision bLower close))

/-- Rational logarithms satisfy a certified real error bound on every
explicit positive rational half-line. -/
theorem rationalLog2_within (lower a b precision : PositiveRatio) (aLower : PositiveRatio.LE lower a)
    (bLower : PositiveRatio.LE lower b)
    (close : QProb.LE (SignedRatio.sub a.toSignedRatio b.toSignedRatio).magnitude (lower.logInputPrecision precision).toQProb) :
    ConstructiveReal.Within precision.toQProb (ConstructiveReal.rationalLog2 a) (ConstructiveReal.rationalLog2 b) := by
  have twoSided := (SignedRatio.magnitude_sub_le_iff _ _ _).mp close
  have transfer (first second : PositiveRatio)
      (bounded : ExactLog.LE (ExactLog.log first) (ExactLog.add (ExactLog.log second) (ExactLog.ofSignedRatio precision.toSignedRatio))) :
      ConstructiveReal.LE (ConstructiveReal.rationalLog2 first)
        (ConstructiveReal.add (ConstructiveReal.rationalLog2 second) (ConstructiveReal.ofSignedRatio precision.toSignedRatio)) :=
    (ConstructiveReal.le_congr (ConstructiveReal.equiv_refl _)
      (ConstructiveReal.equiv_trans (ExactLog.interpret_add _ _)
        (ConstructiveReal.add_congr (ConstructiveReal.equiv_refl _) (ExactLog.interpret_ofSignedRatio _)))).mp
      (ExactLog.interpret_mono bounded)
  exact ⟨transfer a b (rational_log_modulus_bound lower a b precision bLower twoSided.1),
    transfer b a (rational_log_modulus_bound lower b a precision aLower twoSided.2)⟩

end Thesis.Probability
