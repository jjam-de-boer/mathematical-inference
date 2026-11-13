import Thesis.Probability.RationalLogConcavity
import Thesis.Probability.RationalLogContinuity
import Thesis.Probability.ExactLogRationalArithmetic

namespace Thesis.Probability.RationalLogSecant

/-- A rational point one reciprocal unit above one. -/
def point (den : Nat) (positive : 0 < den) : PositiveRatio :=
  ⟨den + 1, den, Nat.zero_lt_succ _, positive⟩

/-- The right secant slope of the base-two logarithm at one. The value is
symbolic logarithmic data, not a rational approximation to that slope. -/
def slope (den : Nat) (positive : 0 < den) : ExactLog :=
  ExactLog.scaleNat den (ExactLog.log (point den positive))

theorem point_ge_one (den : Nat) (positive : 0 < den) :
    PositiveRatio.LE PositiveRatio.one (point den positive) := by
  change 1 * den ≤ (den + 1) * 1
  omega

/-- Concavity makes reciprocal-step secants increase as their denominators
increase. This uses only finite weighted AM–GM, including a zero first
weight when the denominators coincide. -/
theorem slope_mono (first second : Nat) (firstPositive : 0 < first) (secondPositive : 0 < second)
    (ordered : first ≤ second) : ExactLog.LE (slope first firstPositive) (slope second secondPositive) := by
  have arithmetic : QProb.LE
      (QProb.add (QProb.scale (second - first) PositiveRatio.one.toQProb)
        (QProb.scale first (point first firstPositive).toQProb))
      (QProb.scale (second - first + first) (point second secondPositive).toQProb) := by
    rw [Nat.sub_add_cancel ordered]
    simp only [QProb.LE, QProb.add, QProb.scale, PositiveRatio.one, PositiveRatio.toQProb,
      point, Nat.mul_one, Nat.one_mul]
    have split : (second - first) * first + first * (first + 1) = (second + 1) * first := by
      calc
        _ = (second - first + first) * first + first := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]; ac_rfl
        _ = (second + 1) * first := by
          rw [Nat.sub_add_cancel ordered, Nat.add_mul, Nat.one_mul]
    rw [split]
    exact Nat.le_of_eq (by ac_rfl)
  have compared := rational_log_pair_weighted PositiveRatio.one (point first firstPositive)
    (point second secondPositive) (second - first) first arithmetic
  have vanished : ExactLog.Equiv (ExactLog.scaleNat (second - first) (ExactLog.log PositiveRatio.one)) ExactLog.zero := by
    change PositiveRatio.Equiv ((PositiveRatio.one.pow (second - first)).pow 1)
      (PositiveRatio.one.pow 1)
    simp only [PositiveRatio.one_pow, PositiveRatio.pow_one]
    exact PositiveRatio.equiv_refl _
  have reduced := ExactLog.add_congr vanished (ExactLog.equiv_refl (slope first firstPositive))
  rw [ExactLog.zero_add] at reduced
  rw [Nat.sub_add_cancel ordered] at compared
  exact (ExactLog.le_congr reduced (ExactLog.equiv_refl _)).mp compared

/-- Halving a reciprocal step changes the secant by at most half that step.
The estimate comes from the exact quadratic gap between `(1+h/2)^2` and
`1+h`, followed by the finite Bernoulli logarithm bound. -/
theorem slope_double_upper (den : Nat) (positive : 0 < den) :
    ExactLog.LE (slope (2 * den) (Nat.mul_pos (by decide) positive))
      (ExactLog.add (slope den positive)
        (ExactLog.ofSignedRatio (⟨1, 2 * den, by decide, Nat.mul_pos (by decide) positive⟩ : PositiveRatio).toSignedRatio)) := by
  let small : PositiveRatio := ⟨1, 2 * (den * den), by decide, Nat.mul_pos (by decide) (Nat.mul_pos positive positive)⟩
  let next := point (2 * den) (Nat.mul_pos (by decide) positive)
  have gap : SignedRatio.LE (next.pow 2).toSignedRatio
      (SignedRatio.add (point den positive).toSignedRatio (PositiveRatio.one.logInputPrecision small).toSignedRatio) := by
    apply (SignedRatio.le_iff_cross _ _).mpr
    simp only [SignedRatio.add, PositiveRatio.toSignedRatio, PositiveRatio.toQProb, QProb.toSignedRatio,
      PositiveRatio.pow, point, next, PositiveRatio.logInputPrecision, PositiveRatio.divideNat,
      PositiveRatio.one, small, Nat.pow_two, Int.natCast_mul, Int.natCast_add, Int.natCast_one,
      show ((2 : Nat) : Int) = 1 + 1 from rfl,
      Int.mul_one, Int.one_mul, Int.mul_add, Int.add_mul]
    apply Int.le_of_eq
    ac_rfl
  have estimated := rational_log_modulus_bound PositiveRatio.one (next.pow 2) (point den positive)
    small (point_ge_one den positive) gap
  have scaled := (ExactLog.scaleNat_le_scaleNat_iff den positive _ _).mpr estimated
  rw [ExactLog.log_pow, ExactLog.scaleNat_mul, ExactLog.scaleNat_add] at scaled
  have unit : SignedRatio.Equiv (SignedRatio.scaleNat den small.toSignedRatio)
      (⟨1, 2 * den, by decide, Nat.mul_pos (by decide) positive⟩ : PositiveRatio).toSignedRatio := by
    simp only [SignedRatio.Equiv, SignedRatio.scaleNat, PositiveRatio.toSignedRatio,
      PositiveRatio.toQProb, QProb.toSignedRatio, small, Int.natCast_mul]
    ac_rfl
  have error := ExactLog.equiv_trans (ExactLog.scaleNat_ofSignedRatio den small.toSignedRatio)
    (ExactLog.ofSignedRatio_congr unit)
  exact (ExactLog.le_congr (ExactLog.equiv_refl _) (ExactLog.add_congr (ExactLog.equiv_refl _) error)).mp scaled


/-- The rational point `1 + step`, retaining unreduced representations. -/
def offsetPoint (step : PositiveRatio) : PositiveRatio :=
  ⟨step.den + step.num, step.den, by have := step.num_pos; omega, step.den_pos⟩

/-- Right secants for every strictly positive rational step. -/
def offsetSlope (step : PositiveRatio) : ExactLog :=
  ExactLog.scaleRatio step.inv.toQProb (ExactLog.log (offsetPoint step))

/-- Logarithm concavity orders arbitrary positive rational secants in the
opposite order to their step sizes. No rational step is rounded. -/
theorem offsetSlope_antitone (small large : PositiveRatio) (ordered : PositiveRatio.LE small large) :
    ExactLog.LE (offsetSlope large) (offsetSlope small) := by
  let whole := large.num * small.den
  let part := small.num * large.den
  have included : part ≤ whole := ordered
  have recovered : whole - part + part = whole := Nat.sub_add_cancel included
  have arithmetic : QProb.LE
      (QProb.add (QProb.scale (whole - part) PositiveRatio.one.toQProb)
        (QProb.scale part (offsetPoint large).toQProb))
      (QProb.scale (whole - part + part) (offsetPoint small).toQProb) := by
    rw [recovered]
    simp only [QProb.LE, QProb.add, QProb.scale, PositiveRatio.one, PositiveRatio.toQProb,
      offsetPoint, Nat.mul_one, Nat.one_mul]
    have regroup : (whole - part) * large.den + part * (large.den + large.num) =
        whole * large.den + part * large.num := by
      calc
        _ = (whole - part + part) * large.den + part * large.num := by
          simp only [Nat.mul_add, Nat.add_mul]; ac_rfl
        _ = _ := by rw [recovered]
    rw [regroup]
    apply Nat.le_of_eq
    simp only [whole, part, Nat.mul_add, Nat.add_mul]
    ac_rfl
  have compared := rational_log_pair_weighted PositiveRatio.one (offsetPoint large) (offsetPoint small)
    (whole - part) part arithmetic
  simp only [ExactLog.LE, ExactLog.add, ExactLog.scaleNat, ExactLog.log,
    PositiveRatio.pow_one, PositiveRatio.one_pow, PositiveRatio.one_mul] at compared
  rw [recovered] at compared
  simpa only [offsetSlope, ExactLog.LE, ExactLog.scaleRatio, ExactLog.divideNat, ExactLog.scaleNat,
    ExactLog.log, PositiveRatio.inv, PositiveRatio.toQProb, Nat.one_mul, ← PositiveRatio.pow_mul,
    whole, part, Nat.mul_one, Nat.mul_comm] using compared

/-- Reciprocal-unit secants agree with the general rational interface. -/
theorem offsetSlope_unit (den : Nat) (positive : 0 < den) :
    offsetSlope ⟨1, den, by decide, positive⟩ = slope den positive := by
  apply ExactLog.ext
  · rfl
  · exact Nat.one_mul _

end Thesis.Probability.RationalLogSecant
