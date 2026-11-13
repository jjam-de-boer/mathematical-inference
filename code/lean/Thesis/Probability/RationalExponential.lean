import Thesis.Probability.RationalTaylorExponential
import Thesis.Probability.RationalSeriesTail
import Thesis.Probability.RationalNaturalBound

namespace Thesis.Probability.RationalExponential
open SignedRatio RationalTaylorExponential

/-- A finite initial block after which consecutive absolute Taylor terms
shrink by at least a factor of two. Quotients keep unreduced numerators from
artificially determining the size of this block. -/
def offset (x : SignedRatio) : Nat := 2 * x.magnitude.naturalUpper

def tailBound (x : SignedRatio) : Nat := (term x (offset x)).magnitude.naturalUpper

theorem ratio_bound (x : SignedRatio) (n : Nat) :
    QProb.LE (QProb.mul x.magnitude (⟨1, offset x + n + 1, Nat.zero_lt_succ _⟩ : QProb)) ⟨1, 2, by decide⟩ := by
  have enlarged := QProb.mul_le_mul x.magnitude.le_naturalUpper (QProb.le_refl (⟨1, offset x + n + 1, Nat.zero_lt_succ _⟩ : QProb))
  apply QProb.le_trans enlarged
  change (x.magnitude.naturalUpper * 1) * 2 ≤ 1 * (1 * (offset x + n + 1))
  simp only [Nat.mul_one, Nat.one_mul, offset]
  omega

/-- The factorial denominators give geometric domination after the computed
finite prefix, for every signed rational argument. -/
theorem tail_bound (x : SignedRatio) (n : Nat) :
    QProb.LE (term x (offset x + n)).magnitude (RationalGeometricSeries.envelope (tailBound x) n) := by
  induction n with
  | zero => exact (term x (offset x)).magnitude.le_naturalUpper
  | succ n ih =>
      have identity : QProb.Equiv (term x (offset x + n + 1)).magnitude
          (QProb.mul (term x (offset x + n)).magnitude
            (QProb.mul x.magnitude (⟨1, offset x + n + 1, Nat.zero_lt_succ _⟩ : QProb))) :=
        QProb.equiv_trans (magnitude_divideNat _ _ _)
          (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_trans (magnitude_mul _ _) (QProb.mul_comm _ _)) (QProb.equiv_refl _))
            (QProb.mul_assoc _ _ _))
      have estimate := QProb.mul_le_mul ih (ratio_bound x n)
      have collect : QProb.Equiv
          (QProb.mul (RationalGeometricSeries.envelope (tailBound x) n) (⟨1, 2, by decide⟩ : QProb))
          (RationalGeometricSeries.envelope (tailBound x) (n + 1)) := by
        simp only [QProb.Equiv, QProb.mul, RationalGeometricSeries.envelope, Nat.mul_one, Nat.pow_succ]
      exact QProb.le_congr (QProb.equiv_symm identity) collect estimate

def sequence (x : SignedRatio) : RationalCauchySequence :=
  RationalGeometricSeries.eventualSequence (term x) (offset x) (tailBound x) (tail_bound x)

/-- Natural exponential of every rational argument, defined by its exact
Taylor coefficients and the proved effective tail modulus. General real
arguments and analytic identities require further proofs. -/
def exp (x : SignedRatio) : ConstructiveReal := (sequence x).limit

/-- Every truncation after the computed prefix has a certified remainder. -/
theorem remainder (x : SignedRatio) (n : Nat) (after : offset x ≤ n) :
    ConstructiveReal.Within (RationalGeometricSeries.envelope (2 * tailBound x) (n - offset x))
      (ConstructiveReal.ofSignedRatio (RationalGeometricSeries.partialSum (term x) n)) (exp x) :=
  RationalGeometricSeries.eventual_remainder (term x) (offset x) (tailBound x) (tail_bound x) n after

/-- Rational representation changes preserve the completed value. The proof
compares the full coefficient sequences without requiring identical bounds
or Cauchy moduli. -/
theorem exp_congr {x y : SignedRatio} (same : Equiv x y) : ConstructiveReal.Equiv (exp x) (exp y) :=
  RationalCauchySequence.limit_congr (sequence x) (sequence y) (fun _ =>
    RationalGeometricSeries.block_congr (term x) (term y) (term_congr same) _ _)

theorem exp_eq_small (x : SignedRatio) (small : QProb.LE x.magnitude ⟨1, 2, by decide⟩) :
    ConstructiveReal.Equiv (exp x) (expSmall x small) :=
  RationalCauchySequence.limit_congr (sequence x) (RationalGeometricSeries.sequence (term x) 1 (term_bound x small))
    (fun _ => equiv_refl _)

theorem exp_zero : ConstructiveReal.Equiv (exp zero) ConstructiveReal.one :=
  ConstructiveReal.equiv_trans (exp_eq_small zero (by decide)) expSmall_zero

end Thesis.Probability.RationalExponential
