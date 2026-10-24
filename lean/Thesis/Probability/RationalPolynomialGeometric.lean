import Thesis.Probability.RationalGeometricSeries

namespace Thesis.Probability.RationalGeometricSeries

/-- The polynomial factor from a finite square corner is absorbed by half
of the dyadic exponent. The estimate includes small n and the empty square. -/
theorem square_count_decay (n : Nat) : n * n * 2 ^ (n / 2) ≤ 16 * 2 ^ n := by
  let q := n / 4
  have count : n ≤ 4 * 2 ^ q := by
    have geometric : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
    have rounded : n ≤ 4 * (q + 1) := by dsimp only [q]; omega
    exact Nat.le_trans rounded (Nat.mul_le_mul_left 4 geometric)
  have squared : n * n ≤ 16 * 2 ^ (q + q) := by
    have estimate := Nat.mul_le_mul count count
    have collect : (4 * 2 ^ q) * (4 * 2 ^ q) = 16 * 2 ^ (q + q) := by
      rw [Nat.pow_add, show (16 : Nat) = 4 * 4 from rfl]
      ac_rfl
    rw [collect] at estimate
    exact estimate
  calc
    n * n * 2 ^ (n / 2) ≤ (16 * 2 ^ (q + q)) * 2 ^ (n / 2) := Nat.mul_le_mul_right _ squared
    _ = 16 * 2 ^ (q + q + n / 2) := by rw [Nat.mul_assoc, ← Nat.pow_add]
    _ ≤ 16 * 2 ^ n := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_right (by decide) (by dsimp only [q]; omega))

/-- Explicit decay of the rational corner error `C*n²/2ⁿ`. -/
theorem square_envelope_bound (coefficient n : Nat) :
    QProb.LE (QProb.scale (n * n) (envelope coefficient n)) (envelope (16 * coefficient) (n / 2)) := by
  have estimate := Nat.mul_le_mul_left coefficient (square_count_decay n)
  simpa only [QProb.LE, QProb.scale, envelope, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using estimate

/-- An executable modulus for the polynomial-times-geometric bound. -/
def squareEnvelopeModulus (coefficient : Nat) (precision : PositiveRatio) : Nat :=
  2 * ((16 * coefficient * precision.den).log2 + 1)

theorem square_envelope_small (coefficient : Nat) (precision : PositiveRatio) (n : Nat)
    (later : squareEnvelopeModulus coefficient precision ≤ n) :
    QProb.LE (QProb.scale (n * n) (envelope coefficient n)) precision.toQProb := by
  have exponent : (2 * (8 * coefficient) * precision.den).log2 + 1 ≤ n / 2 := by
    have same : 2 * (8 * coefficient) = 16 * coefficient := by omega
    rw [same]
    dsimp only [squareEnvelopeModulus] at later
    omega
  have small := envelope_small (8 * coefficient) precision (n / 2) exponent
  have same : 2 * (8 * coefficient) = 16 * coefficient := by omega
  rw [same] at small
  exact QProb.le_trans (square_envelope_bound coefficient n) small

end Thesis.Probability.RationalGeometricSeries
