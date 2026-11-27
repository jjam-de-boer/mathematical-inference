import Thesis.Probability.RationalSquareObstruction

namespace Thesis.Probability.PellHalfRates

/-!
# Arbitrarily small positive rates certified by an equality

The equation d² + 2s² = 1 excludes d = 0 over the rationals because that
would require a rational square root of one half. Nevertheless its
positive rational solutions approach d = 0. The explicit Pell recurrence
supplies them using only natural arithmetic. This is how a list of ties
can enforce a nonzero common denominator for unbounded rational variables.
-/

/-- Pell pairs starting at (1,0). Each iteration multiplies the formal
quantity A + B√2 by 3 + 2√2, whose norm is one. -/
def pair : Nat → Nat × Nat
  | 0 => (1, 0)
  | step + 1 =>
    let previous := pair step
    (3 * previous.1 + 4 * previous.2, 2 * previous.1 + 3 * previous.2)

private theorem norm_step (a b : Nat) (norm : a * a = 2 * (b * b) + 1) :
    (3 * a + 4 * b) * (3 * a + 4 * b) =
      2 * ((2 * a + 3 * b) * (2 * a + 3 * b)) + 1 := by
  simp only [Nat.add_mul, Nat.mul_add]
  simp only [QProb.mul_reorder_four 3 a 3 a, QProb.mul_reorder_four 3 a 4 b,
    QProb.mul_reorder_four 4 b 3 a, QProb.mul_reorder_four 4 b 4 b,
    QProb.mul_reorder_four 2 a 2 a, QProb.mul_reorder_four 2 a 3 b,
    QProb.mul_reorder_four 3 b 2 a, QProb.mul_reorder_four 3 b 3 b, Nat.mul_comm b a]
  omega

/-- Writing the norm identity without natural subtraction lets both sides
be used directly after clearing the common denominator of the rates. -/
theorem norm (step : Nat) : (pair step).1 * (pair step).1 = 2 * ((pair step).2 * (pair step).2) + 1 := by
  induction step with
  | zero => decide
  | succ step ih => exact norm_step (pair step).1 (pair step).2 ih

theorem lower_bound (step : Nat) : step + 1 ≤ (pair step).1 := by
  induction step with
  | zero => decide
  | succ step ih =>
    change step + 1 + 1 ≤ 3 * (pair step).1 + 4 * (pair step).2
    omega

/-- The denominator of each explicit rational witness is positive. -/
theorem denominator_pos (step : Nat) : 0 < (pair step).1 := by
  have bound := lower_bound step
  omega

/-- The two fractions associated with a Pell pair, in the same denominator. -/
def denominatorRate (step : Nat) : QProb := ⟨1, (pair step).1, denominator_pos step⟩
def companionRate (step : Nat) : QProb := ⟨(pair step).2, (pair step).1, denominator_pos step⟩

theorem denominatorRate_le_one (step : Nat) : (denominatorRate step).LE .one := by
  have positive := denominator_pos step
  change 1 * 1 ≤ 1 * (pair step).1
  omega

theorem companionRate_le_one (step : Nat) : (companionRate step).LE .one := by
  change (pair step).2 * 1 ≤ 1 * (pair step).1
  simp only [Nat.mul_one, Nat.one_mul]
  by_cases ordered : (pair step).2 ≤ (pair step).1
  · exact ordered
  · have squared := Nat.mul_le_mul (show (pair step).1 ≤ (pair step).2 by omega)
      (show (pair step).1 ≤ (pair step).2 by omega)
    have normEquation := norm step
    omega

/-- Direct exact verification of the normalization equation. -/
theorem equation (step : Nat) : QProb.Equiv
    (QProb.add (QProb.mul (denominatorRate step) (denominatorRate step))
      (QProb.scale 2 (QProb.mul (companionRate step) (companionRate step)))) QProb.one := by
  have same := norm step
  simp only [QProb.Equiv, QProb.mul, QProb.add, QProb.scale, QProb.one, denominatorRate, companionRate,
    Nat.mul_one, Nat.one_mul]
  let a := (pair step).1
  let b := (pair step).2
  change a * a + 2 * (b * b) * (a * a) = a * a * (a * a)
  calc
    _ = (2 * (b * b) + 1) * (a * a) := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    _ = _ := congrArg (fun value => value * (a * a)) same.symm

/-- The family eventually lies below any prescribed positive rational
threshold. This needs no limiting real-valued witness. -/
theorem eventually_small (threshold : QProb) (positive : 0 < threshold.num) :
    ∃ step, QProb.LT (denominatorRate step) threshold := by
  refine ⟨threshold.den, ?_⟩
  have bound := lower_bound threshold.den
  change 1 * threshold.den < threshold.num * (pair threshold.den).1
  simp only [Nat.one_mul]
  calc
    threshold.den < (pair threshold.den).1 := by omega
    _ ≤ threshold.num * (pair threshold.den).1 := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right (pair threshold.den).1 (show 1 ≤ threshold.num from positive)

/-- A rational solution to the same equation cannot have zero denominator
rate. A zero first coordinate would give a rational square of one half. -/
theorem positive_of_equation (d s : QProb) (same :
    ((d.mul d).add (QProb.scale 2 (s.mul s))).Equiv .one) : 0 < d.num := by
  by_cases vanished : d.num = 0
  · simp only [QProb.Equiv, QProb.add, QProb.mul, QProb.scale, QProb.one,
      vanished, Nat.zero_mul, Nat.zero_add, Nat.mul_one, Nat.one_mul] at same
    have cleared : (2 * (s.num * s.num)) * (d.den * d.den) = (s.den * s.den) * (d.den * d.den) := by
      simpa only [Nat.mul_comm (s.den * s.den) (d.den * d.den)] using same
    exact (RationalSquareObstruction.twice_square_ne_square _ _ s.den_pos
      (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos d.den_pos d.den_pos) cleared)).elim
  · omega

end Thesis.Probability.PellHalfRates
