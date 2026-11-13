import Thesis.Probability.Core

namespace Thesis.Probability.RationalSquareObstruction

/-- Finite residue checking supplies divisibility by thirteen from square
divisibility. Only the thirteen natural residues are decided. -/
private theorem square_mod_thirteen (value : Nat) (vanished : (value * value) % 13 = 0) : value % 13 = 0 := by
  have residues : ∀ residue : Fin 13, (residue.val * residue.val) % 13 = 0 → residue.val = 0 := by decide +kernel
  apply residues ⟨value % 13, Nat.mod_lt value (by decide)⟩
  rw [Nat.mul_mod] at vanished
  exact vanished

private theorem divisible_of_thirteen_square (numerator denominator : Nat)
    (same : 13 * (numerator * numerator) = denominator * denominator) : denominator % 13 = 0 :=
  square_mod_thirteen denominator (by rw [← same]; exact Nat.mul_mod_right 13 (numerator * numerator))

private theorem thirteen_descent (denominator : Nat) :
    ∀ numerator, 0 < denominator → 13 * (numerator * numerator) ≠ denominator * denominator := by
  induction denominator using Nat.strongRecOn with
  | ind denominator inductionHypothesis =>
      intro numerator positive same
      have denominatorDivisible := divisible_of_thirteen_square numerator denominator same
      have denominatorSplit : denominator = 13 * (denominator / 13) := by omega
      have numeratorSquare : numerator * numerator = 13 * ((denominator / 13) * (denominator / 13)) := by
        apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 13)
        calc
          13 * (numerator * numerator) = denominator * denominator := same
          _ = (13 * (denominator / 13)) * (13 * (denominator / 13)) := by rw [← denominatorSplit]
          _ = 13 * (13 * ((denominator / 13) * (denominator / 13))) := by ac_rfl
      have numeratorDivisible := divisible_of_thirteen_square (denominator / 13) numerator numeratorSquare.symm
      have numeratorSplit : numerator = 13 * (numerator / 13) := by omega
      have smallerSquare : 13 * ((numerator / 13) * (numerator / 13)) = (denominator / 13) * (denominator / 13) := by
        apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 13)
        calc
          13 * (13 * ((numerator / 13) * (numerator / 13))) = (13 * (numerator / 13)) * (13 * (numerator / 13)) := by ac_rfl
          _ = numerator * numerator := by rw [← numeratorSplit]
          _ = 13 * ((denominator / 13) * (denominator / 13)) := numeratorSquare
      exact inductionHypothesis (denominator / 13) (Nat.div_lt_self positive (by decide))
        (numerator / 13) (by omega) smallerSquare

/-- No common-denominator rational square equals thirteen. The denominator
is arbitrary, without normalization, coprimality, or a lowest-terms choice.
This is the discriminant obstruction for the three-state mean-half optimum. -/
theorem square_ne_thirteen (numerator denominator : Nat) (positive : 0 < denominator) :
    numerator * numerator ≠ 13 * (denominator * denominator) := by
  intro same
  have productPositive : 0 < 13 * (denominator * denominator) := Nat.mul_pos (by decide) (Nat.mul_pos positive positive)
  have numeratorPositive : 0 < numerator := by
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero, Nat.zero_mul] at same
    omega
  exact thirteen_descent numerator denominator numeratorPositive same.symm

end Thesis.Probability.RationalSquareObstruction

namespace Thesis.Probability.QProb

/-- Thirteen has no rational square root in the existing probability-value
arithmetic, even when numerator and denominator are unreduced. -/
theorem square_ne_thirteen (value : QProb) : ¬ Equiv (mul value value) (ofNat 13) := by
  intro same
  change (value.num * value.num) * 1 = 13 * (value.den * value.den) at same
  exact RationalSquareObstruction.square_ne_thirteen value.num value.den value.den_pos (by simpa only [Nat.mul_one] using same)

end Thesis.Probability.QProb
