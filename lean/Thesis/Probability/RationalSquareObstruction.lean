import Thesis.Probability.Core

namespace Thesis.Probability

/-!
# A rational square obstruction by finite arithmetic descent

No natural fraction with positive denominator has square one half. The proof
does not normalize fractions, choose a lowest-terms representative, or import
real numbers. If `2*a*a = b*b`, parity makes both `a` and `b` even; dividing
both by two produces the same equation with a strictly smaller positive
denominator. Strong induction on that supplied denominator closes the descent.

This elementary obstruction is useful when checking rational feasibility of
finite probability templates. It says nothing by itself about decidability
of general rational polynomial constraints or graph-wide identification.
-/

namespace RationalSquareObstruction

private theorem square_mod_two (value : Nat) : (value * value) % 2 = value % 2 := by
  rw [Nat.mul_mod]
  have alternatives : value % 2 = 0 ∨ value % 2 = 1 := by omega
  rcases alternatives with remainder | remainder <;> rw [remainder] <;> decide

private theorem even_of_twice_square (numerator denominator : Nat)
    (same : 2 * (numerator * numerator) = denominator * denominator) : denominator % 2 = 0 := by
  calc
    denominator % 2 = (denominator * denominator) % 2 := (square_mod_two denominator).symm
    _ = (2 * (numerator * numerator)) % 2 := congrArg (fun value => value % 2) same.symm
    _ = 0 := Nat.mul_mod_right 2 (numerator * numerator)

private theorem descent (denominator : Nat) :
    ∀ numerator, 0 < denominator → 2 * (numerator * numerator) ≠ denominator * denominator := by
  induction denominator using Nat.strongRecOn with
  | ind denominator inductionHypothesis =>
      intro numerator positive same
      have denominatorEven := even_of_twice_square numerator denominator same
      have denominatorSplit : denominator = 2 * (denominator / 2) := by omega
      have numeratorSquare : numerator * numerator = 2 * ((denominator / 2) * (denominator / 2)) := by
        apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
        calc
          2 * (numerator * numerator) = denominator * denominator := same
          _ = (2 * (denominator / 2)) * (2 * (denominator / 2)) := by rw [← denominatorSplit]
          _ = 2 * (2 * ((denominator / 2) * (denominator / 2))) := by ac_rfl
      have numeratorEven := even_of_twice_square (denominator / 2) numerator numeratorSquare.symm
      have numeratorSplit : numerator = 2 * (numerator / 2) := by omega
      have smallerSquare : 2 * ((numerator / 2) * (numerator / 2)) = (denominator / 2) * (denominator / 2) := by
        apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
        calc
          2 * (2 * ((numerator / 2) * (numerator / 2))) = (2 * (numerator / 2)) * (2 * (numerator / 2)) := by ac_rfl
          _ = numerator * numerator := by rw [← numeratorSplit]
          _ = 2 * ((denominator / 2) * (denominator / 2)) := numeratorSquare
      exact inductionHypothesis (denominator / 2) (Nat.div_lt_self positive (by decide))
        (numerator / 2) (by omega) smallerSquare

/-- The denominator need not be reduced or coprime to the numerator. -/
theorem twice_square_ne_square (numerator denominator : Nat) (positive : 0 < denominator) :
    2 * (numerator * numerator) ≠ denominator * denominator := descent denominator numerator positive

end RationalSquareObstruction

namespace QProb

/-- A direct obstruction in the library's own cross-multiplication semantics,
with no appeal to normalized rationals or an irrational-probability extension. -/
theorem square_ne_half (value : QProb) : ¬ Equiv (mul value value) ⟨1, 2, by decide⟩ := by
  intro same
  change (value.num * value.num) * 2 = 1 * (value.den * value.den) at same
  apply RationalSquareObstruction.twice_square_ne_square value.num value.den value.den_pos
  simpa only [Nat.mul_comm, Nat.one_mul, Nat.mul_one] using same

end QProb
end Thesis.Probability
