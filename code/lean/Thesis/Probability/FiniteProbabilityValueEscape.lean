import Thesis.Probability.Core

namespace Thesis.Probability.QProb

/-!
# A rational probability outside any supplied finite value catalogue

Finite outcome alphabets do not make rational probability parameters finite.
For a supplied list of fractions, take the unit fraction whose denominator
is one greater than the sum of their displayed denominators. If it equalled
a listed fraction with positive numerator, that listed denominator would
already be at least this larger number; a zero numerator cannot equal it.

The construction respects unreduced fraction presentations and returns the
new value as data. It is not an undecidability theorem and does not exclude
procedures needing only one feasible point or two disagreement witnesses.
-/

private def denominatorSum : List QProb → Nat
  | [] => 0
  | value :: rest => value.den + denominatorSum rest

private theorem denominator_le_sum (values : List QProb) (value : QProb) (member : value ∈ values) :
    value.den ≤ denominatorSum values := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · cases same
        exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih later) (Nat.le_add_left _ _)

/-- An actual unit-interval rational value outside every entry, without a
denominator search, normalization, choice or excluded-middle decision. -/
def outsideFiniteCatalogue (values : List QProb) :
    {value : QProb // LE value one ∧ ∀ listed ∈ values, ¬ Equiv value listed} := by
  let value : QProb := ⟨1, denominatorSum values + 1, by omega⟩
  refine ⟨value, ?_, ?_⟩
  · change 1 * 1 ≤ 1 * (denominatorSum values + 1)
    omega
  · intro listed member same
    have bounded := denominator_le_sum values listed member
    have positive := listed.den_pos
    change 1 * listed.den = listed.num * (denominatorSum values + 1) at same
    rw [Nat.one_mul] at same
    have numeratorPositive : 1 ≤ listed.num := by
      by_cases zero : listed.num = 0
      · rw [zero, Nat.zero_mul] at same
        omega
      · omega
    have scaled := Nat.mul_le_mul_right (denominatorSum values + 1) numeratorPositive
    rw [Nat.one_mul, ← same] at scaled
    omega

end Thesis.Probability.QProb
