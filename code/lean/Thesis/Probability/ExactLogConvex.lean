import Thesis.Probability.ExactLogLinear

namespace Thesis.Probability.ExactLog

theorem add_le_add_left_iff (x y z : ExactLog) : LE (add z x) (add z y) ↔ LE x y := by
  rw [le_congr (add_comm z x) (add_comm z y)]
  exact add_le_add_right_iff x y z

theorem add_le_add {a b c d : ExactLog} (first : LE a b) (second : LE c d) : LE (add a c) (add b d) :=
  le_trans ((add_le_add_right_iff a b c).mpr first) ((add_le_add_left_iff c d b).mpr second)

theorem scaleRatio_le_scaleRatio_iff (q : QProb) (positive : 0 < q.num) (x y : ExactLog) :
    LE (scaleRatio q x) (scaleRatio q y) ↔ LE x y := by
  change LE (divideNat (scaleNat q.num x) q.den q.den_pos)
    (divideNat (scaleNat q.num y) q.den q.den_pos) ↔ _
  rw [divideNat_le_divideNat_iff, scaleNat_le_scaleNat_iff q.num positive]

theorem scaleRatio_equiv_iff (q : QProb) (positive : 0 < q.num) (x y : ExactLog) :
    Equiv (scaleRatio q x) (scaleRatio q y) ↔ Equiv x y := by
  rw [equiv_iff_le, equiv_iff_le, scaleRatio_le_scaleRatio_iff q positive,
    scaleRatio_le_scaleRatio_iff q positive]

/-- Equality in the sum of two upper bounds forces equality in each bound. -/
theorem equiv_of_add_equiv {a b c d : ExactLog} (first : LE a c) (second : LE b d)
    (equal : Equiv (add a b) (add c d)) : Equiv a c := by
  have compared := (add_le_add_left_iff b d a).mpr second
  have reverse : LE (add c d) (add a d) := (le_congr equal (equiv_refl _)).mp compared
  exact (equiv_iff_le _ _).mpr ⟨first, (add_le_add_right_iff c a d).mp reverse⟩

theorem convexPair_constant (left right : Nat) (positive : 0 < left + right) (x : ExactLog) :
    Equiv (add (scaleRatio ⟨left, left + right, positive⟩ x) (scaleRatio ⟨right, left + right, positive⟩ x)) x := by
  have normalized : QProb.Equiv (QProb.add ⟨left, left + right, positive⟩ ⟨right, left + right, positive⟩) QProb.one := by
    change (left * (left + right) + right * (left + right)) * 1 = 1 * ((left + right) * (left + right))
    rw [← Nat.add_mul, Nat.mul_one, Nat.one_mul]
  have constant := scaleRatio_weight_congr normalized x
  rw [scaleRatio_one] at constant
  exact equiv_trans (equiv_symm (scaleRatio_add_weight _ _ x)) constant

end Thesis.Probability.ExactLog
