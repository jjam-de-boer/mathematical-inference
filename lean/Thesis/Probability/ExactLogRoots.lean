import Thesis.Probability.ExactLogWeights

namespace Thesis.Probability.ExactLog

/-- A common-degree exact logarithm, convenient for normalized weighted sums. -/
def root (argument : PositiveRatio) (degree : Nat) (positive : 0 < degree) : ExactLog :=
  ⟨argument, degree, positive⟩

theorem root_one_equiv_zero (degree : Nat) (positive : 0 < degree) : Equiv (root PositiveRatio.one degree positive) zero := by
  change PositiveRatio.Equiv (PositiveRatio.one.pow 1) (PositiveRatio.one.pow degree)
  rw [PositiveRatio.one_pow, PositiveRatio.one_pow]
  exact PositiveRatio.equiv_refl _

theorem root_add_equiv (a b : PositiveRatio) (degree : Nat) (positive : 0 < degree) :
    Equiv (add (root a degree positive) (root b degree positive)) (root (PositiveRatio.mul a b) degree positive) := by
  change PositiveRatio.Equiv ((PositiveRatio.mul (a.pow degree) (b.pow degree)).pow degree)
    ((PositiveRatio.mul a b).pow (degree * degree))
  rw [← PositiveRatio.mul_pow, ← PositiveRatio.pow_mul]
  exact PositiveRatio.equiv_refl _

theorem root_le_zero_iff (a : PositiveRatio) (degree : Nat) (positive : 0 < degree) :
    LE (root a degree positive) zero ↔ PositiveRatio.LE a PositiveRatio.one := by
  simp only [LE, root, zero, PositiveRatio.pow_one, PositiveRatio.one_pow]

theorem zero_le_root_iff (a : PositiveRatio) (degree : Nat) (positive : 0 < degree) :
    LE zero (root a degree positive) ↔ PositiveRatio.LE PositiveRatio.one a := by
  simp only [LE, root, zero, PositiveRatio.pow_one, PositiveRatio.one_pow]

end Thesis.Probability.ExactLog
