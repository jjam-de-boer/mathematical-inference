import Thesis.Probability.Core

namespace Thesis.Probability

/-- A strictly positive rational, with explicit unreduced natural weights.
This auxiliary value is not a probability law and has no upper bound. -/
structure PositiveRatio where
  num : Nat
  den : Nat
  num_pos : 0 < num
  den_pos : 0 < den

namespace PositiveRatio

def toQProb (x : PositiveRatio) : QProb := ⟨x.num, x.den, x.den_pos⟩
def Equiv (x y : PositiveRatio) : Prop := QProb.Equiv x.toQProb y.toQProb
def LE (x y : PositiveRatio) : Prop := QProb.LE x.toQProb y.toQProb
instance (x y : PositiveRatio) : Decidable (Equiv x y) := inferInstanceAs (Decidable (x.num * y.den = y.num * x.den))
instance (x y : PositiveRatio) : Decidable (LE x y) := inferInstanceAs (Decidable (x.num * y.den ≤ y.num * x.den))

def one : PositiveRatio := ⟨1, 1, Nat.zero_lt_one, Nat.zero_lt_one⟩
def ofNat (n : Nat) (positive : 0 < n) : PositiveRatio := ⟨n, 1, positive, Nat.zero_lt_one⟩
def mul (x y : PositiveRatio) : PositiveRatio :=
  ⟨x.num * y.num, x.den * y.den, Nat.mul_pos x.num_pos y.num_pos, Nat.mul_pos x.den_pos y.den_pos⟩
def inv (x : PositiveRatio) : PositiveRatio := ⟨x.den, x.num, x.den_pos, x.num_pos⟩
def pow (x : PositiveRatio) (n : Nat) : PositiveRatio :=
  ⟨x.num ^ n, x.den ^ n, Nat.pow_pos x.num_pos, Nat.pow_pos x.den_pos⟩

theorem ext {x y : PositiveRatio} (numerator : x.num = y.num) (denominator : x.den = y.den) : x = y := by
  cases x; cases y; simp_all

theorem equiv_refl (x : PositiveRatio) : Equiv x x := rfl
theorem equiv_symm {x y : PositiveRatio} (same : Equiv x y) : Equiv y x := same.symm
theorem equiv_trans {x y z : PositiveRatio} (first : Equiv x y) (second : Equiv y z) : Equiv x z :=
  QProb.equiv_trans first second

theorem le_refl (x : PositiveRatio) : LE x x := Nat.le_refl _
theorem le_trans {x y z : PositiveRatio} (first : LE x y) (second : LE y z) : LE x z :=
  QProb.le_trans first second

theorem le_congr {x x' y y' : PositiveRatio} (first : Equiv x x') (second : Equiv y y') :
    LE x y ↔ LE x' y' :=
  ⟨QProb.le_congr first second, QProb.le_congr (QProb.equiv_symm first) (QProb.equiv_symm second)⟩

theorem le_antisymm {x y : PositiveRatio} (first : LE x y) (second : LE y x) : Equiv x y :=
  Nat.le_antisymm first second

theorem le_total (x y : PositiveRatio) : LE x y ∨ LE y x := Nat.le_total _ _

theorem mul_congr {x x' y y' : PositiveRatio} (first : Equiv x x') (second : Equiv y y') :
    Equiv (mul x y) (mul x' y') := QProb.mul_congr first second

theorem inv_congr {x y : PositiveRatio} (same : Equiv x y) : Equiv (inv x) (inv y) := by
  change x.den * y.num = y.den * x.num
  change x.num * y.den = y.num * x.den at same
  simpa only [Nat.mul_comm] using same.symm

theorem pow_congr {x y : PositiveRatio} (same : Equiv x y) (n : Nat) : Equiv (pow x n) (pow y n) := by
  change x.num ^ n * y.den ^ n = y.num ^ n * x.den ^ n
  simpa only [Nat.mul_pow] using congrArg (fun value => value ^ n) same

theorem pow_le_pow_iff (x y : PositiveRatio) (n : Nat) (positive : 0 < n) :
    LE (pow x n) (pow y n) ↔ LE x y := by
  change x.num ^ n * y.den ^ n ≤ y.num ^ n * x.den ^ n ↔ x.num * y.den ≤ y.num * x.den
  rw [← Nat.mul_pow, ← Nat.mul_pow]
  exact Nat.pow_le_pow_iff_left (Nat.ne_of_gt positive)

theorem pow_equiv_pow_iff (x y : PositiveRatio) (n : Nat) (positive : 0 < n) :
    Equiv (pow x n) (pow y n) ↔ Equiv x y := by
  change x.num ^ n * y.den ^ n = y.num ^ n * x.den ^ n ↔ x.num * y.den = y.num * x.den
  rw [← Nat.mul_pow, ← Nat.mul_pow]
  exact Nat.pow_left_inj (Nat.ne_of_gt positive)

theorem one_pow (n : Nat) : pow one n = one := by apply ext <;> simp [pow, one]

theorem pow_zero (x : PositiveRatio) : pow x 0 = one := by apply ext <;> rfl
theorem pow_one (x : PositiveRatio) : pow x 1 = x := by apply ext <;> simp [pow]
theorem pow_mul (x : PositiveRatio) (m n : Nat) : pow x (m * n) = pow (pow x m) n := by
  apply ext <;> simp only [pow, Nat.pow_mul]
theorem pow_comm (x : PositiveRatio) (m n : Nat) : pow (pow x m) n = pow (pow x n) m := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm m n]

theorem mul_pow (x y : PositiveRatio) (n : Nat) : pow (mul x y) n = mul (pow x n) (pow y n) := by
  apply ext <;> simp only [pow, mul, Nat.mul_pow]

theorem pow_add (x : PositiveRatio) (m n : Nat) : pow x (m + n) = mul (pow x m) (pow x n) := by
  apply ext <;> simp only [pow, mul, Nat.pow_add]

theorem mul_assoc (x y z : PositiveRatio) : mul (mul x y) z = mul x (mul y z) := by
  apply ext <;> simp only [mul, Nat.mul_assoc]
theorem mul_comm (x y : PositiveRatio) : mul x y = mul y x := by
  apply ext <;> simp only [mul, Nat.mul_comm]
theorem mul_one (x : PositiveRatio) : mul x one = x := by apply ext <;> simp [mul, one]
theorem one_mul (x : PositiveRatio) : mul one x = x := by rw [mul_comm, mul_one]

theorem mul_inv (x : PositiveRatio) : Equiv (mul x (inv x)) one := by
  change (x.num * x.den) * 1 = 1 * (x.den * x.num)
  simp only [Nat.mul_one, Nat.mul_comm]

theorem inv_inv (x : PositiveRatio) : inv (inv x) = x := by apply ext <;> rfl
theorem inv_mul (x y : PositiveRatio) : inv (mul x y) = mul (inv x) (inv y) := by apply ext <;> rfl
theorem inv_pow (x : PositiveRatio) (n : Nat) : inv (pow x n) = pow (inv x) n := by apply ext <;> rfl

theorem inv_le_inv_iff (x y : PositiveRatio) : LE (inv x) (inv y) ↔ LE y x := by
  change x.den * y.num ≤ y.den * x.num ↔ y.num * x.den ≤ x.num * y.den
  simp only [Nat.mul_comm]

/-- Multiplication by a positive rational preserves and reflects order. -/
theorem mul_le_mul_left_iff (factor x y : PositiveRatio) : LE (mul factor x) (mul factor y) ↔ LE x y := by
  change (factor.num * x.num) * (factor.den * y.den) ≤ (factor.num * y.num) * (factor.den * x.den) ↔
    x.num * y.den ≤ y.num * x.den
  have left : (factor.num * x.num) * (factor.den * y.den) = (factor.num * factor.den) * (x.num * y.den) := by ac_rfl
  have right : (factor.num * y.num) * (factor.den * x.den) = (factor.num * factor.den) * (y.num * x.den) := by ac_rfl
  rw [left, right]
  exact Nat.mul_le_mul_left_iff (Nat.mul_pos factor.num_pos factor.den_pos)

theorem mul_le_mul {a b c d : PositiveRatio} (first : LE a b) (second : LE c d) : LE (mul a c) (mul b d) := by
  apply le_trans ((mul_le_mul_left_iff c a b).mpr first |> fun h => by simpa only [mul_comm] using h)
  exact (mul_le_mul_left_iff b c d).mpr second

end PositiveRatio
end Thesis.Probability
