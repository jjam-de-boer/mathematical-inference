import Thesis.Probability.Core

namespace Thesis
namespace Probability

/-!
# Unnormalized signed rational presentations for auxiliary algebra

Only the numerator is signed.  Denominators are explicit positive naturals,
and equality is cross-multiplication, just as for `QProb`.  There is no gcd
normalization, quotient representative, real parameter, or chosen witness.
These constructors avoid the forbidden dependency found in the standard
normalized-rational construction during the axiom audit.

This is an auxiliary coefficient type, not a probability record.  Actual
source weights remain natural and normalized.  A negative coefficient can
describe a linear dependence or certificate without becoming an atom weight.
-/

structure SignedRatio where
  num : Int
  den : Nat
  den_pos : 0 < den

namespace SignedRatio

def Equiv (left right : SignedRatio) : Prop := left.num * (right.den : Int) = right.num * (left.den : Int)

instance (left right : SignedRatio) : Decidable (Equiv left right) := by
  unfold Equiv
  infer_instance

def zero : SignedRatio := ⟨0, 1, by decide⟩
def one : SignedRatio := ⟨1, 1, by decide⟩

def add (left right : SignedRatio) : SignedRatio :=
  ⟨left.num * (right.den : Int) + right.num * (left.den : Int), left.den * right.den,
    Nat.mul_pos left.den_pos right.den_pos⟩

def neg (value : SignedRatio) : SignedRatio := ⟨-value.num, value.den, value.den_pos⟩
def sub (left right : SignedRatio) : SignedRatio := add left (neg right)

def mul (left right : SignedRatio) : SignedRatio :=
  ⟨left.num * right.num, left.den * right.den, Nat.mul_pos left.den_pos right.den_pos⟩

theorem equiv_refl (value : SignedRatio) : Equiv value value := rfl
theorem equiv_symm {left right : SignedRatio} (same : Equiv left right) : Equiv right left := same.symm

theorem equiv_trans {first second third : SignedRatio} (left : Equiv first second) (right : Equiv second third) :
    Equiv first third := by
  have cleared : first.num * (third.den : Int) * (second.den : Int) =
      third.num * (first.den : Int) * (second.den : Int) := by
    calc
      _ = (first.num * (second.den : Int)) * (third.den : Int) := by ac_rfl
      _ = (second.num * (first.den : Int)) * (third.den : Int) := by rw [left]
      _ = (second.num * (third.den : Int)) * (first.den : Int) := by ac_rfl
      _ = (third.num * (second.den : Int)) * (first.den : Int) := by rw [right]
      _ = _ := by ac_rfl
  exact Int.eq_of_mul_eq_mul_right (by have positive := second.den_pos; omega) cleared

theorem equiv_zero_iff (value : SignedRatio) : Equiv value zero ↔ value.num = 0 := by
  simp only [Equiv, zero, Int.natCast_one, Int.mul_one, Int.zero_mul]

theorem add_assoc (first second third : SignedRatio) :
    Equiv (add (add first second) third) (add first (add second third)) := by
  simp only [Equiv, add, Int.natCast_mul, Int.add_mul]
  ac_rfl

theorem add_comm (left right : SignedRatio) : Equiv (add left right) (add right left) := by
  simp only [Equiv, add, Int.natCast_mul, Int.add_mul]
  ac_rfl

theorem add_zero (value : SignedRatio) : Equiv (add value zero) value := by
  simp only [Equiv, add, zero, Int.natCast_one, Int.mul_one, Int.zero_mul, Int.add_zero, Nat.mul_one]

theorem mul_add (factor left right : SignedRatio) :
    Equiv (mul factor (add left right)) (add (mul factor left) (mul factor right)) := by
  simp only [Equiv, mul, add, Int.natCast_mul, Int.add_mul, Int.mul_add]
  ac_rfl

end SignedRatio
end Probability
end Thesis
