import Thesis.Probability.PositiveRatio
import Thesis.Probability.Distros.RationalLinearOrder

namespace Thesis.Probability
namespace PositiveRatio

/-- A positive rational precision, interpreted as an auxiliary signed value. -/
def toSignedRatio (value : PositiveRatio) : SignedRatio := value.toQProb.toSignedRatio

def half (value : PositiveRatio) : PositiveRatio :=
  ⟨value.num, value.den * 2, value.num_pos, Nat.mul_pos value.den_pos (by decide)⟩

theorem signed_nonnegative (value : PositiveRatio) : SignedRatio.Nonnegative value.toSignedRatio :=
  Int.natCast_nonneg _

theorem half_add_half (value : PositiveRatio) :
    SignedRatio.Equiv (SignedRatio.add value.half.toSignedRatio value.half.toSignedRatio) value.toSignedRatio := by
  change (((value.num : Int) * ((value.den * 2 : Nat) : Int) +
    (value.num : Int) * ((value.den * 2 : Nat) : Int)) * (value.den : Int)) =
    (value.num : Int) * (((value.den * 2) * (value.den * 2) : Nat) : Int)
  simp only [Int.natCast_mul]
  have timesTwo (x : Int) : x * 2 = x + x := by
    rw [Int.mul_comm]
    exact Int.two_mul x
  have castTwo : ((2 : Nat) : Int) = 2 := rfl
  simp only [castTwo, timesTwo, Int.mul_add, Int.add_mul]
  ac_rfl


end PositiveRatio

namespace SignedRatio

/-- Adding the same rational to both sides preserves and reflects order. -/
theorem add_le_add_right_iff (a b c : SignedRatio) : LE (add a c) (add b c) ↔ LE a b := by
  have same : Equiv (sub (add b c) (add a c)) (sub b a) := by
    simp only [Equiv, sub, add, neg, Int.natCast_mul, Int.mul_add,
      Int.neg_add, Int.mul_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega
  exact nonnegative_congr same

/-- Reflection of a narrow interval under negation. -/
theorem neg_le_add_iff (a b c : SignedRatio) : LE (neg a) (add (neg b) c) ↔ LE b (add a c) := by
  have same : Equiv (sub (add (neg b) c) (neg a)) (sub (add a c) b) := by
    simp only [Equiv, sub, add, neg, Int.natCast_mul, Int.mul_add,
      Int.neg_neg, Int.mul_neg, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega
  exact nonnegative_congr same

theorem sub_le_zero_iff (a b : SignedRatio) : LE (sub a b) zero ↔ LE a b := by
  rw [le_iff_cross, le_iff_cross]
  simp only [sub, add, neg, zero, Int.natCast_one, Int.mul_one, Int.zero_mul, Int.neg_mul]
  constructor <;> intro bounded <;> omega

theorem zero_le_sub_iff (a b : SignedRatio) : LE zero (sub a b) ↔ LE b a := by
  rw [le_iff_cross, le_iff_cross]
  simp only [sub, add, neg, zero, Int.natCast_one, Int.mul_one, Int.zero_mul, Int.neg_mul]
  constructor <;> intro bounded <;> omega

/-- Rational order is closed under arbitrarily small explicit positive error.
The separating precision is computed from the two stored denominators. -/
theorem le_of_forall_add_positive (a b : SignedRatio)
    (bounded : ∀ error : PositiveRatio, LE a (add b error.toSignedRatio)) : LE a b := by
  let error : PositiveRatio := ⟨1, 2 * (a.den * b.den), by decide,
    Nat.mul_pos (by decide) (Nat.mul_pos a.den_pos b.den_pos)⟩
  have compared := (le_iff_cross _ _).mp (bounded error)
  change a.num * ((b.den * (2 * (a.den * b.den)) : Nat) : Int) ≤
    (b.num * ((2 * (a.den * b.den) : Nat) : Int) + 1 * (b.den : Int)) * (a.den : Int) at compared
  have left : a.num * ((b.den * (2 * (a.den * b.den)) : Nat) : Int) =
      (2 * (a.num * (b.den : Int))) * ((a.den : Int) * (b.den : Int)) := by
    simp only [Int.natCast_mul]
    ac_rfl
  have right : (b.num * ((2 * (a.den * b.den) : Nat) : Int) + 1 * (b.den : Int)) * (a.den : Int) =
      (2 * (b.num * (a.den : Int)) + 1) * ((a.den : Int) * (b.den : Int)) := by
    simp only [Int.natCast_mul, Int.add_mul, Int.one_mul]
    ac_rfl
  rw [left, right] at compared
  have positive : 0 < (a.den : Int) * (b.den : Int) :=
    Int.mul_pos (by have h := a.den_pos; omega) (by have h := b.den_pos; omega)
  have canceled := (Int.mul_le_mul_right positive).mp compared
  apply (le_iff_cross _ _).mpr
  omega

end SignedRatio
end Thesis.Probability
