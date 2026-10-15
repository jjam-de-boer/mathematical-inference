import Thesis.Probability.SignedRatioAlgebra
import Thesis.Probability.RationalValues

namespace Thesis
namespace Probability
namespace SignedRatio

/-!
# Constructive signs and order for explicit signed rational presentations

Denominators are positive, so nonnegativity is exactly nonnegativity of the
stored integer numerator.  The congruence theorem proves that this sign is
independent of the chosen fraction presentation.  It uses positive integer
multiplication, not normalized `Rat`, a real order, or global propositional
excluded middle.

Squares may be nonnegative even when their base is negative.  Only integer
comparison is split in that proof; certificate producers need not pretend
that every auxiliary polynomial value is a probability.
-/

def Nonnegative (value : SignedRatio) : Prop := 0 ≤ value.num
instance (value : SignedRatio) : Decidable (Nonnegative value) := inferInstanceAs (Decidable (0 ≤ value.num))

theorem nonnegative_zero : Nonnegative zero := Int.le_refl 0
theorem nonnegative_one : Nonnegative one := by decide

theorem nonnegative_congr {left right : SignedRatio} (same : Equiv left right) : Nonnegative left ↔ Nonnegative right := by
  have transfer {first second : SignedRatio} (compared : Equiv first second) (positive : Nonnegative first) : Nonnegative second := by
    have scaled : 0 ≤ first.num * (second.den : Int) := Int.mul_nonneg positive (Int.natCast_nonneg _)
    rw [compared] at scaled
    exact Int.nonneg_of_mul_nonneg_left scaled (by have denominatorPositive := first.den_pos; omega)
  exact ⟨transfer same, transfer (equiv_symm same)⟩

theorem nonnegative_of_equiv_zero {value : SignedRatio} (vanished : Equiv value zero) : Nonnegative value :=
  (nonnegative_congr vanished).mpr nonnegative_zero

theorem nonnegative_add {left right : SignedRatio} (first : Nonnegative left) (second : Nonnegative right) : Nonnegative (add left right) :=
  Int.add_nonneg (Int.mul_nonneg first (Int.natCast_nonneg _)) (Int.mul_nonneg second (Int.natCast_nonneg _))

theorem nonnegative_mul {left right : SignedRatio} (first : Nonnegative left) (second : Nonnegative right) : Nonnegative (mul left right) :=
  Int.mul_nonneg first second

theorem nonnegative_square (value : SignedRatio) : Nonnegative (mul value value) := by
  by_cases positive : 0 ≤ value.num
  · exact Int.mul_nonneg positive positive
  · have nonpositive : value.num ≤ 0 := by omega
    exact Int.mul_nonneg_of_nonpos_of_nonpos nonpositive nonpositive

def LE (left right : SignedRatio) : Prop := Nonnegative (sub right left)
instance (left right : SignedRatio) : Decidable (LE left right) := inferInstanceAs (Decidable (Nonnegative (sub right left)))

theorem le_congr {left left' right right' : SignedRatio} (first : Equiv left left') (second : Equiv right right') :
    LE left right ↔ LE left' right' := nonnegative_congr (add_congr second (neg_congr first))

theorem toSignedRatio_le_iff (left right : QProb) : LE left.toSignedRatio right.toSignedRatio ↔ QProb.LE left right := by
  change 0 ≤ (right.num : Int) * (left.den : Int) + -(left.num : Int) * (right.den : Int) ↔
    left.num * right.den ≤ right.num * left.den
  rw [Int.neg_mul]
  change 0 ≤ (right.num : Int) * (left.den : Int) - (left.num : Int) * (right.den : Int) ↔
    left.num * right.den ≤ right.num * left.den
  rw [Int.sub_nonneg, ← Int.natCast_mul, ← Int.natCast_mul, Int.ofNat_le]

end SignedRatio
end Probability
end Thesis
