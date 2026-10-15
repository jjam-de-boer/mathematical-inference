import Thesis.Probability.SignedRatioFiniteSum

namespace Thesis
namespace Probability
namespace SignedRatio

/-!
# Finite exact algebra for polynomial evaluation

Polynomial coefficients and intermediate values are explicit signed rational
presentations.  These identities use cross-multiplication, positive stored
denominators and finite sums; there is no normalization to a chosen rational
representative.  Negative values are auxiliary algebra, never negative
probability weights.

The finite-sum laws are stated up to `Equiv`, just like the existing probability
core.  This makes a polynomial certificate insensitive to unreduced fraction
presentations while keeping every equality check executable in the kernel.
-/

theorem zero_add (value : SignedRatio) : Equiv (add zero value) value :=
  equiv_trans (add_comm zero value) (add_zero value)

theorem add_left_comm (first second third : SignedRatio) :
    Equiv (add first (add second third)) (add second (add first third)) := by
  simp only [Equiv, add, Int.natCast_mul, Int.add_mul, Int.mul_add]
  ac_rfl

theorem add_interchange (first second third fourth : SignedRatio) :
    Equiv (add (add first second) (add third fourth)) (add (add first third) (add second fourth)) := by
  simp only [Equiv, add, Int.natCast_mul, Int.add_mul, Int.mul_add]
  ac_rfl

theorem mul_comm (left right : SignedRatio) : Equiv (mul left right) (mul right left) := by
  simp only [Equiv, mul, Int.natCast_mul]
  ac_rfl

theorem mul_assoc (first second third : SignedRatio) :
    Equiv (mul (mul first second) third) (mul first (mul second third)) := by
  simp only [Equiv, mul, Int.natCast_mul]
  ac_rfl

theorem mul_one (value : SignedRatio) : Equiv (mul value one) value := by
  simp only [Equiv, mul, one, Int.natCast_one, Int.mul_one]

theorem one_mul (value : SignedRatio) : Equiv (mul one value) value :=
  equiv_trans (mul_comm one value) (mul_one value)

theorem mul_zero (value : SignedRatio) : Equiv (mul value zero) zero := by
  simp only [Equiv, mul, zero, Int.natCast_one, Int.mul_zero, Int.zero_mul]

theorem zero_mul (value : SignedRatio) : Equiv (mul zero value) zero :=
  equiv_trans (mul_comm zero value) (mul_zero value)

theorem add_mul (left right factor : SignedRatio) :
    Equiv (mul (add left right) factor) (add (mul left factor) (mul right factor)) := by
  simp only [Equiv, mul, add, Int.natCast_mul, Int.add_mul, Int.mul_add]
  ac_rfl

theorem mul_interchange (first second third fourth : SignedRatio) :
    Equiv (mul (mul first second) (mul third fourth)) (mul (mul first third) (mul second fourth)) := by
  simp only [Equiv, mul, Int.natCast_mul]
  ac_rfl

theorem neg_congr {left right : SignedRatio} (same : Equiv left right) : Equiv (neg left) (neg right) := by
  change -left.num * (right.den : Int) = -right.num * (left.den : Int)
  rw [Int.neg_mul, Int.neg_mul, same]

theorem neg_add (left right : SignedRatio) : Equiv (neg (add left right)) (add (neg left) (neg right)) := by
  simp only [Equiv, neg, add, Int.neg_add, Int.neg_mul]

theorem neg_mul (left right : SignedRatio) : Equiv (mul (neg left) right) (neg (mul left right)) := by
  simp only [Equiv, neg, mul, Int.neg_mul]

theorem sub_equiv_zero_iff (left right : SignedRatio) : Equiv (sub left right) zero ↔ Equiv left right := by
  rw [equiv_zero_iff]
  change left.num * (right.den : Int) + -right.num * (left.den : Int) = 0 ↔
    left.num * (right.den : Int) = right.num * (left.den : Int)
  rw [Int.neg_mul]
  omega

theorem listSum_append (left right : List SignedRatio) :
    Equiv (listSum (left ++ right)) (add (listSum left) (listSum right)) := by
  induction left with
  | nil => exact equiv_symm (zero_add _)
  | cons value rest inductionHypothesis =>
      exact equiv_trans (add_congr (equiv_refl _) inductionHypothesis)
        (equiv_symm (add_assoc value (listSum rest) (listSum right)))

theorem listSum_map_add (values : List α) (left right : α → SignedRatio) :
    Equiv (listSum (values.map fun value => add (left value) (right value)))
      (add (listSum (values.map left)) (listSum (values.map right))) := by
  induction values with
  | nil => exact equiv_symm (add_zero zero)
  | cons value rest inductionHypothesis =>
      exact equiv_trans (add_congr (equiv_refl _) inductionHypothesis)
        (add_interchange (left value) (right value) _ _)

theorem mul_listSum (factor : SignedRatio) (values : List SignedRatio) :
    Equiv (mul factor (listSum values)) (listSum (values.map (mul factor))) := by
  induction values with
  | nil => exact mul_zero factor
  | cons value rest inductionHypothesis =>
      exact equiv_trans (mul_add factor value (listSum rest)) (add_congr (equiv_refl _) inductionHypothesis)

theorem listSum_mul (values : List SignedRatio) (factor : SignedRatio) :
    Equiv (mul (listSum values) factor) (listSum (values.map fun value => mul value factor)) := by
  induction values with
  | nil => exact zero_mul factor
  | cons value rest inductionHypothesis =>
      exact equiv_trans (add_mul value (listSum rest) factor) (add_congr (equiv_refl _) inductionHypothesis)

theorem listSum_flatMap (values : List α) (family : α → List SignedRatio) :
    Equiv (listSum (values.flatMap family)) (listSum (values.map fun value => listSum (family value))) := by
  induction values with
  | nil => exact equiv_refl zero
  | cons value rest inductionHypothesis =>
      exact equiv_trans (listSum_append (family value) (rest.flatMap family)) (add_congr (equiv_refl _) inductionHypothesis)

theorem listSum_map_neg (values : List SignedRatio) : Equiv (listSum (values.map neg)) (neg (listSum values)) := by
  induction values with
  | nil => exact equiv_refl zero
  | cons value rest inductionHypothesis =>
      exact equiv_trans (add_congr (equiv_refl _) inductionHypothesis) (equiv_symm (neg_add value (listSum rest)))

end SignedRatio
end Probability
end Thesis
