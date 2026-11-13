import Thesis.Probability.SignedRatio

namespace Thesis
namespace Probability
namespace SignedRatio

/-!
# Finite signed rational sums without normalized representatives

The rational compression bridge integrates signed responses against ordinary
natural probability weights.  These helpers operate on explicit positive
denominators throughout.  Congruence is proved at cross-products, rather than
by selecting a canonical representative of an equivalence class.

`scaleNat` deliberately keeps its argument's denominator; `divideNat` only
multiplies it by a supplied positive natural.  Neither operation divides an
integer numerator or silently gives a value to a zero denominator.
-/

theorem add_congr {left left' right right' : SignedRatio}
    (first : Equiv left left') (second : Equiv right right') :
    Equiv (add left right) (add left' right') := by
  change (left.num * (right.den : Int) + right.num * (left.den : Int)) *
      ((left'.den * right'.den : Nat) : Int) =
    (left'.num * (right'.den : Int) + right'.num * (left'.den : Int)) *
      ((left.den * right.den : Nat) : Int)
  simp only [Int.natCast_mul, Int.add_mul]
  have firstTerm : left.num * (right.den : Int) * ((left'.den : Int) * (right'.den : Int)) =
      left'.num * (right'.den : Int) * ((left.den : Int) * (right.den : Int)) := by
    calc
      _ = (left.num * (left'.den : Int)) * ((right.den : Int) * (right'.den : Int)) := by ac_rfl
      _ = (left'.num * (left.den : Int)) * ((right.den : Int) * (right'.den : Int)) := by rw [first]
      _ = _ := by ac_rfl
  have secondTerm : right.num * (left.den : Int) * ((left'.den : Int) * (right'.den : Int)) =
      right'.num * (left'.den : Int) * ((left.den : Int) * (right.den : Int)) := by
    calc
      _ = (right.num * (right'.den : Int)) * ((left.den : Int) * (left'.den : Int)) := by ac_rfl
      _ = (right'.num * (right.den : Int)) * ((left.den : Int) * (left'.den : Int)) := by rw [second]
      _ = _ := by ac_rfl
  rw [firstTerm, secondTerm]

theorem mul_congr {left left' right right' : SignedRatio}
    (first : Equiv left left') (second : Equiv right right') :
    Equiv (mul left right) (mul left' right') := by
  change left.num * right.num * ((left'.den * right'.den : Nat) : Int) =
    left'.num * right'.num * ((left.den * right.den : Nat) : Int)
  simp only [Int.natCast_mul]
  calc
    _ = (left.num * (left'.den : Int)) * (right.num * (right'.den : Int)) := by ac_rfl
    _ = (left'.num * (left.den : Int)) * (right'.num * (right.den : Int)) := by rw [first, second]
    _ = _ := by ac_rfl

def scaleNat (weight : Nat) (value : SignedRatio) : SignedRatio :=
  ⟨(weight : Int) * value.num, value.den, value.den_pos⟩

theorem scaleNat_congr (weight : Nat) {left right : SignedRatio} (same : Equiv left right) :
    Equiv (scaleNat weight left) (scaleNat weight right) := by
  change (weight : Int) * left.num * (right.den : Int) = (weight : Int) * right.num * (left.den : Int)
  calc
    _ = (weight : Int) * (left.num * (right.den : Int)) := by ac_rfl
    _ = (weight : Int) * (right.num * (left.den : Int)) := by rw [same]
    _ = _ := by ac_rfl

def divideNat (value : SignedRatio) (denominator : Nat) (positive : 0 < denominator) : SignedRatio :=
  ⟨value.num, value.den * denominator, Nat.mul_pos value.den_pos positive⟩

theorem divideNat_congr {left right : SignedRatio} (same : Equiv left right)
    (denominator : Nat) (positive : 0 < denominator) :
    Equiv (divideNat left denominator positive) (divideNat right denominator positive) := by
  change left.num * ((right.den * denominator : Nat) : Int) =
    right.num * ((left.den * denominator : Nat) : Int)
  simp only [Int.natCast_mul, ← Int.mul_assoc]
  rw [same]

def listSum : List SignedRatio → SignedRatio
  | [] => zero
  | value :: rest => add value (listSum rest)

theorem listSum_map_congr (values : List α) (left right : α → SignedRatio)
    (same : forall value, Equiv (left value) (right value)) :
    Equiv (listSum (values.map left)) (listSum (values.map right)) := by
  induction values with
  | nil => exact equiv_refl zero
  | cons value rest inductionHypothesis => exact add_congr (same value) inductionHypothesis

theorem add_mk_same_den (denominator : Nat) (positive : 0 < denominator) (first second : Int) :
    Equiv (add ⟨first, denominator, positive⟩ ⟨second, denominator, positive⟩)
      ⟨first + second, denominator, positive⟩ := by
  simp only [Equiv, add, Int.natCast_mul, Int.add_mul]
  ac_rfl

/-- A common-denominator finite sum retains the ordinary integer sum of
numerators.  The empty list is included and needs no inhabited index type. -/
theorem listSum_mk_same_den (denominator : Nat) (positive : 0 < denominator) (numerators : List Int) :
    Equiv (listSum (numerators.map fun numerator => ⟨numerator, denominator, positive⟩))
      ⟨numerators.sum, denominator, positive⟩ := by
  induction numerators with
  | nil => simp only [List.map_nil, listSum, zero, List.sum_nil, Equiv, Int.zero_mul]
  | cons first rest inductionHypothesis =>
      exact equiv_trans (add_congr (equiv_refl _) inductionHypothesis)
        (add_mk_same_den denominator positive first rest.sum)

end SignedRatio
end Probability
end Thesis
