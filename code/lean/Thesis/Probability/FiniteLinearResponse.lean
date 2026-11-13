import Thesis.Probability.Core

namespace Thesis
namespace Probability

/-!
# Finite linear responses and balanced rational perturbations

The causal table construction varies nonnegative rational cells.  A signed
perturbation need not introduce integers, subtraction, or representatives of
rational equivalence classes: its positive and negative parts can be supplied
as two nonnegative cell families.  A pointwise balance then transports through
finite sums and fixed coefficients.

The decisive cancellation below uses only stored denominator positivity.
Neither probability-cell positivity nor common denominators are required.
In particular, zero coefficients remain harmless.  These algebraic results
do not claim that a given graph admits a separating perturbation; they expose
the exact finite equations a constructive countermodel must satisfy.
-/

namespace QProb

/-- Cancel a common rational summand using natural cross-products.  Only
the denominator is cancelled; the common summand may have zero numerator. -/
theorem add_cancel_right {left right common : QProb}
    (balanced : Equiv (add left common) (add right common)) : Equiv left right := by
  change (left.num * common.den + common.num * left.den) * (right.den * common.den) =
    (right.num * common.den + common.num * right.den) * (left.den * common.den) at balanced
  simp only [Nat.add_mul] at balanced
  have expanded :
      (left.num * right.den) * (common.den * common.den) +
          (common.num * (left.den * right.den)) * common.den =
        (right.num * left.den) * (common.den * common.den) +
          (common.num * (left.den * right.den)) * common.den := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using balanced
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos common.den_pos common.den_pos)
    (Nat.add_right_cancel expanded)

/-- The left-summand version retains arbitrary rational presentations. -/
theorem add_cancel_left {left right common : QProb}
    (balanced : Equiv (add common left) (add common right)) : Equiv left right :=
  add_cancel_right (equiv_trans (add_comm left common)
    (equiv_trans balanced (add_comm common right)))

/-- A sum of pointwise additions is the addition of the two finite sums.
No duplicate-free or complete-list hypothesis is needed for this algebra. -/
theorem listSum_map_add (values : List α) (left right : α → QProb) :
    Equiv (listSum (values.map fun value => add (left value) (right value)))
      (add (listSum (values.map left)) (listSum (values.map right))) := by
  induction values with
  | nil => simp [listSum, Equiv, add, zero]
  | cons value rest inductionHypothesis =>
      exact equiv_trans (add_congr (equiv_refl _) inductionHypothesis) (by
        simp only [List.map_cons, listSum, Equiv, add, Nat.add_mul]
        ac_rfl)

end QProb

namespace FiniteLinearResponse

open QProb

/-- The sum of a cell family against a fixed nonnegative rational
environment.  The environment may already contain products or finite sums. -/
def applyWith (values : List α) (environment cells : α → QProb) : QProb :=
  listSum (values.map fun value => mul (cells value) (environment value))

/-- Pointwise balanced cells remain balanced after finite summation. -/
theorem sum_balance (values : List α) (left right decrease increase : α → QProb)
    (balanced : forall value, Equiv (add (left value) (decrease value))
      (add (right value) (increase value))) :
    Equiv (add (listSum (values.map left)) (listSum (values.map decrease)))
      (add (listSum (values.map right)) (listSum (values.map increase))) :=
  equiv_trans (equiv_symm (listSum_map_add values left decrease))
    (equiv_trans (listSum_map_congr values _ _ balanced)
      (listSum_map_add values right increase))

/-- Equality of two balanced finite sums is equivalent to cancellation
of the perturbation's two parts.  This also provides the contrapositive
needed for separation, without deciding an arbitrary proposition. -/
theorem sum_equiv_iff_of_balance (values : List α)
    (left right decrease increase : α → QProb)
    (balanced : forall value, Equiv (add (left value) (decrease value))
      (add (right value) (increase value))) :
    Equiv (listSum (values.map left)) (listSum (values.map right)) ↔
      Equiv (listSum (values.map decrease)) (listSum (values.map increase)) := by
  have summed := sum_balance values left right decrease increase balanced
  constructor
  · intro compared
    exact add_cancel_left (equiv_trans
      (equiv_symm (add_congr compared (equiv_refl _))) summed)
  · intro cancelled
    exact add_cancel_right (equiv_trans summed
      (add_congr (equiv_refl _) (equiv_symm cancelled)))

/-- Fixed environments transport pointwise balance.  An environment
coefficient is multiplied, never divided out, so it may vanish. -/
theorem applyWith_equiv_iff_of_balance (values : List α) (environment : α → QProb)
    (left right decrease increase : α → QProb)
    (balanced : forall value, Equiv (add (left value) (decrease value))
      (add (right value) (increase value))) :
    Equiv (applyWith values environment left) (applyWith values environment right) ↔
      Equiv (applyWith values environment decrease) (applyWith values environment increase) := by
  apply sum_equiv_iff_of_balance values
  intro value
  exact equiv_trans (equiv_symm (add_mul_distrib _ _ _))
    (equiv_trans (mul_congr (balanced value) (equiv_refl _))
      (add_mul_distrib _ _ _))

end FiniteLinearResponse
end Probability
end Thesis
