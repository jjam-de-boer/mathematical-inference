import Thesis.Probability.ExactLog

namespace Thesis.Probability.ExactLog

/-- Multiplication of an exact logarithm by a nonnegative rational coefficient. -/
def scaleRatio (q : QProb) (x : ExactLog) : ExactLog :=
  ⟨x.argument.pow q.num, x.degree * q.den, Nat.mul_pos x.degree_pos q.den_pos⟩

theorem scaleRatio_value_congr (q : QProb) {x y : ExactLog} (same : Equiv x y) :
    Equiv (scaleRatio q x) (scaleRatio q y) := by
  change PositiveRatio.Equiv ((x.argument.pow q.num).pow (y.degree * q.den))
    ((y.argument.pow q.num).pow (x.degree * q.den))
  have left : (x.argument.pow q.num).pow (y.degree * q.den) =
      (x.argument.pow y.degree).pow (q.num * q.den) := by
    simp only [← PositiveRatio.pow_mul]; congr 1; ac_rfl
  have right : (y.argument.pow q.num).pow (x.degree * q.den) =
      (y.argument.pow x.degree).pow (q.num * q.den) := by
    simp only [← PositiveRatio.pow_mul]; congr 1; ac_rfl
  rw [left, right]
  exact PositiveRatio.pow_congr same _

theorem scaleRatio_weight_congr {p q : QProb} (same : QProb.Equiv p q) (x : ExactLog) :
    Equiv (scaleRatio p x) (scaleRatio q x) := by
  change PositiveRatio.Equiv ((x.argument.pow p.num).pow (x.degree * q.den))
    ((x.argument.pow q.num).pow (x.degree * p.den))
  rw [← PositiveRatio.pow_mul, ← PositiveRatio.pow_mul]
  have exponent : p.num * (x.degree * q.den) = q.num * (x.degree * p.den) := by
    calc
      _ = (p.num * q.den) * x.degree := by ac_rfl
      _ = (q.num * p.den) * x.degree := by rw [same]
      _ = _ := by ac_rfl
  rw [exponent]
  exact PositiveRatio.equiv_refl _

theorem scaleRatio_congr {p q : QProb} {x y : ExactLog} (weight : QProb.Equiv p q) (value : Equiv x y) :
    Equiv (scaleRatio p x) (scaleRatio q y) :=
  equiv_trans (scaleRatio_value_congr p value) (scaleRatio_weight_congr weight y)

theorem scaleRatio_zero_value (q : QProb) : Equiv (scaleRatio q zero) zero := by
  change PositiveRatio.Equiv ((PositiveRatio.one.pow q.num).pow 1) (PositiveRatio.one.pow (1 * q.den))
  rw [PositiveRatio.one_pow, PositiveRatio.one_pow, PositiveRatio.one_pow]
  exact PositiveRatio.equiv_refl _

theorem scaleRatio_mono (q : QProb) {x y : ExactLog} (compared : LE x y) :
    LE (scaleRatio q x) (scaleRatio q y) := by
  by_cases positive : 0 < q.num
  · change LE (divideNat (scaleNat q.num x) q.den q.den_pos) (divideNat (scaleNat q.num y) q.den q.den_pos)
    exact (divideNat_le_divideNat_iff _ _ _ _).mpr ((scaleNat_le_scaleNat_iff _ positive _ _).mpr compared)
  · have vanished : q.num = 0 := Nat.eq_zero_of_not_pos positive
    change PositiveRatio.LE ((x.argument.pow q.num).pow (y.degree * q.den))
      ((y.argument.pow q.num).pow (x.degree * q.den))
    rw [vanished, PositiveRatio.pow_zero, PositiveRatio.pow_zero, PositiveRatio.one_pow, PositiveRatio.one_pow]
    exact PositiveRatio.le_refl _

theorem scaleRatio_nonnegative (q : QProb) {x : ExactLog} (nonnegative : LE zero x) : LE zero (scaleRatio q x) :=
  (le_congr (scaleRatio_zero_value q) (equiv_refl _)).mp (scaleRatio_mono q nonnegative)

def listSum : List ExactLog → ExactLog
  | [] => zero
  | head :: rest => add head (listSum rest)

theorem listSum_map_congr (values : List A) (f g : A → ExactLog)
    (same : ∀ value ∈ values, Equiv (f value) (g value)) :
    Equiv (listSum (values.map f)) (listSum (values.map g)) := by
  induction values with
  | nil => exact equiv_refl _
  | cons head rest ih =>
      exact add_congr (same head (List.mem_cons_self ..))
        (ih (fun value member => same value (List.mem_cons_of_mem _ member)))

theorem listSum_append (xs ys : List ExactLog) : listSum (xs ++ ys) = add (listSum xs) (listSum ys) := by
  induction xs with
  | nil => exact (zero_add _).symm
  | cons head rest ih => simp only [List.cons_append, listSum, ih, add_assoc]

theorem listSum_perm {xs ys : List ExactLog} (permutation : xs.Perm ys) : Equiv (listSum xs) (listSum ys) := by
  induction permutation with
  | nil => exact equiv_refl _
  | cons head _ ih => exact add_congr (equiv_refl _) ih
  | swap a b rest =>
      change Equiv (add b (add a (listSum rest))) (add a (add b (listSum rest)))
      rw [← add_assoc, ← add_assoc]
      exact add_congr (add_comm b a) (equiv_refl _)
  | trans _ _ first second => exact equiv_trans first second

theorem add_nonnegative {x y : ExactLog} (first : LE zero x) (second : LE zero y) : LE zero (add x y) := by
  have lifted := (add_le_add_right_iff zero x y).mpr first
  rw [zero_add] at lifted
  exact le_trans second lifted

theorem listSum_map_nonnegative (values : List A) (f : A → ExactLog)
    (nonnegative : ∀ value ∈ values, LE zero (f value)) : LE zero (listSum (values.map f)) := by
  induction values with
  | nil => exact le_refl _
  | cons head rest ih =>
      exact add_nonnegative (nonnegative head (List.mem_cons_self ..))
        (ih (fun value member => nonnegative value (List.mem_cons_of_mem _ member)))

theorem listSum_map_zero (values : List A) : listSum (values.map (fun _ => zero)) = zero := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp only [List.map_cons, listSum, ih, zero_add]

end Thesis.Probability.ExactLog
