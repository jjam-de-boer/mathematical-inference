import Thesis.Probability.ExactLogWeights

namespace Thesis.Probability.ExactLog

theorem ext {x y : ExactLog} (argument : x.argument = y.argument) (degree : x.degree = y.degree) : x = y := by
  cases x; cases y; simp_all

theorem neg_zero : neg zero = zero := rfl

theorem neg_add (x y : ExactLog) : neg (add x y) = add (neg x) (neg y) := by
  apply ext
  · simp only [neg, add, PositiveRatio.inv_mul, PositiveRatio.inv_pow]
  · rfl

theorem add_left_comm (a b c : ExactLog) : Equiv (add a (add b c)) (add b (add a c)) := by
  rw [← add_assoc, ← add_assoc]
  exact add_congr (add_comm a b) (equiv_refl _)

theorem add_four (a b c d : ExactLog) : Equiv (add (add a b) (add c d)) (add (add a c) (add b d)) := by
  rw [add_assoc, add_assoc]
  exact add_congr (equiv_refl _) (add_left_comm b c d)

/-- Rational scaling is linear in its exact logarithm argument. -/
theorem scaleRatio_add_value (q : QProb) (x y : ExactLog) :
    Equiv (scaleRatio q (add x y)) (add (scaleRatio q x) (scaleRatio q y)) := by
  have presentation : add (scaleRatio q x) (scaleRatio q y) =
      rescale (scaleRatio q (add x y)) q.den q.den_pos := by
    apply ext
    · apply PositiveRatio.ext <;>
        simp only [add, scaleRatio, rescale, PositiveRatio.mul, PositiveRatio.pow, Nat.mul_pow, ← Nat.pow_mul] <;> ac_rfl
    · change (x.degree * q.den) * (y.degree * q.den) = (x.degree * y.degree * q.den) * q.den
      ac_rfl
  rw [presentation]
  exact equiv_symm (rescale_equiv _ _ _)

/-- Rational scaling is linear in the nonnegative coefficient as well. -/
theorem scaleRatio_add_weight (p q : QProb) (x : ExactLog) :
    Equiv (scaleRatio (QProb.add p q) x) (add (scaleRatio p x) (scaleRatio q x)) := by
  have presentation : add (scaleRatio p x) (scaleRatio q x) =
      rescale (scaleRatio (QProb.add p q) x) x.degree x.degree_pos := by
    apply ext
    · apply PositiveRatio.ext <;>
        simp only [add, scaleRatio, rescale, QProb.add, PositiveRatio.mul, PositiveRatio.pow,
          ← Nat.pow_mul, ← Nat.pow_add, Nat.add_mul] <;> ac_rfl
    · change (x.degree * p.den) * (x.degree * q.den) = (x.degree * (p.den * q.den)) * x.degree
      ac_rfl
  rw [presentation]
  exact equiv_symm (rescale_equiv _ _ _)

theorem scaleRatio_one (x : ExactLog) : scaleRatio QProb.one x = x := by
  apply ext <;> simp only [scaleRatio, QProb.one, PositiveRatio.pow_one, Nat.mul_one]

theorem scaleRatio_zero_weight (x : ExactLog) : Equiv (scaleRatio QProb.zero x) zero := by
  change PositiveRatio.Equiv ((x.argument.pow 0).pow 1) (PositiveRatio.one.pow (x.degree * 1))
  rw [PositiveRatio.pow_zero, PositiveRatio.one_pow, PositiveRatio.one_pow]
  exact PositiveRatio.equiv_refl _

theorem scaleRatio_mul (p q : QProb) (x : ExactLog) : scaleRatio p (scaleRatio q x) = scaleRatio (QProb.mul p q) x := by
  apply ext
  · simp only [scaleRatio, QProb.mul, ← PositiveRatio.pow_mul, Nat.mul_comm]
  · simp only [scaleRatio, QProb.mul]; ac_rfl

theorem scaleRatio_neg (q : QProb) (x : ExactLog) : scaleRatio q (neg x) = neg (scaleRatio q x) := by
  apply ext
  · simp only [scaleRatio, neg, PositiveRatio.inv_pow]
  · rfl

theorem listSum_neg (values : List ExactLog) : listSum (values.map neg) = neg (listSum values) := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp only [List.map_cons, listSum, ih, neg_add]

theorem listSum_scaleRatio (values : List ExactLog) (q : QProb) :
    Equiv (listSum (values.map (scaleRatio q))) (scaleRatio q (listSum values)) := by
  induction values with
  | nil => exact equiv_symm (scaleRatio_zero_value q)
  | cons head rest ih =>
      exact equiv_trans (add_congr (equiv_refl _) ih) (equiv_symm (scaleRatio_add_value q head (listSum rest)))

theorem listSum_scaleRatio_weights (values : List QProb) (x : ExactLog) :
    Equiv (listSum (values.map (fun q => scaleRatio q x))) (scaleRatio (QProb.listSum values) x) := by
  induction values with
  | nil => exact equiv_symm (scaleRatio_zero_weight x)
  | cons head rest ih =>
      exact equiv_trans (add_congr (equiv_refl _) ih) (equiv_symm (scaleRatio_add_weight head (QProb.listSum rest) x))

theorem listSum_map_add (values : List A) (f g : A → ExactLog) :
    Equiv (listSum (values.map (fun value => add (f value) (g value))))
      (add (listSum (values.map f)) (listSum (values.map g))) := by
  induction values with
  | nil =>
      change Equiv zero (add zero zero)
      rw [zero_add]
      exact equiv_refl _
  | cons head rest ih =>
      exact equiv_trans (add_congr (equiv_refl _) ih) (add_four _ _ _ _)

theorem zero_le_sub_iff (y x : ExactLog) : LE zero (sub y x) ↔ LE x y := by
  calc
    _ ↔ LE (add x (neg x)) (add y (neg x)) := (le_congr (add_neg x) (equiv_refl _)).symm
    _ ↔ LE x y := add_le_add_right_iff x y (neg x)

theorem sub_le_zero_iff (y x : ExactLog) : LE (sub y x) zero ↔ LE y x := by
  calc
    _ ↔ LE (add y (neg x)) (add x (neg x)) := (le_congr (equiv_refl _) (add_neg x)).symm
    _ ↔ LE y x := add_le_add_right_iff y x (neg x)

theorem sub_equiv_zero_iff (y x : ExactLog) : Equiv (sub y x) zero ↔ Equiv y x := by
  rw [equiv_iff_le, sub_le_zero_iff, zero_le_sub_iff]
  exact (equiv_iff_le y x).symm

theorem listSum_map_neg (values : List A) (f : A → ExactLog) :
    listSum (values.map (fun value => neg (f value))) = neg (listSum (values.map f)) := by
  have result := listSum_neg (values.map f)
  simpa only [List.map_map, Function.comp_def] using result

theorem listSum_map_sub (values : List A) (f g : A → ExactLog) :
    Equiv (listSum (values.map (fun value => sub (f value) (g value))))
      (sub (listSum (values.map f)) (listSum (values.map g))) := by
  have result := listSum_map_add values f (fun value => neg (g value))
  rw [listSum_map_neg] at result
  exact result

end Thesis.Probability.ExactLog
