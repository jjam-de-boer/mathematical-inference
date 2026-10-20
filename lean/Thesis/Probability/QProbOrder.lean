import Thesis.Probability.Core

namespace Thesis.Probability.QProb

instance (a b : QProb) : Decidable (LE a b) :=
  inferInstanceAs (Decidable (a.num * b.den ≤ b.num * a.den))
instance (a b : QProb) : Decidable (LT a b) :=
  inferInstanceAs (Decidable (a.num * b.den < b.num * a.den))

/-- Addition is monotone on unreduced nonnegative rational presentations. -/
theorem add_le_add {a b c d : QProb} (first : LE a b) (second : LE c d) : LE (add a c) (add b d) := by
  simp only [LE, add, Nat.add_mul]
  calc
    _ = (a.num * b.den) * (c.den * d.den) + (c.num * d.den) * (a.den * b.den) := by
      congr 1 <;> ac_rfl
    _ ≤ (b.num * a.den) * (c.den * d.den) + (d.num * c.den) * (a.den * b.den) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ first) (Nat.mul_le_mul_right _ second)
    _ = _ := by congr 1 <;> ac_rfl

theorem listSum_map_mono (values : List A) (f g : A → QProb)
    (compared : ∀ value ∈ values, LE (f value) (g value)) :
    LE (listSum (values.map f)) (listSum (values.map g)) := by
  induction values with
  | nil => exact le_refl _
  | cons head rest ih =>
      exact add_le_add (compared head (List.mem_cons_self ..))
        (ih (fun value member => compared value (List.mem_cons_of_mem _ member)))

theorem scale_add (factor : Nat) (a b : QProb) : Equiv (scale factor (add a b)) (add (scale factor a) (scale factor b)) := by
  simp only [Equiv, scale, add, Nat.mul_add, Nat.add_mul]
  ac_rfl

theorem listSum_scale (values : List QProb) (factor : Nat) :
    Equiv (listSum (values.map (scale factor))) (scale factor (listSum values)) := by
  induction values with
  | nil => simp only [List.map_nil, listSum, Equiv, scale, zero, Nat.mul_zero, Nat.zero_mul]
  | cons head rest ih =>
      exact equiv_trans (add_congr (equiv_refl _) ih) (equiv_symm (scale_add factor head (listSum rest)))

end Thesis.Probability.QProb
