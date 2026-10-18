import Thesis.Probability.Construction

namespace Thesis.Probability

/-!
# Bounds for explicit finite enumerations

These list bounds count supplied positions, not positive-probability values.
They will bound native hidden-value tables by evaluating a finite list of
interventions at every explicitly listed noise assignment. Repeated labels,
empty coordinate lists and an empty coordinate family are all retained.
No finiteness instance, representative choice or probabilistic positivity
assumption is used in the counting arguments.
-/

theorem deduplicate_length_le [DecidableEq X] (values : List X) :
    (deduplicate values).length ≤ values.length := by
  induction values with
  | nil => exact Nat.le_refl 0
  | cons head tail inductionHypothesis =>
      unfold deduplicate
      split
      · exact Nat.le_trans inductionHypothesis (Nat.le_succ _)
      · exact Nat.succ_le_succ inductionHypothesis

/-- A rectangular list of evaluations has its literal product length,
even when the entries themselves repeat. -/
theorem length_flatMap_of_length (values : List X) (family : X → List Y)
    (width : Nat) (same : ∀ value, (family value).length = width) :
    (values.flatMap family).length = values.length * width := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change (family head ++ tail.flatMap family).length = (tail.length + 1) * width
      rw [List.length_append, same head, inductionHypothesis, Nat.succ_mul, Nat.add_comm]

namespace FiniteProduct

/-- Count the actual dependent-product enumeration in its existing terminal-
coordinate order. This includes the singleton empty assignment. -/
theorem enumeration_length (n : Nat) (Value : Fin n → Type u)
    (values : (index : Fin n) → List (Value index)) :
    (enumeration n Value values).length = natProduct n (fun index => (values index).length) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [enumeration, length_flatMap_of_length _ _
        (enumeration n (fun index => Value index.castSucc) (fun index => values index.castSucc)).length
        (fun _ => List.length_map _), inductionHypothesis]
      rfl

/-- A common coordinate bound gives a power bound without computing the
Cartesian list. Zero bounds and an empty product are permitted. -/
theorem natProduct_le_pow (n : Nat) (values : Fin n → Nat) (bound : Nat)
    (bounded : ∀ index, values index ≤ bound) : natProduct n values ≤ bound ^ n := by
  induction n with
  | zero => exact Nat.le_refl 1
  | succ n inductionHypothesis =>
      change values (Fin.last n) * natProduct n (fun index => values index.castSucc) ≤ bound ^ (n + 1)
      rw [Nat.pow_succ, Nat.mul_comm (bound ^ n) bound]
      exact Nat.mul_le_mul (bounded (Fin.last n))
        (inductionHypothesis (fun index => values index.castSucc) (fun index => bounded index.castSucc))

end FiniteProduct
end Thesis.Probability
