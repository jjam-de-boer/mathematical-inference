import Thesis.Probability.Construction

namespace Thesis
namespace Probability
namespace FiniteProduct

/-!
# Isolating one factor of a finite rational product

A local-table perturbation changes one response coordinate, while the other
coordinates retain their actual probability factors.  The product should be
factored around that coordinate—not divided by its old probability, which
may be zero.  Replacing the selected factor by one gives a common remaining
product with no positivity or common-denominator assumption.

These statements concern arbitrary nonnegative rational presentations.  All
coordinate decisions are the supplied finite equality; no representative of
a probability equivalence class or ordering of latent states is selected.
-/

/-- Pointwise multiplication can be regrouped into the two separate finite
products.  Equivalence, rather than presentation equality, retains arbitrary
rational denominators and the existing terminal-coordinate recursion. -/
theorem qProduct_pointwise_mul (n : Nat) (left right : Fin n → QProb) :
    QProb.Equiv (qProduct n (fun index => QProb.mul (left index) (right index)))
      (QProb.mul (qProduct n left) (qProduct n right)) := by
  induction n with
  | zero => simp [qProduct, QProb.Equiv, QProb.mul, QProb.one]
  | succ n inductionHypothesis =>
      exact QProb.equiv_trans
        (QProb.mul_congr (QProb.equiv_refl _)
          (inductionHypothesis (fun index => left index.castSucc) (fun index => right index.castSucc)))
        (by simp only [qProduct, QProb.Equiv, QProb.mul]; ac_rfl)

/-- Keep every factor except the explicitly selected coordinate.  No index
is erased or renumbered, so this definition also handles gapped selections. -/
def qProductWithout (n : Nat) (chosen : Fin n) (values : Fin n → QProb) : QProb :=
  qProduct n (fun index => if index = chosen then QProb.one else values index)

/-- Isolate one factor without dividing by it.  This remains valid when
either the chosen factor or another factor has zero numerator. -/
theorem qProduct_coordinate (n : Nat) (chosen : Fin n) (values : Fin n → QProb) :
    QProb.Equiv (qProduct n values)
      (QProb.mul (values chosen) (qProductWithout n chosen values)) := by
  let selected : Fin n → QProb := fun index => if index = chosen then values chosen else QProb.one
  let remaining : Fin n → QProb := fun index => if index = chosen then QProb.one else values index
  have pointwise (index : Fin n) :
      QProb.Equiv (values index) (QProb.mul (selected index) (remaining index)) := by
    by_cases same : index = chosen
    · subst index
      simp only [selected, remaining, if_pos rfl]
      exact QProb.equiv_symm (QProb.mul_one (values chosen))
    · simp only [selected, remaining, if_neg same]
      exact QProb.equiv_symm (QProb.one_mul (values index))
  exact QProb.equiv_trans (qProduct_congr n pointwise)
    (QProb.equiv_trans (qProduct_pointwise_mul n selected remaining)
      (QProb.mul_congr (qProduct_singleton n chosen (values chosen)) (QProb.equiv_refl _)))

/-- A remaining product is common to any two families agreeing off the
chosen coordinate.  Its chosen factor is literally one in both families. -/
theorem qProductWithout_congr (n : Nat) (chosen : Fin n) (left right : Fin n → QProb)
    (same : forall index, index ≠ chosen → QProb.Equiv (left index) (right index)) :
    QProb.Equiv (qProductWithout n chosen left) (qProductWithout n chosen right) := by
  apply qProduct_congr n
  intro index
  by_cases selected : index = chosen
  · simp only [if_pos selected]
    exact QProb.equiv_refl _
  · simp only [if_neg selected]
    exact same index selected

end FiniteProduct
end Probability
end Thesis
