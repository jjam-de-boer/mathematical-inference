import Thesis.Probability.FiniteProductResponse
import Thesis.Probability.FiniteLinearResponse

namespace Thesis
namespace Probability
namespace FiniteProduct

/-!
# Exact balanced changes of several finite product factors

A coordinated table change is not linear in all changed rows together.
Summing the one-row derivatives at the original table misses products of
changes.  The finite telescope below instead uses a mixed environment:
coordinates already replaced use the right factors, and the remaining
coordinates use the left factors.  Consequently every interaction is
retained without introducing signed rationals or choosing representatives.

The two nonnegative variation parts satisfy the same balance as the two
complete products.  Their equality is therefore equivalent to equality of
the products, using only denominator positivity for cancellation.  Factors
and variation parts may vanish, and all rational presentations may have
different denominators.  Nothing is divided by an old probability.

This algebra supports simultaneous causal-table changes at arbitrary finite
sets of vertices, including responding descendants.  It does not prove the
missing existence of a graph-specific observationally cancelling direction.
-/

/-- One nonnegative part of the exact finite telescope.  The terminal
coordinate changes against the old remaining product; later recursive terms
retain that coordinate's new factor.  The empty telescope is zero. -/
def qProductVariation : (n : Nat) -> (Fin n -> QProb) -> (Fin n -> QProb) ->
    (Fin n -> QProb) -> QProb
  | 0, _, _, _ => QProb.zero
  | n + 1, left, right, part =>
      QProb.add
        (QProb.mul (part (Fin.last n)) (qProduct n (fun index => left index.castSucc)))
        (QProb.mul (right (Fin.last n))
          (qProductVariation n (fun index => left index.castSucc)
            (fun index => right index.castSucc) (fun index => part index.castSucc)))

private theorem add_swap_middle (first second third : QProb) :
    QProb.Equiv (QProb.add (QProb.add first second) third)
      (QProb.add (QProb.add first third) second) :=
  QProb.equiv_trans (QProb.add_assoc first second third)
    (QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) (QProb.add_comm second third))
      (QProb.equiv_symm (QProb.add_assoc first third second)))

/-- The one-step telescope combines a balanced changed factor with an
already balanced remaining product.  Both cross terms are kept explicitly. -/
private theorem product_balance_step (a b c e d i f g : QProb)
    (factor : QProb.Equiv (QProb.add a d) (QProb.add b i))
    (rest : QProb.Equiv (QProb.add c f) (QProb.add e g)) :
    QProb.Equiv
      (QProb.add (QProb.mul a c) (QProb.add (QProb.mul d c) (QProb.mul b f)))
      (QProb.add (QProb.mul b e) (QProb.add (QProb.mul i c) (QProb.mul b g))) := by
  refine QProb.equiv_trans (QProb.equiv_symm (QProb.add_assoc _ _ _)) ?_
  refine QProb.equiv_trans
    (QProb.add_congr (QProb.equiv_symm (QProb.add_mul_distrib a d c)) (QProb.equiv_refl _)) ?_
  refine QProb.equiv_trans
    (QProb.add_congr (QProb.mul_congr factor (QProb.equiv_refl c)) (QProb.equiv_refl _)) ?_
  refine QProb.equiv_trans
    (QProb.add_congr (QProb.add_mul_distrib b i c) (QProb.equiv_refl _)) ?_
  refine QProb.equiv_trans (add_swap_middle _ _ _) ?_
  refine QProb.equiv_trans
    (QProb.add_congr (QProb.equiv_symm (QProb.mul_add_distrib b c f)) (QProb.equiv_refl _)) ?_
  refine QProb.equiv_trans
    (QProb.add_congr (QProb.mul_congr (QProb.equiv_refl b) rest) (QProb.equiv_refl _)) ?_
  refine QProb.equiv_trans
    (QProb.add_congr (QProb.mul_add_distrib b e g) (QProb.equiv_refl _)) ?_
  exact QProb.equiv_trans (add_swap_middle _ _ _) (QProb.add_assoc _ _ _)

/-- Pointwise balance of arbitrary nonnegative factor changes gives an
exact balance of the complete products.  Induction follows the existing
terminal-coordinate product order, rather than imposing a new enumeration. -/
theorem qProduct_balance (n : Nat) (left right decrease increase : Fin n -> QProb)
    (balanced : forall index, QProb.Equiv (QProb.add (left index) (decrease index))
      (QProb.add (right index) (increase index))) :
    QProb.Equiv
      (QProb.add (qProduct n left) (qProductVariation n left right decrease))
      (QProb.add (qProduct n right) (qProductVariation n left right increase)) := by
  induction n with
  | zero => simp [qProduct, qProductVariation, QProb.Equiv, QProb.add, QProb.zero, QProb.one]
  | succ n inductionHypothesis =>
      exact product_balance_step _ _ _ _ _ _ _ _ (balanced (Fin.last n))
        (inductionHypothesis (fun index => left index.castSucc) (fun index => right index.castSucc)
          (fun index => decrease index.castSucc) (fun index => increase index.castSucc)
          (fun index => balanced index.castSucc))

/-- Equality of complete products is exactly cancellation of the two
mixed-environment variation parts.  The equivalence also gives separation
by a contrapositive, without deciding an arbitrary proposition. -/
theorem qProduct_equiv_iff_of_balance (n : Nat) (left right decrease increase : Fin n -> QProb)
    (balanced : forall index, QProb.Equiv (QProb.add (left index) (decrease index))
      (QProb.add (right index) (increase index))) :
    QProb.Equiv (qProduct n left) (qProduct n right) ↔
      QProb.Equiv (qProductVariation n left right decrease) (qProductVariation n left right increase) := by
  have total := qProduct_balance n left right decrease increase balanced
  constructor
  · intro compared
    exact QProb.add_cancel_left (QProb.equiv_trans
      (QProb.equiv_symm (QProb.add_congr compared (QProb.equiv_refl _))) total)
  · intro cancelled
    exact QProb.add_cancel_right (QProb.equiv_trans total
      (QProb.add_congr (QProb.equiv_refl _) (QProb.equiv_symm cancelled)))

/-- The singleton boundary is the original change part, so the telescope
reduces to one-row response when only one product coordinate is present. -/
theorem qProductVariation_one (left right part : Fin 1 -> QProb) :
    QProb.Equiv (qProductVariation 1 left right part) (part (Fin.last 0)) := by
  simp [qProductVariation, qProduct, QProb.Equiv, QProb.add, QProb.mul, QProb.zero, QProb.one,
    Nat.mul_comm, Nat.mul_left_comm]

end FiniteProduct
end Probability
end Thesis
