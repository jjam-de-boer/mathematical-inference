import Thesis.Probability.FiniteProductBalance

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteProductBalance

/-!
# Small exact checks for interacting finite product changes

These two-coordinate calculations check the mixed-environment order and the
orientation of balanced variation parts.  The first has a zero old cell:
two simultaneous increases give a product change twice the naive sum taken
at the old environment.  The second changes both factors but preserves the
product, using unequal rational presentations on the two sides.

Only these tiny explicit rational expressions are evaluated.  No SCM private
function space or exhaustive graph search is constructed by this regression.
The general cancellation theorem, rather than a numerical equality alone,
is used to infer the complete product comparison in each case.
-/

private def zeroLeft (index : Fin 2) : QProb :=
  if index.val = 0 then QProb.zero else ⟨1, 3, by decide⟩

private def zeroRight (index : Fin 2) : QProb :=
  if index.val = 0 then ⟨1, 2, by decide⟩ else ⟨2, 3, by decide⟩

private def zeroDecrease (index : Fin 2) : QProb :=
  if index.val = 0 then ⟨1, 2, by decide⟩ else ⟨1, 3, by decide⟩

private def noPart (_index : Fin 2) : QProb := QProb.zero

private theorem zero_balanced (index : Fin 2) :
    QProb.Equiv (QProb.add (zeroLeft index) (zeroDecrease index))
      (QProb.add (zeroRight index) (noPart index)) := by
  rcases index with ⟨value, bound⟩
  match value with
  | 0 => simp [zeroLeft, zeroDecrease, zeroRight, noPart, QProb.Equiv, QProb.add, QProb.zero]
  | 1 => simp [zeroLeft, zeroDecrease, zeroRight, noPart, QProb.Equiv, QProb.add, QProb.zero]
  | _ + 2 => exact False.elim (by omega)

/-- The exact variation retains the interaction at the changed second
factor; the old-environment approximation loses half the actual change. -/
theorem interaction_retained :
    QProb.Equiv (FiniteProduct.qProductVariation 2 zeroLeft zeroRight zeroDecrease)
      ⟨1, 3, by decide⟩ ∧
    QProb.Equiv
      (QProb.add (QProb.mul (zeroDecrease 1) (zeroLeft 0))
        (QProb.mul (zeroLeft 1) (zeroDecrease 0))) ⟨1, 6, by decide⟩ := by
  decide +kernel

/-- A zero old factor is harmless: no positive-cell division is needed to
deduce the product gap from the noncancelling mixed variation parts. -/
theorem zero_cell_products_separated :
    Not (QProb.Equiv (FiniteProduct.qProduct 2 zeroLeft) (FiniteProduct.qProduct 2 zeroRight)) := by
  intro equal
  have cancelled := (FiniteProduct.qProduct_equiv_iff_of_balance 2 zeroLeft zeroRight
    zeroDecrease noPart zero_balanced).mp equal
  have distinct : Not (QProb.Equiv
      (FiniteProduct.qProductVariation 2 zeroLeft zeroRight zeroDecrease)
      (FiniteProduct.qProductVariation 2 zeroLeft zeroRight noPart)) := by decide +kernel
  exact distinct cancelled

private def cancelLeft (index : Fin 2) : QProb :=
  if index.val = 0 then ⟨2, 4, by decide⟩ else ⟨2, 3, by decide⟩

private def cancelRight (index : Fin 2) : QProb :=
  if index.val = 0 then ⟨2, 6, by decide⟩ else ⟨7, 7, by decide⟩

private def cancelDecrease (index : Fin 2) : QProb :=
  if index.val = 0 then QProb.zero else ⟨1, 3, by decide⟩

private def cancelIncrease (index : Fin 2) : QProb :=
  if index.val = 0 then ⟨1, 6, by decide⟩ else QProb.zero

private theorem cancellation_balanced (index : Fin 2) :
    QProb.Equiv (QProb.add (cancelLeft index) (cancelDecrease index))
      (QProb.add (cancelRight index) (cancelIncrease index)) := by
  rcases index with ⟨value, bound⟩
  match value with
  | 0 => simp [cancelLeft, cancelDecrease, cancelRight, cancelIncrease, QProb.Equiv, QProb.add, QProb.zero]
  | 1 => simp [cancelLeft, cancelDecrease, cancelRight, cancelIncrease, QProb.Equiv, QProb.add, QProb.zero]
  | _ + 2 => exact False.elim (by omega)

/-- Different factors and denominator presentations can cancel exactly
after mixing.  Equality of individual changed cells is not required. -/
theorem mixed_variations_cancel :
    QProb.Equiv (FiniteProduct.qProductVariation 2 cancelLeft cancelRight cancelDecrease)
      (FiniteProduct.qProductVariation 2 cancelLeft cancelRight cancelIncrease) := by
  decide +kernel

/-- Recover complete product equality through the general balance theorem,
checking the reverse implication as well as the separation implication. -/
theorem changed_products_equal :
    QProb.Equiv (FiniteProduct.qProduct 2 cancelLeft) (FiniteProduct.qProduct 2 cancelRight) :=
  (FiniteProduct.qProduct_equiv_iff_of_balance 2 cancelLeft cancelRight cancelDecrease
    cancelIncrease cancellation_balanced).mpr mixed_variations_cancel

end FiniteProductBalance
end Examples
end Probability
end Thesis
