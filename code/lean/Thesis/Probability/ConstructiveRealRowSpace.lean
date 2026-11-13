import Thesis.Probability.ConstructiveRealKernelElimination
import Thesis.Probability.ConstructiveRealPolynomialExpression

namespace Thesis.Probability.ConstructiveReal.IntegerRowSpace
open ConstructiveReal
open FiniteLinear
open Distros.RationalLinear

/-- Only nonzero integer pivots are inverted. The sign case distinction is
finite arithmetic, never a comparison or equality test on analytic values. -/
def integerInverse (value : Int) (nonzero : value ≠ 0) : SignedRatio := by
  cases value with
  | ofNat n => exact ⟨1, n, by have : (n : Int) ≠ 0 := nonzero; omega⟩
  | negSucc n => exact ⟨-1, n + 1, Nat.zero_lt_succ _⟩

theorem integer_mul_inverse (value : Int) (nonzero : value ≠ 0) :
    Equiv (mul (realInteger value) (ofSignedRatio (integerInverse value nonzero))) one := by
  apply equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr ?_)
  cases value <;> simp [integerInverse, SignedRatio.Equiv, SignedRatio.mul, SignedRatio.one, Int.negSucc_eq]

private abbrev Expr := RationalPolynomial.Expression 6
private def a : Expr := .coordinate 0
private def g : Expr := .coordinate 1
private def h : Expr := .coordinate 2
private def b : Expr := .coordinate 3
private def k : Expr := .coordinate 4
private def z : Expr := .coordinate 5
private def gapLeft : Expr := .sub (.sub (.mul a g) (.mul b k)) (.sub (.mul a h) (.mul b z))
private def gapRight : Expr := .sub (.mul a (.sub g h)) (.mul b (.sub k z))

private theorem gap_identity (av gv hv bv kv zv : ConstructiveReal) :
    Equiv (sub (sub (mul av gv) (mul bv kv)) (sub (mul av hv) (mul bv zv)))
      (sub (mul av (sub gv hv)) (mul bv (sub kv zv))) :=
  RationalPolynomial.Expression.equalityCheck_sound_real gapLeft gapRight (by decide +kernel)
    (fun i => if i.val = 0 then av else if i.val = 1 then gv else if i.val = 2 then hv else if i.val = 3 then bv else if i.val = 4 then kv else zv)

private theorem sub_add_cancel (first second : ConstructiveReal) : Equiv (add (sub first second) second) first :=
  equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (equiv_trans (add_comm _ _) (add_neg second))) (add_zero first))

/-- Back-substitution uses only a certified inverse of the integer pivot.
The remaining coefficients and gradient coordinates can be analytic. -/
private theorem reconstruct (pivot : Int) (nonzero : pivot ≠ 0) (gv hv bv kv zv : ConstructiveReal)
    (same : Equiv (sub (mul (realInteger pivot) gv) (mul bv kv)) (sub (mul (realInteger pivot) hv) (mul bv zv))) :
    Equiv gv (add (mul bv (mul (ofSignedRatio (integerInverse pivot nonzero)) (sub kv zv))) hv) := by
  let inverse := ofSignedRatio (integerInverse pivot nonzero)
  have inverseLaw : Equiv (mul inverse (realInteger pivot)) one :=
    equiv_trans (mul_comm _ _) (integer_mul_inverse pivot nonzero)
  have gap := equiv_trans (equiv_symm (gap_identity (realInteger pivot) gv hv bv kv zv))
    ((sub_equiv_zero_iff _ _).mpr same)
  have equation := (sub_equiv_zero_iff _ _).mp gap
  have scaled := mul_congr (equiv_refl inverse) equation
  have left : Equiv (mul inverse (mul (realInteger pivot) (sub gv hv))) (sub gv hv) :=
    equiv_trans (equiv_symm (mul_assoc _ _ _)) (equiv_trans (mul_congr inverseLaw (equiv_refl _)) (one_mul _))
  have right : Equiv (mul inverse (mul bv (sub kv zv))) (mul bv (mul inverse (sub kv zv))) :=
    equiv_trans (equiv_symm (mul_assoc _ _ _)) (equiv_trans (mul_congr (mul_comm inverse bv) (equiv_refl _)) (mul_assoc _ _ _))
  have difference := equiv_trans (equiv_symm left) (equiv_trans scaled right)
  exact equiv_trans (equiv_symm (sub_add_cancel gv hv)) (add_congr difference (equiv_refl hv))

private theorem reduced_column (matrix : Matrix (rows + 1) (columns + 1)) (column : Fin columns)
    (multipliers : Fin rows → ConstructiveReal) :
    Equiv (realDot rows (fun row => reduced matrix row column) multipliers)
      (sub (mul (realInteger (matrix (Fin.last rows) (Fin.last columns))) (realDot rows (fun row => matrix row.castSucc column.castSucc) multipliers))
        (mul (realInteger (matrix (Fin.last rows) column.castSucc)) (realDot rows (fun row => matrix row.castSucc (Fin.last columns)) multipliers))) := by
  have second : Equiv (realDot rows (fun row => matrix row.castSucc (Fin.last columns) * matrix (Fin.last rows) column.castSucc) multipliers)
      (mul (realInteger (matrix (Fin.last rows) column.castSucc)) (realDot rows (fun row => matrix row.castSucc (Fin.last columns)) multipliers)) := by
    have same : (fun row : Fin rows => matrix row.castSucc (Fin.last columns) * matrix (Fin.last rows) column.castSucc) =
        (fun row => matrix (Fin.last rows) column.castSucc * matrix row.castSucc (Fin.last columns)) := funext (fun _ => Int.mul_comm _ _)
    rw [same]
    exact realDot_scale_coefficients rows _ _ multipliers
  exact equiv_trans (realDot_sub_coefficients rows _ _ multipliers)
    (add_congr (realDot_scale_coefficients rows _ _ multipliers) (neg_congr second))

def liftMultipliers (matrix : Matrix (rows + 1) (columns + 1)) (gradient : Fin (columns + 1) → ConstructiveReal)
    (nonzero : matrix (Fin.last rows) (Fin.last columns) ≠ 0)
    (found : Multipliers (reduced matrix) (reducedGradient matrix gradient)) : Multipliers matrix gradient := by
  let pivot := matrix (Fin.last rows) (Fin.last columns)
  let previous := realDot rows (fun row => matrix row.castSucc (Fin.last columns)) found.value
  let last := mul (ofSignedRatio (integerInverse pivot nonzero)) (sub (gradient (Fin.last columns)) previous)
  refine ⟨FiniteLinear.extend found.value last, ?_⟩
  intro column
  refine Fin.lastCases ?_ (fun earlier => ?_) column
  · have evaluation := realDot_extend rows (fun row => matrix row (Fin.last columns)) found.value last
    have canceled : Equiv (mul (realInteger pivot) last) (sub (gradient (Fin.last columns)) previous) :=
      equiv_trans (equiv_symm (mul_assoc _ _ _))
        (equiv_trans (mul_congr (integer_mul_inverse pivot nonzero) (equiv_refl _)) (one_mul _))
    exact equiv_symm (equiv_trans evaluation (equiv_trans (add_congr canceled (equiv_refl previous)) (sub_add_cancel _ _)))
  · have equation := equiv_trans (add_congr (equiv_refl _)
      (neg_congr (mul_comm (realInteger (matrix (Fin.last rows) earlier.castSucc)) (gradient (Fin.last columns)))))
      (equiv_trans (found.represents earlier) (reduced_column matrix earlier found.value))
    have result := reconstruct pivot nonzero (gradient earlier.castSucc)
      (realDot rows (fun row => matrix row.castSucc earlier.castSucc) found.value)
      (realInteger (matrix (Fin.last rows) earlier.castSucc)) (gradient (Fin.last columns)) previous equation
    exact equiv_trans result (equiv_symm (realDot_extend rows (fun row => matrix row earlier.castSucc) found.value last))

/-- Construct coefficients of the original rows from annihilation of their
analytic kernel. Recursion tests only explicit integer entries; zero and
redundant rows require no independence hypothesis. The output contains the
coefficients themselves, not a choice from an existential proposition. -/
def ofAnnihilator (rows columns : Nat) (matrix : Matrix rows columns) (gradient : Fin columns → ConstructiveReal)
    (annihilates : AnnihilatesKernel matrix gradient) : Multipliers matrix gradient := by
  induction rows generalizing columns with
  | zero =>
      refine ⟨(fun row => Fin.elim0 row), ?_⟩
      intro column
      have vanished := annihilates (fun i => realInteger (if i = column then 1 else 0)) (fun row => Fin.elim0 row)
      have recovered := equiv_trans (pair_comm columns gradient _) (pair_unit columns column gradient)
      exact equiv_trans (equiv_symm recovered) vanished
  | succ rows ih =>
      cases columns with
      | zero => exact ⟨fun _ => zero, fun column => Fin.elim0 column⟩
      | succ columns =>
          cases searched : IntegerLinearAlgebra.findNonzero (matrix (Fin.last rows)) with
          | none =>
              have zeroRow : matrix (Fin.last rows) = (fun _ => 0) := funext (IntegerLinearAlgebra.findNonzero_none _ searched)
              have previous : AnnihilatesKernel (fun row : Fin rows => matrix row.castSucc) gradient := by
                intro values valid
                apply annihilates values
                intro row
                refine Fin.lastCases ?_ (fun i => valid i) row
                rw [zeroRow]
                exact realDot_zero _ values
              let found := ih (columns + 1) (fun row => matrix row.castSucc) gradient previous
              refine ⟨FiniteLinear.extend found.value zero, ?_⟩
              intro column
              have evaluation := equiv_trans (realDot_extend rows (fun row => matrix row column) found.value zero)
                (equiv_trans (add_congr (mul_zero _) (equiv_refl _)) (zero_add _))
              exact equiv_trans (found.represents column) (equiv_symm evaluation)
          | some column =>
              let swapped : Matrix (rows + 1) (columns + 1) := fun row => IntegerLinearAlgebra.swapVector (matrix row) column (Fin.last columns)
              let swappedGradient := swap gradient column (Fin.last columns)
              have nonzero : swapped (Fin.last rows) (Fin.last columns) ≠ 0 := by
                simpa only [swapped, IntegerLinearAlgebra.swapVector, IntegerLinearAlgebra.swapIndex_second] using
                  IntegerLinearAlgebra.findNonzero_some _ column searched
              have previous := annihilates_reduced swapped swappedGradient (annihilates_swapped matrix gradient annihilates column (Fin.last columns))
              let found := ih columns (reduced swapped) (reducedGradient swapped swappedGradient) previous
              exact unswapMultipliers matrix gradient column (Fin.last columns) (liftMultipliers swapped swappedGradient nonzero found)

end Thesis.Probability.ConstructiveReal.IntegerRowSpace
