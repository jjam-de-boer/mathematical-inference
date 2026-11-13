import Thesis.Probability.ConstructiveRealRowSpace

namespace Thesis.Probability.ConstructiveReal.IntegerRowSpace
open ConstructiveReal
open FiniteLinear
open Distros.RationalLinear

private theorem pair_zero_first (size : Nat) (values : Fin size → ConstructiveReal) :
    Equiv (pair size (fun _ => zero) values) zero :=
  equiv_trans (equiv_symm (realDot_pair size (fun _ => 0) values)) (realDot_zero size values)

/-- Finite bilinear transposition for original integer rows. This is the
algebraic identity behind the converse kernel/row-space implication. -/
theorem combination_pair (rows columns : Nat) (matrix : Matrix rows columns)
    (coefficients : Fin rows → ConstructiveReal) (directions : Fin columns → ConstructiveReal) :
    Equiv (pair columns (fun column => realDot rows (fun row => matrix row column) coefficients) directions)
      (pair rows coefficients (fun row => realDot columns (matrix row) directions)) := by
  induction rows generalizing columns with
  | zero => exact pair_zero_first columns directions
  | succ rows ih =>
      have first : Equiv
          (pair columns (fun column => mul (realInteger (matrix (Fin.last rows) column)) (coefficients (Fin.last rows))) directions)
          (mul (coefficients (Fin.last rows)) (realDot columns (matrix (Fin.last rows)) directions)) :=
        equiv_trans (pair_congr columns _ _ directions directions (fun _ => mul_comm _ _) (fun _ => equiv_refl _))
          (equiv_trans (pair_scale_first columns (coefficients (Fin.last rows)) _ directions)
            (mul_congr (equiv_refl _) (equiv_symm (realDot_pair columns _ directions))))
      change Equiv (pair columns (fun column => add
        (mul (realInteger (matrix (Fin.last rows) column)) (coefficients (Fin.last rows)))
        (realDot rows (fun row => matrix row.castSucc column) (fun row => coefficients row.castSucc))) directions) _
      exact equiv_trans (pair_add_first columns _ _ directions)
        (equiv_trans (add_congr first (ih columns (fun row => matrix row.castSucc) (fun row => coefficients row.castSucc) directions))
          (equiv_trans (add_comm _ _) (equiv_symm (pair_succ rows coefficients (fun row => realDot columns (matrix row) directions)))))

/-- Every actual row combination annihilates the original analytic kernel. -/
theorem Multipliers.annihilates {matrix : Matrix rows columns} {gradient : Fin columns → ConstructiveReal}
    (certificate : Multipliers matrix gradient) : AnnihilatesKernel matrix gradient := by
  intro directions valid
  exact equiv_trans (pair_congr columns _ _ directions directions certificate.represents (fun _ => equiv_refl _))
    (equiv_trans (combination_pair rows columns matrix certificate.value directions)
      (equiv_trans (pair_congr rows certificate.value certificate.value _ (fun _ => zero) (fun _ => equiv_refl _) valid)
        (equiv_trans (pair_comm rows certificate.value (fun _ => zero)) (pair_zero_first rows certificate.value))))

/-- The usual annihilator/row-space equivalence, with the forward
construction supplied by `ofAnnihilator` as explicit computable data. -/
theorem multipliers_iff_annihilates (matrix : Matrix rows columns) (gradient : Fin columns → ConstructiveReal) :
    Nonempty (Multipliers matrix gradient) ↔ AnnihilatesKernel matrix gradient :=
  ⟨fun ⟨certificate⟩ => certificate.annihilates, fun valid => ⟨ofAnnihilator rows columns matrix gradient valid⟩⟩

end Thesis.Probability.ConstructiveReal.IntegerRowSpace
