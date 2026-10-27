import Thesis.Probability.ConstructiveRealFiniteLinear

namespace Thesis.Probability.ConstructiveReal.FiniteLinear
open ConstructiveReal
open Distros.RationalLinear

theorem pair_zero_first (size : Nat) (values : Fin size → ConstructiveReal) :
    Equiv (pair size (fun _ => zero) values) zero :=
  equiv_trans (equiv_symm (realDot_pair size (fun _ => 0) values)) (realDot_zero size values)

theorem pair_zero_second (size : Nat) (values : Fin size → ConstructiveReal) :
    Equiv (pair size values (fun _ => zero)) zero :=
  equiv_trans (pair_comm size values (fun _ => zero)) (pair_zero_first size values)

theorem pair_sub_second (size : Nat) (values first second : Fin size → ConstructiveReal) :
    Equiv (pair size values (fun i => sub (first i) (second i)))
      (sub (pair size values first) (pair size values second)) :=
  equiv_trans (pair_comm _ _ _) (equiv_trans (pair_sub_first _ _ _ _)
    (add_congr (pair_comm _ _ _) (neg_congr (pair_comm _ _ _))))

theorem pair_constant_kernel (size : Nat) (constant : ConstructiveReal) (directions : Fin size → ConstructiveReal)
    (normalized : Equiv (realDot size (fun _ => 1) directions) zero) :
    Equiv (pair size (fun _ => constant) directions) zero := by
  have expanded : Equiv (pair size (fun _ => constant) directions)
      (mul constant (realDot size (fun _ => 1) directions)) :=
    equiv_trans (pair_congr size _ (fun _ => mul constant one) directions directions
      (fun _ => equiv_symm (mul_one constant)) (fun _ => equiv_refl _))
      (equiv_trans (pair_scale_first size constant (fun _ => one) directions)
        (mul_congr (equiv_refl _) (equiv_symm (realDot_pair size (fun _ => 1) directions))))
  exact equiv_trans expanded (equiv_trans (mul_congr (equiv_refl _) normalized) (mul_zero constant))

/-- Finite bilinear Fubini with arbitrary analytic matrix entries. This
identity uses only finite sums and arithmetic, not matrix rank or a test
of equality between analytic values. -/
theorem combination_pair (rows columns : Nat) (matrix : Fin rows → Fin columns → ConstructiveReal)
    (coefficients : Fin rows → ConstructiveReal) (directions : Fin columns → ConstructiveReal) :
    Equiv (pair columns (fun column => pair rows coefficients (fun row => matrix row column)) directions)
      (pair rows coefficients (fun row => pair columns (matrix row) directions)) := by
  induction rows generalizing columns with
  | zero => exact pair_zero_first columns directions
  | succ rows ih =>
      have expanded : Equiv (pair columns (fun column => pair (rows + 1) coefficients (fun row => matrix row column)) directions)
          (pair columns (fun column => add
            (pair rows (fun row => coefficients row.castSucc) (fun row => matrix row.castSucc column))
            (mul (coefficients (Fin.last rows)) (matrix (Fin.last rows) column))) directions) :=
        pair_congr columns _ _ directions directions (fun column => pair_succ rows coefficients (fun row => matrix row column)) (fun _ => equiv_refl _)
      exact equiv_trans expanded (equiv_trans (pair_add_first columns _ _ directions)
        (equiv_trans (add_congr (ih columns (fun row => matrix row.castSucc) (fun row => coefficients row.castSucc) directions)
          (pair_scale_first columns (coefficients (Fin.last rows)) (matrix (Fin.last rows)) directions))
          (equiv_symm (pair_succ rows coefficients (fun row => pair columns (matrix row) directions)))))

end Thesis.Probability.ConstructiveReal.FiniteLinear
