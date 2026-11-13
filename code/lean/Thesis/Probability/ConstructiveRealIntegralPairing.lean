import Thesis.Probability.ConstructiveRealBilinearFubini
import Thesis.Probability.ConstructiveRealKernelElimination

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal
open IntegerLinearAlgebra

/-- Interpreting a finite integer scalar product agrees exactly with the
analytic row evaluation. The integer equality itself remains decidable. -/
theorem realDot_integers (size : Nat) (first second : Fin size → Int) :
    Equiv (realDot size first (fun i => realInteger (second i))) (realInteger (IntegerLinearAlgebra.dot first second)) := by
  induction size with
  | zero => exact equiv_refl zero
  | succ size ih =>
      rw [dot_succ]
      exact equiv_trans (add_congr (realInteger_mul _ _)
        (ih (fun i => first i.castSucc) (fun i => second i.castSucc)))
        (equiv_trans (add_comm _ _) (realInteger_add _ _))

theorem realInteger_injective (first second : Int) (same : Equiv (realInteger first) (realInteger second)) : first = second := by
  have rational := (ofSignedRatio_equiv_iff _ _).mp same
  simpa only [SignedRatio.Equiv, Int.natCast_one, Int.mul_one] using rational

/-- Integral coordinate selectors are verified through the already proved
analytic selector identity and the faithful integral interpretation. -/
theorem integerDot_unit (size : Nat) (index : Fin size) (values : Fin size → Int) :
    IntegerLinearAlgebra.dot (fun i => if i = index then 1 else 0) values = values index :=
  realInteger_injective _ _ (equiv_trans (equiv_symm (realDot_integers size _ values))
    (realDot_unit size index (fun i => realInteger (values i))))

/-- Integral row evaluation commutes with signed scalar multiplication of
analytic coordinates. -/
theorem realDot_scale_left_values (size : Nat) (coefficients : Fin size → Int)
    (factor : ConstructiveReal) (values : Fin size → ConstructiveReal) :
    Equiv (realDot size coefficients (fun i => mul factor (values i)))
      (mul factor (realDot size coefficients values)) :=
  equiv_trans (FiniteLinear.realDot_pair size coefficients _)
    (equiv_trans (FiniteLinear.pair_scale_second size factor _ values)
      (mul_congr (equiv_refl factor) (equiv_symm (FiniteLinear.realDot_pair size coefficients values))))

/-- Negating analytic coordinates negates every integral row evaluation. -/
theorem realDot_neg_values (size : Nat) (coefficients : Fin size → Int) (values : Fin size → ConstructiveReal) :
    Equiv (realDot size coefficients (fun i => neg (values i))) (neg (realDot size coefficients values)) := by
  induction size with
  | zero => exact ofSignedRatio_neg SignedRatio.zero
  | succ size ih =>
      exact equiv_trans (add_congr (mul_neg _ _) (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc)))
        (equiv_symm (neg_add _ _))

theorem realInteger_neg (value : Int) : Equiv (realInteger (-value)) (neg (realInteger value)) :=
  ofSignedRatio_neg ⟨value, 1, by decide⟩

theorem realInteger_sub (first second : Int) :
    Equiv (sub (realInteger first) (realInteger second)) (realInteger (first - second)) := by
  rw [Int.sub_eq_add_neg]
  exact equiv_trans (add_congr (equiv_refl _) (equiv_symm (realInteger_neg second))) (realInteger_add _ _)

end Thesis.Probability.Distros.RationalLinear
