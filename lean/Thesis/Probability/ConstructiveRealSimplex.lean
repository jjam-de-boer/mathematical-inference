import Thesis.Probability.ConstructiveRealFeasibleApproximation
import Thesis.Probability.Distros.RationalSimplex

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

private theorem realDot_neg_coefficients (variables : Nat) (coefficients : Fin variables → Int) (values : Fin variables → ConstructiveReal) :
    Equiv (realDot variables (fun i => -coefficients i) values) (neg (realDot variables coefficients values)) :=
  equiv_trans (by simpa only [Int.neg_one_mul] using realDot_scale_coefficients variables (-1) coefficients values)
    (equiv_trans (mul_congr (ofSignedRatio_neg SignedRatio.one) (equiv_refl _))
      (equiv_trans (neg_mul one _) (neg_congr (one_mul _))))

theorem realDot_mono_coefficients (variables : Nat) (first second : Fin variables → Int) (values : Fin variables → ConstructiveReal)
    (nonnegative : ∀ i, LE zero (values i)) (compared : ∀ i, first i ≤ second i) :
    LE (realDot variables first values) (realDot variables second values) := by
  induction variables with
  | zero => exact le_refl zero
  | succ variables ih =>
      have factor : LE (realInteger (first (Fin.last variables))) (realInteger (second (Fin.last variables))) :=
        (ofSignedRatio_le_iff _ _).mpr (by
          rw [SignedRatio.le_iff_cross]
          simpa only [Int.natCast_one, Int.mul_one] using compared (Fin.last variables))
      exact add_le_add (mul_le_mul_nonnegative_right (nonnegative (Fin.last variables)) factor)
        (ih (fun i => first i.castSucc) (fun i => second i.castSucc) (fun i => values i.castSucc)
          (fun i => nonnegative i.castSucc) (fun i => compared i.castSucc))

/-- The original simplex rows imply every real coordinate lies in [0,1].
Thus the entropy domain certificates impose no extra condition on the ideal
feasible polytope. Their proofs require no decision of real sign or equality. -/
theorem real_simplex_bounds (values : Fin variables → ConstructiveReal) (valid : RealSatisfies (simplexRows variables) values) :
    ∀ index, LE zero (values index) ∧ LE (values index) one := by
  have nonnegative (index : Fin variables) : LE zero (values index) := by
    have original := valid (nonnegativeRow variables index)
      (List.mem_append_left _ (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩))
    have negated : LE (neg (values index)) (neg zero) :=
      (le_congr (realDot_negative_unit variables index values) (ofSignedRatio_neg SignedRatio.zero)).mp original
    exact (neg_le_neg_iff zero (values index)).mp negated
  have upper : LE (realDot variables (fun _ => 1) values) one :=
    valid (upperMassRow variables) (List.mem_append_right _ (List.mem_cons_self ..))
  have lower := valid (lowerMassRow variables)
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have normalized : Equiv (realDot variables (fun _ => 1) values) one := by
    refine ⟨upper, ?_⟩
    have negated : LE (neg (realDot variables (fun _ => 1) values)) (neg one) :=
      (le_congr (realDot_neg_coefficients variables (fun _ => 1) values) (ofSignedRatio_neg SignedRatio.one)).mp lower
    exact (neg_le_neg_iff one _).mp negated
  intro index
  refine ⟨nonnegative index, ?_⟩
  have coefficientBound (i : Fin variables) : (if i = index then (1 : Int) else 0) ≤ 1 := by
    by_cases same : i = index <;> simp only [same, if_true, if_false] <;> decide
  exact (le_congr (realDot_unit variables index values) normalized).mp
    (realDot_mono_coefficients variables _ _ values nonnegative coefficientBound)

end Thesis.Probability.Distros.RationalLinear
