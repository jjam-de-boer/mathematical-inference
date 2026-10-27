import Thesis.Probability.ConstructiveRealSimplex
import Thesis.Probability.Distros.ShiftedMoments

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

/-- Negating integer coefficients negates the analytic row value. -/
theorem realDot_negated_coefficients (variables : Nat) (coefficients : Fin variables → Int)
    (values : Fin variables → ConstructiveReal) :
    Equiv (realDot variables (fun i => -coefficients i) values) (neg (realDot variables coefficients values)) :=
  equiv_trans (by simpa only [Int.neg_one_mul] using realDot_scale_coefficients variables (-1) coefficients values)
    (equiv_trans (mul_congr (ofSignedRatio_neg SignedRatio.one) (equiv_refl _))
      (equiv_trans (neg_mul one _) (neg_congr (one_mul _))))

/-- The two original mass inequalities imply exact analytic normalization. -/
theorem real_simplex_normalized (values : Fin variables → ConstructiveReal)
    (valid : RealSatisfies (simplexRows variables) values) :
    Equiv (realDot variables (fun _ => 1) values) one := by
  have upper := valid (upperMassRow variables) (List.mem_append_right _ (List.mem_cons_self ..))
  have lower := valid (lowerMassRow variables)
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have reversed := (le_congr (realDot_negated_coefficients variables (fun _ => 1) values)
    (ofSignedRatio_neg SignedRatio.one)).mp lower
  exact ⟨upper, (neg_le_neg_iff one _).mp reversed⟩

/-- Constant responses have their constant value on a normalized vector. -/
theorem realDot_constant_normalized (variables : Nat) (factor : Int) (values : Fin variables → ConstructiveReal)
    (normalized : Equiv (realDot variables (fun _ => 1) values) one) :
    Equiv (realDot variables (fun _ => factor) values) (realInteger factor) := by
  have scaled := realDot_scale_coefficients variables factor (fun _ => 1) values
  simp only [Int.mul_one] at scaled
  exact equiv_trans scaled (equiv_trans (mul_congr (equiv_refl _) normalized) (mul_one _))

private def coordinateGrid (variables : Nat) : EntropyGrid (Fin variables) :=
  ⟨List.finRange variables, Probability.finRange_nodup variables⟩

/-- Computed integer lower bound for a finite response, independent of a
probability law, strict positivity or independence of constraint rows. -/
def coefficientLower (variables : Nat) (coefficients : Fin variables → Int) : Int :=
  -((coordinateGrid variables).responseShift coefficients : Int)

theorem coefficientLower_le (variables : Nat) (coefficients : Fin variables → Int) (index : Fin variables) :
    coefficientLower variables coefficients ≤ coefficients index := by
  have identity := (coordinateGrid variables).shiftedResponse_spec coefficients index (List.mem_finRange index)
  have positive : 0 ≤ ((coordinateGrid variables).shiftedResponse coefficients index : Int) := Int.natCast_nonneg _
  change -((coordinateGrid variables).responseShift coefficients : Int) ≤ coefficients index
  omega

/-- Every finite integer response has a proved lower bound on the closed
simplex, including forced-zero coordinates. This supplies a redundant lower
endpoint when a one-sided rational inequality is encoded as a moment band. -/
theorem realDot_lower_normalized (variables : Nat) (coefficients : Fin variables → Int)
    (values : Fin variables → ConstructiveReal) (nonnegative : ∀ i, LE zero (values i))
    (normalized : Equiv (realDot variables (fun _ => 1) values) one) :
    LE (realInteger (coefficientLower variables coefficients)) (realDot variables coefficients values) :=
  (le_congr (realDot_constant_normalized variables (coefficientLower variables coefficients) values normalized)
    (equiv_refl _)).mp
    (realDot_mono_coefficients variables (fun _ => coefficientLower variables coefficients) coefficients values
      nonnegative (coefficientLower_le variables coefficients))

/-- Reindexing by an equality of finite dimensions preserves row evaluation.
The equality is supplied by finite list lengths, not by a real comparison. -/
theorem realDot_cast (first second : Nat) (same : first = second) (coefficients : Fin first → Int)
    (values : Fin first → ConstructiveReal) :
    Equiv (realDot first coefficients values)
      (realDot second (fun i => coefficients (Fin.cast same.symm i)) (fun i => values (Fin.cast same.symm i))) := by
  cases same
  exact equiv_refl _

end Thesis.Probability.Distros.RationalLinear
