import Thesis.Probability.ConstructiveRealOrderedRing
import Thesis.Probability.Distros.RationalLinearSolve

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

/-- The same finite rational constraint rows can be interpreted on auxiliary
real assignments. No arbitrary real comparison is made decidable. -/
def realInteger (factor : Int) : ConstructiveReal := ofSignedRatio ⟨factor, 1, Nat.zero_lt_one⟩

theorem realInteger_add (first second : Int) :
    Equiv (add (realInteger first) (realInteger second)) (realInteger (first + second)) :=
  equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by
    simp only [SignedRatio.Equiv, SignedRatio.add, Nat.one_mul, Int.natCast_one, Int.mul_one]))

theorem realInteger_mul (first second : Int) :
    Equiv (mul (realInteger first) (realInteger second)) (realInteger (first * second)) :=
  equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by
    simp only [SignedRatio.Equiv, SignedRatio.mul, Nat.one_mul, Int.natCast_one, Int.mul_one]))

private theorem realInteger_nonnegative (factor : Int) (positive : 0 ≤ factor) : LE zero (realInteger factor) :=
  (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr positive)

def realDot : (variables : Nat) → (Fin variables → Int) → (Fin variables → ConstructiveReal) → ConstructiveReal
  | 0, _, _ => zero
  | variables + 1, coefficients, values =>
      add (mul (realInteger (coefficients (Fin.last variables))) (values (Fin.last variables)))
        (realDot variables (fun i => coefficients i.castSucc) (fun i => values i.castSucc))

def Inequality.RealHolds (row : Inequality variables) (values : Fin variables → ConstructiveReal) : Prop :=
  LE (realDot variables row.coefficients values) (ofSignedRatio row.bound)

def RealSatisfies (rows : List (Inequality variables)) (values : Fin variables → ConstructiveReal) : Prop :=
  ∀ row ∈ rows, row.RealHolds values

theorem realDot_ofSignedRatio (variables : Nat) (coefficients : Fin variables → Int) (values : Fin variables → SignedRatio) :
    Equiv (realDot variables coefficients (fun i => ofSignedRatio (values i))) (ofSignedRatio (dot variables coefficients values)) := by
  induction variables with
  | zero => exact equiv_refl zero
  | succ variables ih =>
      exact equiv_trans (add_congr (ofSignedRatio_mul _ _) (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc)))
        (ofSignedRatio_add _ _)

theorem realDot_add_coefficients (variables : Nat) (first second : Fin variables → Int) (values : Fin variables → ConstructiveReal) :
    Equiv (realDot variables (fun i => first i + second i) values)
      (add (realDot variables first values) (realDot variables second values)) := by
  induction variables with
  | zero => exact equiv_symm (add_zero zero)
  | succ variables ih =>
      have factor : Equiv
          (mul (realInteger (first (Fin.last variables) + second (Fin.last variables))) (values (Fin.last variables)))
          (add (mul (realInteger (first (Fin.last variables))) (values (Fin.last variables)))
            (mul (realInteger (second (Fin.last variables))) (values (Fin.last variables)))) :=
        equiv_trans (mul_congr (equiv_symm (realInteger_add _ _)) (equiv_refl _)) (add_mul _ _ _)
      exact equiv_trans (add_congr factor (ih (fun i => first i.castSucc) (fun i => second i.castSucc) (fun i => values i.castSucc)))
        (add_four _ _ _ _)

theorem realDot_scale_coefficients (variables : Nat) (factor : Int) (coefficients : Fin variables → Int) (values : Fin variables → ConstructiveReal) :
    Equiv (realDot variables (fun i => factor * coefficients i) values) (mul (realInteger factor) (realDot variables coefficients values)) := by
  induction variables with
  | zero => exact equiv_symm (mul_zero _)
  | succ variables ih =>
      have product : Equiv (mul (realInteger (factor * coefficients (Fin.last variables))) (values (Fin.last variables)))
          (mul (realInteger factor) (mul (realInteger (coefficients (Fin.last variables))) (values (Fin.last variables)))) :=
        equiv_trans (mul_congr (equiv_symm (realInteger_mul _ _)) (equiv_refl _)) (mul_assoc _ _ _)
      exact equiv_trans (add_congr product (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc)))
        (equiv_symm (mul_add _ _ _))

theorem realDot_zero (variables : Nat) (values : Fin variables → ConstructiveReal) :
    Equiv (realDot variables (fun _ => 0) values) zero := by
  induction variables with
  | zero => exact equiv_refl zero
  | succ variables ih =>
      exact equiv_trans (add_congr (zero_mul _) (ih (fun i => values i.castSucc))) (zero_add zero)

/-- A coordinate selector has the same meaning on rational and real assignments. -/
theorem realDot_unit (variables : Nat) (index : Fin variables) (values : Fin variables → ConstructiveReal) :
    Equiv (realDot variables (fun i => if i = index then 1 else 0) values) (values index) := by
  induction variables with
  | zero => exact Fin.elim0 index
  | succ variables ih =>
      by_cases last : index = Fin.last variables
      · subst index
        have earlier : (fun i : Fin variables => if i.castSucc = Fin.last variables then (1 : Int) else 0) = (fun _ => 0) := by
          funext i
          have different : i.castSucc ≠ Fin.last variables := by
            intro same
            have value := congrArg Fin.val same
            simp only [Fin.val_castSucc, Fin.val_last] at value
            have bound := i.isLt
            omega
          exact if_neg different
        change Equiv (add (mul (realInteger (if Fin.last variables = Fin.last variables then 1 else 0)) (values (Fin.last variables)))
          (realDot variables _ (fun i => values i.castSucc))) _
        simp only [if_true, earlier]
        exact equiv_trans (add_congr (one_mul _) (realDot_zero variables _)) (add_zero _)
      · have before : index.val < variables := by
          have bound := index.isLt
          have notLast : index.val ≠ variables := by intro same; exact last (Fin.ext same)
          omega
        let old : Fin variables := ⟨index.val, before⟩
        have same : index = old.castSucc := Fin.ext rfl
        rw [same]
        have different : Fin.last variables ≠ old.castSucc := by
          intro reversed
          exact last (same.trans reversed.symm)
        change Equiv (add (mul (realInteger (if Fin.last variables = old.castSucc then 1 else 0)) (values (Fin.last variables)))
          (realDot variables _ (fun i => values i.castSucc))) _
        simp only [if_neg different, Fin.castSucc_inj]
        exact equiv_trans (add_congr (zero_mul _) (ih old (fun i => values i.castSucc))) (zero_add _)

/-- Positive integer row combination cancels the eliminated coordinate in
real arithmetic, exactly as in the rational elimination trace. -/
theorem real_combine_sound (upper lower : Inequality (variables + 1)) (values : Fin (variables + 1) → ConstructiveReal)
    (positive : 0 < upper.pivot) (negative : lower.pivot < 0)
    (upperHolds : upper.RealHolds values) (lowerHolds : lower.RealHolds values) :
    (combine upper lower).RealHolds (fun i => values i.castSucc) := by
  let coefficients := fun i => -lower.pivot * upper.coefficients i + upper.pivot * lower.coefficients i
  have combined : Equiv (realDot (variables + 1) coefficients values)
      (add (mul (realInteger (-lower.pivot)) (realDot (variables + 1) upper.coefficients values))
        (mul (realInteger upper.pivot) (realDot (variables + 1) lower.coefficients values))) :=
    equiv_trans (realDot_add_coefficients _ _ _ values)
      (add_congr (realDot_scale_coefficients _ _ _ values) (realDot_scale_coefficients _ _ _ values))
  have canceled : -lower.pivot * upper.pivot + upper.pivot * lower.pivot = 0 := by
    rw [Int.neg_mul, Int.mul_comm upper.pivot lower.pivot]
    omega
  have reduced : Equiv (realDot (variables + 1) coefficients values)
      (realDot variables (combine upper lower).coefficients (fun i => values i.castSucc)) := by
    change Equiv (add (mul (realInteger (-lower.pivot * upper.pivot + upper.pivot * lower.pivot)) (values (Fin.last variables))) _) _
    rw [canceled]
    exact equiv_trans (add_congr (zero_mul _) (equiv_refl _)) (zero_add _)
  have scaled := add_le_add (mul_le_mul_nonnegative (realInteger_nonnegative (-lower.pivot) (by omega)) upperHolds)
    (mul_le_mul_nonnegative (realInteger_nonnegative upper.pivot (by omega)) lowerHolds)
  have bound : Equiv
      (add (mul (realInteger (-lower.pivot)) (ofSignedRatio upper.bound))
        (mul (realInteger upper.pivot) (ofSignedRatio lower.bound))) (ofSignedRatio (combine upper lower).bound) :=
    equiv_trans (add_congr (ofSignedRatio_mul _ _) (ofSignedRatio_mul _ _)) (ofSignedRatio_add _ _)
  exact (le_congr (equiv_trans (equiv_symm combined) reduced) bound).mp scaled

/-- Soundness of real projection needs only finite rational row signs; it
does not select or compare the real coordinates. -/
theorem real_project_sound (rows : List (Inequality (variables + 1))) (values : Fin (variables + 1) → ConstructiveReal)
    (valid : RealSatisfies rows values) : RealSatisfies (project rows) (fun i => values i.castSucc) := by
  intro row member
  rcases List.mem_append.mp member with unchanged | paired
  · rcases List.mem_map.mp unchanged with ⟨source, listed, same⟩
    cases same
    have pivotZero := of_decide_eq_true (List.mem_filter.mp listed).2
    have reduced : Equiv (realDot (variables + 1) source.coefficients values)
        (realDot variables source.trim.coefficients (fun i => values i.castSucc)) := by
      change Equiv (add (mul (realInteger source.pivot) (values (Fin.last variables))) _) _
      rw [pivotZero]
      exact equiv_trans (add_congr (zero_mul _) (equiv_refl _)) (zero_add _)
    exact (le_congr reduced (equiv_refl _)).mp (valid source (List.mem_filter.mp listed).1)
  · rcases List.mem_flatMap.mp paired with ⟨upper, upperListed, lowerRows⟩
    rcases List.mem_map.mp lowerRows with ⟨lower, lowerListed, same⟩
    cases same
    exact real_combine_sound upper lower values (of_decide_eq_true (List.mem_filter.mp upperListed).2)
      (of_decide_eq_true (List.mem_filter.mp lowerListed).2)
      (valid upper (List.mem_filter.mp upperListed).1) (valid lower (List.mem_filter.mp lowerListed).1)

/-- A rational infeasibility certificate rules out real solutions as well.
This is a theorem about the existing finite trace, not a real feasibility
oracle or an additional constructor assumption. -/
theorem Infeasibility.not_real (certificate : Infeasibility variables rows) :
    ¬ ∃ values : Fin variables → ConstructiveReal, RealSatisfies rows values := by
  induction certificate with
  | constant rows row member negative =>
      rintro ⟨values, valid⟩
      have rational := (ofSignedRatio_le_iff SignedRatio.zero row.bound).mp (valid row member)
      have nonnegative := (SignedRatio.zero_le_iff_nonnegative _).mp rational
      change 0 ≤ row.bound.num at nonnegative
      omega
  | projected rows previous ih =>
      rintro ⟨values, valid⟩
      exact ih ⟨fun i => values i.castSucc, real_project_sound rows values valid⟩

end Thesis.Probability.Distros.RationalLinear
