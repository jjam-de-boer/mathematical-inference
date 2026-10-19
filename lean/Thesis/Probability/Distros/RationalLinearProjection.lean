import Thesis.Probability.Distros.RationalLinearInequalities

namespace Thesis.Probability.Distros.RationalLinear

def Inequality.upperValue (row : Inequality (variables + 1)) (values : Fin variables → SignedRatio) : SignedRatio :=
  if positive : 0 < row.pivot then
    SignedRatio.divideNat (row.residual values) row.pivot.toNat (by omega)
  else SignedRatio.zero

def Inequality.lowerValue (row : Inequality (variables + 1)) (values : Fin variables → SignedRatio) : SignedRatio :=
  if negative : row.pivot < 0 then
    SignedRatio.divideNat (SignedRatio.neg (row.residual values)) (-row.pivot).toNat (by omega)
  else SignedRatio.zero

theorem Inequality.holds_upper_iff (row : Inequality (variables + 1)) (values : Fin variables → SignedRatio)
    (last : SignedRatio) (positive : 0 < row.pivot) :
    row.Holds (extend values last) ↔ SignedRatio.LE last (row.upperValue values) := by
  rw [row.holds_extend_iff]
  simp only [upperValue, dif_pos positive]
  simpa only [Int.toNat_of_nonneg (show 0 ≤ row.pivot by omega)] using
    SignedRatio.scaleInt_divide_le_iff row.pivot.toNat (by omega) last (row.residual values)

theorem Inequality.holds_lower_iff (row : Inequality (variables + 1)) (values : Fin variables → SignedRatio)
    (last : SignedRatio) (negative : row.pivot < 0) :
    row.Holds (extend values last) ↔ SignedRatio.LE (row.lowerValue values) last := by
  rw [row.holds_extend_iff]
  simp only [lowerValue, dif_pos negative]
  refine (SignedRatio.neg_le_neg_iff (SignedRatio.scaleInt row.pivot last) (row.residual values)).symm.trans ?_
  refine (SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm (SignedRatio.neg_scaleInt row.pivot last))).trans ?_
  simpa only [Int.toNat_of_nonneg (show 0 ≤ -row.pivot by omega)] using
    SignedRatio.le_scaleInt_iff_divide_le (-row.pivot).toNat (by omega) (SignedRatio.neg (row.residual values)) last

theorem Inequality.holds_zero_iff (row : Inequality (variables + 1)) (values : Fin variables → SignedRatio)
    (last : SignedRatio) (zero : row.pivot = 0) : row.Holds (extend values last) ↔ row.trim.Holds values := by
  unfold Holds
  rw [dot_extend]
  change SignedRatio.LE (SignedRatio.add (SignedRatio.scaleInt row.pivot last)
    (dot variables row.trim.coefficients values)) row.bound ↔ _
  rw [zero]
  exact SignedRatio.le_congr (SignedRatio.equiv_trans
    (SignedRatio.add_congr (SignedRatio.zero_scaleInt last) (SignedRatio.equiv_refl _)) (SignedRatio.zero_add _)) (SignedRatio.equiv_refl _)

/-- The projected pair is precisely the compatibility condition between
its original lower and upper bounds for the eliminated variable. -/
theorem combine_holds_residual_iff (upper lower : Inequality (variables + 1)) (values : Fin variables → SignedRatio) :
    (combine upper lower).Holds values ↔ SignedRatio.Nonnegative
      (SignedRatio.add (SignedRatio.scaleInt (-lower.pivot) (upper.residual values))
        (SignedRatio.scaleInt upper.pivot (lower.residual values))) := by
  have expanded : SignedRatio.Equiv (dot variables (combine upper lower).coefficients values)
      (SignedRatio.add (SignedRatio.scaleInt (-lower.pivot) (dot variables upper.trim.coefficients values))
        (SignedRatio.scaleInt upper.pivot (dot variables lower.trim.coefficients values))) :=
    SignedRatio.equiv_trans (dot_add_coefficients variables _ _ values)
      (SignedRatio.add_congr (dot_scale_coefficients variables (-lower.pivot) _ values)
        (dot_scale_coefficients variables upper.pivot _ values))
  apply SignedRatio.nonnegative_congr
  exact SignedRatio.equiv_trans (ratio_sub_congr (SignedRatio.equiv_refl _) expanded)
    (SignedRatio.equiv_trans (SignedRatio.sub_add_sub _ _ _ _)
      (SignedRatio.add_congr (SignedRatio.equiv_symm (SignedRatio.scaleInt_sub _ _ _))
        (SignedRatio.equiv_symm (SignedRatio.scaleInt_sub _ _ _))))

theorem combine_holds_iff (upper lower : Inequality (variables + 1)) (values : Fin variables → SignedRatio)
    (positive : 0 < upper.pivot) (negative : lower.pivot < 0) :
    (combine upper lower).Holds values ↔ SignedRatio.LE (lower.lowerValue values) (upper.upperValue values) := by
  rw [combine_holds_residual_iff]
  simp only [Inequality.lowerValue, Inequality.upperValue, dif_pos positive, dif_pos negative]
  rw [SignedRatio.divideNat_le_divideNat_iff]
  rw [Int.toNat_of_nonneg (show 0 ≤ upper.pivot by omega), Int.toNat_of_nonneg (show 0 ≤ -lower.pivot by omega)]
  exact ((SignedRatio.le_congr (SignedRatio.scaleInt_neg upper.pivot (lower.residual values)) (SignedRatio.equiv_refl _)).trans
    (SignedRatio.neg_le_iff_nonnegative_add _ _)).symm

/-- Every assignment satisfying the input system satisfies its projection. -/
theorem project_sound (rows : List (Inequality (variables + 1))) (values : Fin variables → SignedRatio) (last : SignedRatio)
    (satisfies : Satisfies rows (extend values last)) : Satisfies (project rows) values := by
  intro row member
  rcases List.mem_append.mp member with unchanged | paired
  · rcases List.mem_map.mp unchanged with ⟨source, listed, same⟩
    cases same
    exact (source.holds_zero_iff values last (of_decide_eq_true (List.mem_filter.mp listed).2)).mp
      (satisfies source (List.mem_filter.mp listed).1)
  · rcases List.mem_flatMap.mp paired with ⟨upper, upperListed, lowerRows⟩
    rcases List.mem_map.mp lowerRows with ⟨lower, lowerListed, same⟩
    cases same
    have positive := of_decide_eq_true (List.mem_filter.mp upperListed).2
    have negative := of_decide_eq_true (List.mem_filter.mp lowerListed).2
    exact (combine_holds_iff upper lower values positive negative).mpr
      (SignedRatio.le_trans ((lower.holds_lower_iff values last negative).mp (satisfies lower (List.mem_filter.mp lowerListed).1))
        ((upper.holds_upper_iff values last positive).mp (satisfies upper (List.mem_filter.mp upperListed).1)))

def lowerBounds (rows : List (Inequality (variables + 1))) (values : Fin variables → SignedRatio) : List SignedRatio :=
  (rows.filter (fun row => decide (row.pivot < 0))).map (fun row => row.lowerValue values)

def upperBounds (rows : List (Inequality (variables + 1))) (values : Fin variables → SignedRatio) : List SignedRatio :=
  (rows.filter (fun row => decide (0 < row.pivot))).map (fun row => row.upperValue values)

/-- Lifting is a program: finite endpoint selection supplies the eliminated
variable. Inconsistent endpoint pairs contradict an actual projected row. -/
def lift (rows : List (Inequality (variables + 1))) (values : Fin variables → SignedRatio)
    (satisfies : Satisfies (project rows) values) : {last : SignedRatio // Satisfies rows (extend values last)} :=
  match checkRationalInterval (lowerBounds rows values) (upperBounds rows values) with
  | .feasible last lows highs => ⟨last, by
      intro row member
      by_cases positive : 0 < row.pivot
      · exact (row.holds_upper_iff values last positive).mpr
          (highs (row.upperValue values) (List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true positive⟩, rfl⟩))
      · by_cases negative : row.pivot < 0
        · exact (row.holds_lower_iff values last negative).mpr
            (lows (row.lowerValue values) (List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true negative⟩, rfl⟩))
        · have zero : row.pivot = 0 := by omega
          exact (row.holds_zero_iff values last zero).mpr (satisfies row.trim (project_zero_mem rows row member zero))⟩
  | .infeasible below lowerMember above upperMember incompatible => False.elim (by
      rcases List.mem_map.mp lowerMember with ⟨lower, lowerListed, lowerSame⟩
      rcases List.mem_map.mp upperMember with ⟨upper, upperListed, upperSame⟩
      have positive := of_decide_eq_true (List.mem_filter.mp upperListed).2
      have negative := of_decide_eq_true (List.mem_filter.mp lowerListed).2
      apply incompatible
      rw [← lowerSame, ← upperSame]
      exact (combine_holds_iff upper lower values positive negative).mp
        (satisfies (combine upper lower) (project_pair_mem rows upper lower
          (List.mem_filter.mp upperListed).1 (List.mem_filter.mp lowerListed).1 positive negative)))

/-- Exact existential projection, with a constructive lifting program. -/
theorem project_iff (rows : List (Inequality (variables + 1))) (values : Fin variables → SignedRatio) :
    Satisfies (project rows) values ↔ ∃ last : SignedRatio, Satisfies rows (extend values last) := by
  constructor
  · intro satisfies
    exact ⟨(lift rows values satisfies).val, (lift rows values satisfies).property⟩
  · rintro ⟨last, satisfies⟩
    exact project_sound rows values last satisfies

end Thesis.Probability.Distros.RationalLinear
