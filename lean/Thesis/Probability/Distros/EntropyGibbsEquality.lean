import Thesis.Probability.Distros.EntropyGibbs
import Thesis.Probability.LogMeanEquality

namespace Thesis.Probability.Distros

private theorem sum_map_mono (values : List A) (f g : A → Nat)
    (bounded : ∀ value ∈ values, f value ≤ g value) : (values.map f).sum ≤ (values.map g).sum := by
  induction values with
  | nil => exact Nat.le_refl _
  | cons head rest ih =>
      exact Nat.add_le_add (bounded head (List.mem_cons_self ..))
        (ih (fun value member => bounded value (List.mem_cons_of_mem _ member)))

private theorem eq_of_sum_map_eq (values : List A) (f g : A → Nat)
    (bounded : ∀ value ∈ values, f value ≤ g value) (equal : (values.map f).sum = (values.map g).sum) :
    ∀ value ∈ values, f value = g value := by
  induction values with
  | nil => intro value member; exact False.elim (List.not_mem_nil member)
  | cons head rest ih =>
      have tailBound := sum_map_mono rest f g (fun value member => bounded value (List.mem_cons_of_mem _ member))
      change f head + (rest.map f).sum = g head + (rest.map g).sum at equal
      have reversed : g head + (rest.map f).sum ≤ f head + (rest.map f).sum := by
        calc
          _ ≤ g head + (rest.map g).sum := Nat.add_le_add_left tailBound _
          _ = _ := equal.symm
      have headEqual := Nat.le_antisymm (bounded head (List.mem_cons_self ..)) (Nat.le_of_add_le_add_right reversed)
      have tailEqual : (rest.map f).sum = (rest.map g).sum :=
        Nat.add_left_cancel (by simpa only [headEqual] using equal)
      intro value member
      rcases List.mem_cons.mp member with here | later
      · subst value; exact headEqual
      · exact ih (fun value member => bounded value (List.mem_cons_of_mem _ member)) tailEqual value later

/-- Zero KL forces equality of all events. This includes observed zero masses:
normalization prevents unmatched reference mass from hiding in those cells. -/
theorem Distro.sameLaw_of_relativeEntropy_zero [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid)
    (vanished : ExactLog.Equiv (μ.relativeEntropy reference grid support referenceSupport positive) ExactLog.zero) :
    μ.SameLaw reference := by
  have represented := μ.relativeEntropy_logMean reference grid support referenceSupport positive
  have logZero := ExactLog.equiv_trans (ExactLog.equiv_symm represented) vanished
  have ratios := RationalAMGM.eq_one_of_logMean_zero (μ.relativeRatioItems reference grid positive)
    μ.record.den μ.record.den_pos
    (by rw [μ.relativeRatioItems_weight reference grid support positive]; exact μ.record.den_pos)
    (μ.relativeRatioItems_inverse_mean reference grid support referenceSupport positive) logZero
  have positiveAgreement : ∀ value ∈ grid.cells, 0 < (μ.pmf value).num → QProb.Equiv (μ.pmf value) (reference.pmf value) := by
    intro value listed massPositive
    let cell : { value // value ∈ grid.cells } := ⟨value, listed⟩
    have belongs : (relativeRatio (μ.pmf value) (reference.pmf value) (positive value listed), (μ.pmf value).num) ∈
        μ.relativeRatioItems reference grid positive :=
      List.mem_map.mpr ⟨cell, List.mem_attach .., rfl⟩
    exact (relativeRatio_equiv_one_iff _ _ _ massPositive).mp (ratios _ belongs massPositive)
  let f := fun value => (μ.pmf value).num * reference.record.den
  let g := fun value => (reference.pmf value).num * μ.record.den
  have pointwiseBound : ∀ value ∈ grid.cells, f value ≤ g value := by
    intro value listed
    by_cases massPositive : 0 < (μ.pmf value).num
    · exact Nat.le_of_eq (positiveAgreement value listed massPositive)
    · have zero := Nat.eq_zero_of_not_pos massPositive
      change (μ.pmf value).num * reference.record.den ≤ _
      rw [zero, Nat.zero_mul]
      exact Nat.zero_le _
  have firstSum : (grid.cells.map f).sum = μ.record.den * reference.record.den := by
    have scaled := FiniteAMGM.sum_scale (grid.cells.map (fun value => (μ.pmf value).num)) reference.record.den
    rw [μ.pmf_grid_numerator_sum grid support] at scaled
    simpa only [f, List.map_map, Function.comp_def, Nat.mul_comm] using scaled
  have secondSum : (grid.cells.map g).sum = reference.record.den * μ.record.den := by
    have scaled := FiniteAMGM.sum_scale (grid.cells.map (fun value => (reference.pmf value).num)) μ.record.den
    rw [reference.pmf_grid_numerator_sum grid referenceSupport] at scaled
    simpa only [g, List.map_map, Function.comp_def, Nat.mul_comm] using scaled
  have sumEqual : (grid.cells.map f).sum = (grid.cells.map g).sum := by
    rw [firstSum, secondSum, Nat.mul_comm]
  have agreement := eq_of_sum_map_eq grid.cells f g pointwiseBound sumEqual
  apply μ.sameLaw_of_pmf reference
  intro value
  by_cases listed : value ∈ grid.cells
  · exact agreement value listed
  · have firstZero := μ.pmf_zero_of_almostSure_ne value
      (fun atom member weight same => listed (same ▸ support atom member weight))
    have secondZero := reference.pmf_zero_of_almostSure_ne value
      (fun atom member weight same => listed (same ▸ referenceSupport atom member weight))
    exact QProb.equiv_trans firstZero (QProb.equiv_symm secondZero)

/-- The exact equality condition in the finite Gibbs inequality. -/
theorem Distro.relativeEntropy_equiv_zero_iff [DecidableEq A] (μ reference : Distro A) (grid : EntropyGrid A)
    (support : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (referenceSupport : reference.AlmostSurely (fun value => value ∈ grid.cells))
    (positive : reference.GridPositive grid) :
    ExactLog.Equiv (μ.relativeEntropy reference grid support referenceSupport positive) ExactLog.zero ↔ μ.SameLaw reference := by
  constructor
  · exact μ.sameLaw_of_relativeEntropy_zero reference grid support referenceSupport positive
  · intro same
    exact ExactLog.equiv_trans
      (Distro.relativeEntropy_sameLaw same (Distro.SameLaw.refl reference) grid support referenceSupport
        referenceSupport referenceSupport positive positive)
      (reference.relativeEntropy_self grid referenceSupport positive)

end Thesis.Probability.Distros
