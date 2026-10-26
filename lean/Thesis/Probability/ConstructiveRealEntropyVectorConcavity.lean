import Thesis.Probability.ConstructiveRealEntropyStrongConcavityClosed

namespace Thesis.Probability.ConstructiveReal

/-- Finite sums respect pointwise closed order. -/
theorem listSum_map_mono (values : List A) (first second : A → ConstructiveReal)
    (compared : ∀ value ∈ values, LE (first value) (second value)) :
    LE (listSum (values.map first)) (listSum (values.map second)) := by
  induction values with
  | nil => exact le_refl zero
  | cons value rest ih =>
      exact add_le_add (compared value (List.mem_cons_self ..))
        (ih (fun other member => compared other (List.mem_cons_of_mem _ member)))

theorem listSum_map_add (values : List A) (first second : A → ConstructiveReal) :
    Equiv (listSum (values.map (fun value => add (first value) (second value))))
      (add (listSum (values.map first)) (listSum (values.map second))) := by
  induction values with
  | nil => exact equiv_symm (zero_add zero)
  | cons value rest ih => exact equiv_trans (add_congr (equiv_refl _) ih) (add_four _ _ _ _)

/-- An individual nonnegative summand is bounded by the full finite sum.
Membership is in the declared list, so repeated values do not require a
choice of occurrence or a comparison of analytic values. -/
theorem le_listSum_of_mem (values : List ConstructiveReal) (nonnegative : ∀ value ∈ values, LE zero value)
    (value : ConstructiveReal) (member : value ∈ values) : LE value (listSum values) := by
  induction values with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first rest ih =>
      have restPositive := listSum_nonnegative rest (fun other listed => nonnegative other (List.mem_cons_of_mem _ listed))
      rcases List.mem_cons.mp member with rfl | later
      · exact (le_congr (add_zero value) (equiv_refl _)).mp (add_le_add (le_refl value) restPositive)
      · exact (le_congr (zero_add value) (equiv_refl _)).mp
          (add_le_add (nonnegative first (List.mem_cons_self ..))
            (ih (fun other listed => nonnegative other (List.mem_cons_of_mem _ listed)) later))

/-- The scalar quantitative entropy gap adds over every finite vector,
including zero coordinates. Normalization is unnecessary for this analytic
inequality; feasible-law applications separately supply their original rows. -/
theorem realEntropySum_strong_midpoint (values : List A) (first second : A → UnitIntervalValue) :
    LE (add (mul (add (realEntropySum (values.map first)) (realEntropySum (values.map second)))
        (ofSignedRatio ⟨1, 2, by decide⟩))
      (mul (listSum (values.map (fun value => mul (sub (first value).value (second value).value)
        (sub (first value).value (second value).value)))) (ofSignedRatio ⟨1, 8, by decide⟩)))
      (realEntropySum (values.map (fun value => (first value).midpoint (second value)))) := by
  simp only [realEntropySum, List.map_map]
  let half := ofSignedRatio (⟨1, 2, by decide⟩ : SignedRatio)
  let eighth := ofSignedRatio (⟨1, 8, by decide⟩ : SignedRatio)
  let average := fun value => mul (add (first value).entropy (second value).entropy) half
  let gap := fun value => mul (sub (first value).value (second value).value) (sub (first value).value (second value).value)
  have terms := listSum_map_mono values (fun value => add (average value) (mul (gap value) eighth))
    (fun value => ((first value).midpoint (second value)).entropy)
    (fun value _ => (first value).entropy_strong_midpoint (second value))
  have collectAverage : Equiv (listSum (values.map average))
      (mul (add (realEntropySum (values.map first)) (realEntropySum (values.map second))) half) := by
    simp only [realEntropySum, List.map_map]
    have distributed := listSum_mul (values.map (fun value => add (first value).entropy (second value).entropy)) half
    simp only [List.map_map] at distributed
    exact equiv_trans (equiv_symm distributed)
      (mul_congr (listSum_map_add values _ _) (equiv_refl _))
  have collectGap : Equiv (listSum (values.map (fun value => mul (gap value) eighth)))
      (mul (listSum (values.map gap)) eighth) :=
    equiv_symm (by simpa only [List.map_map] using listSum_mul (values.map gap) eighth)
  have collected := equiv_trans
    (listSum_map_add values average (fun value => mul (gap value) eighth))
    (add_congr collectAverage collectGap)
  simpa only [realEntropySum, List.map_map] using (le_congr collected (equiv_refl _)).mp terms

end Thesis.Probability.ConstructiveReal
