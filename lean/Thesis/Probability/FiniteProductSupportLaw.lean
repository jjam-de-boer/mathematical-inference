import Thesis.Probability.FiniteRecordSupport
import Thesis.Probability.FiniteProductExtensional

namespace Thesis.Probability.FiniteProduct

/-!
# Independent products depend on factor supports at positivity level

Changing positive source weights generally changes event probabilities. It
does not change which joint assignments, or which arbitrary mixed events,
have positive probability, provided each coordinate retains exactly its old
positive support. This theorem is about actual independent product records;
it is not an assumed support or coupling interface.

The proof uses the existing rectangular law for singleton assignments. A
product of nonnegative fractions is positive exactly when every coordinate
numerator is positive. The finite-record event-support theorem then handles
arbitrary events. Empty source families and zero source cells are retained.
No positive assignment is selected to construct a computational object.
-/

theorem qProduct_num_pos_iff (count : Nat) (values : Fin count → QProb) :
    0 < (qProduct count values).num ↔ ∀ source, 0 < (values source).num := by
  induction count with
  | zero =>
      constructor
      · intro _ source; exact Fin.elim0 source
      · intro _; exact Nat.zero_lt_one
  | succ count ih =>
      change 0 < (values (Fin.last count)).num * (qProduct count (fun source => values source.castSucc)).num ↔ _
      rw [Nat.mul_pos_iff, ih]
      constructor
      · rintro ⟨last, initial⟩ source
        exact Fin.lastCases last initial source
      · intro positive
        exact ⟨positive (Fin.last count), fun source => positive source.castSucc⟩

variable {count : Nat} {cards : Fin count → Nat}

theorem record_singleton_positive_iff
    (factors : (source : Fin count) → FiniteProbRecord (Fin (cards source)))
    (reference : (source : Fin count) → Fin (cards source)) :
    letI := assignmentDecidableEq count (fun source => Fin (cards source)) (fun _ => inferInstance)
    (record count _ factors).EventPositive (FiniteProbRecord.singletonEvent reference) ↔
      ∀ source, (factors source).EventPositive (FiniteProbRecord.singletonEvent (reference source)) := by
  letI := assignmentDecidableEq count (fun source => Fin (cards source)) (fun _ => inferInstance)
  have compared := record_rectangular_probVal count (fun source => Fin (cards source)) factors
    (fun source => FiniteProbRecord.singletonEvent (reference source))
  rw [rectangularEvent_assignment_singleton (fun _ => inferInstance) reference] at compared
  exact (QProb.equiv_num_pos_iff compared).trans (qProduct_num_pos_iff count _)

/-- Coordinate support equality implies equality of the *whole* independent
product support, including events that couple several coordinates. -/
theorem record_support_eq_of_factor_support_eq
    (left right : (source : Fin count) → FiniteProbRecord (Fin (cards source)))
    (same : ∀ source, (left source).support = (right source).support) :
    letI := assignmentDecidableEq count (fun source => Fin (cards source)) (fun _ => inferInstance)
    (record count _ left).support = (record count _ right).support := by
  letI := assignmentDecidableEq count (fun source => Fin (cards source)) (fun _ => inferInstance)
  funext reference
  apply Bool.eq_iff_iff.mpr
  simp only [FiniteProbRecord.support, decide_eq_true_eq]
  rw [record_singleton_positive_iff, record_singleton_positive_iff]
  constructor
  · intro positive source
    have checked : (left source).support (reference source) = true := decide_eq_true (positive source)
    rw [same source] at checked
    exact of_decide_eq_true checked
  · intro positive source
    have checked : (right source).support (reference source) = true := decide_eq_true (positive source)
    rw [← same source] at checked
    exact of_decide_eq_true checked

theorem record_eventPositive_iff_of_factor_support_eq
    (left right : (source : Fin count) → FiniteProbRecord (Fin (cards source)))
    (same : ∀ source, (left source).support = (right source).support)
    (event : Event ((source : Fin count) → Fin (cards source))) :
    (record count _ left).EventPositive event ↔ (record count _ right).EventPositive event := by
  letI := assignmentDecidableEq count (fun source => Fin (cards source)) (fun _ => inferInstance)
  exact FiniteProbRecord.eventPositive_iff_of_support_eq (record_support_eq_of_factor_support_eq left right same) event

end Thesis.Probability.FiniteProduct
