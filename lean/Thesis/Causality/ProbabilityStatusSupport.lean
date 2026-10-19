import Thesis.Causality.ProbabilityStatus

namespace Thesis.Causality.ProbabilityResult

open Probability

/-!
# Constructive support data from exact partial-result status

Equal support status does not identify two probability values. It does allow
support evidence to be rebuilt from each result's *own* actual value. These
small constructors inspect `Option QProb` directly; they never select a value
from a propositional existential or copy an inequivalent old numerator.
Positive evidence is similarly rebuilt only after a proved positive status.
-/

theorem valueStatus_eq_of_num_pos_iff (left right : QProb)
    (same : 0 < left.num ↔ 0 < right.num) : valueStatus left = valueStatus right := by
  by_cases positive : 0 < left.num
  · simp only [valueStatus, if_neg (Nat.ne_of_gt positive), if_neg (Nat.ne_of_gt (same.mp positive))]
  · have leftZero := Nat.eq_zero_of_not_pos positive
    have rightZero := Nat.eq_zero_of_not_pos (fun rightPositive => positive (same.mpr rightPositive))
    simp only [valueStatus, if_pos leftZero, if_pos rightZero]

theorem supported_isSome {result : Result} (supported : Supported result) : result.isSome = true := by
  rcases supported with ⟨value, equivalent⟩
  cases equivalent
  rfl

def supportedOfIsSome (result : Result) (checked : result.isSome = true) : Supported result := by
  cases result with
  | none => cases checked
  | some value => exact ⟨value, .value (QProb.equiv_refl value)⟩

theorem positiveSupported_status {result : Result} (positive : PositiveSupportedValue result) : status result = .positive := by
  cases result with
  | none => cases positive.equivalent
  | some actual =>
      have same : QProb.Equiv actual positive.value := by
        cases positive.equivalent with
        | value same => exact same
      have actualPositive := (QProb.equiv_num_pos_iff same).mpr positive.positive
      exact if_neg (Nat.ne_of_gt actualPositive)

def positiveSupportedOfStatus (result : Result) (checked : status result = .positive) : PositiveSupportedValue result := by
  cases result with
  | none => cases checked
  | some value =>
      refine ⟨value, .value (QProb.equiv_refl value), ?_⟩
      by_cases zero : value.num = 0
      · have impossible : Status.zero = Status.positive := by
          simpa only [status, valueStatus, if_pos zero] using checked
        cases impossible
      · exact Nat.pos_of_ne_zero zero

end Thesis.Causality.ProbabilityResult
