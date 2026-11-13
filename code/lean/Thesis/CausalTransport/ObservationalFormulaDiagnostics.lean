import Thesis.CausalTransport.ObservationalFormulaSelection

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Observable applicability diagnostics for certified formula plans

An unavailable plan is not the same as structural ID failure.  These data-only
diagnostics distinguish a rejected observable guard from an unavailable
partial expression, and retain the actual value of a ready expression.  For
action-free certified plans, expression unavailability concerns the printed
formula's own support; arbitrary uncertified plans may also contain rejected
actionful leaves.  No rejection is called general nonidentifiability.

The bridge theorems relate these messages to the existing executable selector
exactly.  In particular, an exhausted catalogue means every supplied plan is
unavailable, not that every mathematically possible formula is unavailable.
The diagnosis neither evaluates nor promises the original conditional causal
target's support.  Conditional application still needs that separate premise;
an observational-only diagnostic must not silently manufacture it.
-/

/-- No causal or structural conclusion is encoded by these runtime states.
`ready` reports observational evaluation, not a replacement for certification. -/
inductive FormulaPlanDiagnostic where
  | guardRejected
  | expressionUnavailable
  | ready (value : QProb)

namespace FormulaPlanDiagnostic

def isReady : FormulaPlanDiagnostic → Bool
  | .ready _ => true
  | .guardRejected => false
  | .expressionUnavailable => false

end FormulaPlanDiagnostic

namespace ObservationalFormulaPlan

/-- Check the observable guard first, then the actual partial expression.
No unsupported denominator is totalized and no hidden model is inspected. -/
def diagnose (plan : ObservationalFormulaPlan S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) : FormulaPlanDiagnostic :=
  if plan.guard.check record reference then
    match plan.formula.observationalDenote record reference with
    | some value => .ready value
    | none => .expressionUnavailable
  else .guardRejected

theorem diagnose_ready_iff (plan : ObservationalFormulaPlan S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) (value : QProb) :
    plan.diagnose record reference = .ready value ↔
      plan.guard.check record reference = true ∧ plan.formula.observationalDenote record reference = some value := by
  cases guardValue : plan.guard.check record reference <;>
    cases expressionValue : plan.formula.observationalDenote record reference <;>
    simp [diagnose, guardValue, expressionValue]

/-- The new diagnosis accepts exactly the plans accepted before this API
was introduced.  It changes reporting, not the selector's support domain. -/
theorem diagnose_isReady_eq_available (plan : ObservationalFormulaPlan S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) :
    (plan.diagnose record reference).isReady = plan.available record reference := by
  cases guardValue : plan.guard.check record reference <;>
    cases expressionValue : plan.formula.observationalDenote record reference <;>
    simp [diagnose, available, guardValue, expressionValue, FormulaPlanDiagnostic.isReady]

theorem diagnose_guardRejected_iff (plan : ObservationalFormulaPlan S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) :
    plan.diagnose record reference = .guardRejected ↔ plan.guard.check record reference = false := by
  cases guardValue : plan.guard.check record reference <;>
    cases expressionValue : plan.formula.observationalDenote record reference <;>
    simp [diagnose, guardValue, expressionValue]

theorem diagnose_expressionUnavailable_iff (plan : ObservationalFormulaPlan S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) :
    plan.diagnose record reference = .expressionUnavailable ↔
      plan.guard.check record reference = true ∧ plan.formula.observationalDenote record reference = none := by
  cases guardValue : plan.guard.check record reference <;>
    cases expressionValue : plan.formula.observationalDenote record reference <;>
    simp [diagnose, guardValue, expressionValue]

/-- Preserve catalogue order and diagnose every candidate, including those
after the first ready plan, when an application requests an explanation. -/
def diagnoseCatalogue (plans : List (ObservationalFormulaPlan S))
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) : List FormulaPlanDiagnostic :=
  plans.map (fun plan => plan.diagnose record reference)

theorem select_none_iff_no_ready_diagnosis (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (plans : List (ObservationalFormulaPlan S)) :
    select record reference plans = none ↔
      forall plan, plan ∈ plans → (plan.diagnose record reference).isReady = false := by
  constructor
  · intro absent plan listed
    rw [diagnose_isReady_eq_available]
    exact (select_none_iff record reference plans).mp absent plan listed
  · intro unavailable
    apply (select_none_iff record reference plans).mpr
    intro plan listed
    rw [← diagnose_isReady_eq_available]
    exact unavailable plan listed

end ObservationalFormulaPlan
end Causality
end Thesis
