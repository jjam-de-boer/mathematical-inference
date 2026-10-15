import Thesis.CausalTransport.ObservationalFormulaDiagnostics
import Thesis.Examples.BackdoorAdjustmentSearch

namespace Thesis
namespace Causality
namespace Examples
namespace ObservationalFormulaDiagnostics

open Probability AlternativeFormulaSelection

/-!
# Three distinct observable plan outcomes

A constant zero expression is perfectly well-defined.  The literal ratio
`0 / 0` is not.  A separate probability-one action guard can reject even the
well-defined constant expression.  The catalogue retains this distinction
and still falls back to the ready plan, with the same result as the existing
selector.  No claim about identification of a causal target is inferred from
these arbitrary syntax-only test plans.
-/

abbrev record := BackdoorAdjustmentSearch.pointRecord
abbrev requested := BackdoorAdjustmentSearch.oppositeReference

def readyPlan : ObservationalFormulaPlan signature := ⟨.zero, .always⟩
def undefinedPlan : ObservationalFormulaPlan signature := ⟨.divide .zero .zero, .always⟩
def rejectedPlan : ObservationalFormulaPlan signature := ⟨.zero, .actionOne (NodeSet.singleton x)⟩

theorem ready_value : readyPlan.diagnose record requested = .ready QProb.zero := rfl
theorem undefined_denominator : undefinedPlan.diagnose record requested = .expressionUnavailable := rfl

theorem guard_rejection : rejectedPlan.diagnose record requested = .guardRejected := by
  apply (ObservationalFormulaPlan.diagnose_guardRejected_iff _ _ _).mpr
  decide +kernel

theorem catalogue_keeps_reasons :
    ObservationalFormulaPlan.diagnoseCatalogue [rejectedPlan, undefinedPlan, readyPlan] record requested =
      [.guardRejected, .expressionUnavailable, .ready QProb.zero] := by
  simp only [ObservationalFormulaPlan.diagnoseCatalogue, List.map_cons, List.map_nil,
    guard_rejection, undefined_denominator, ready_value]

theorem selector_still_falls_back :
    ObservationalFormulaPlan.select record requested [rejectedPlan, undefinedPlan, readyPlan] = some readyPlan := by
  have rejected : rejectedPlan.available record requested = false := by
    rw [← ObservationalFormulaPlan.diagnose_isReady_eq_available, guard_rejection]
    rfl
  have undefined : undefinedPlan.available record requested = false := by
    rw [← ObservationalFormulaPlan.diagnose_isReady_eq_available, undefined_denominator]
    rfl
  have ready : readyPlan.available record requested = true := by
    rw [← ObservationalFormulaPlan.diagnose_isReady_eq_available, ready_value]
    rfl
  simp only [ObservationalFormulaPlan.select, rejected, undefined, ready, Bool.false_eq_true, if_false, if_true]

end ObservationalFormulaDiagnostics
end Examples
end Causality
end Thesis
