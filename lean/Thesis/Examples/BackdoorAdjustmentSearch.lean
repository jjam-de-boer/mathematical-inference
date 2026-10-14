import Thesis.Examples.AlternativeFormulaSelection
import Thesis.CausalTransport.BackdoorAdjustmentSearch

namespace Thesis
namespace Causality
namespace Examples
namespace BackdoorAdjustmentSearch

open Probability
open AlternativeFormulaSelection

/-!
# Generated adjustment search: genuine fallback and support boundaries

The existing four-variable fixture has two valid adjustment sets, `C` and
`C,Z`.  ID's chosen expression and adjustment using both covariates are
undefined at the requested action; adjustment using only `C` is supported
and returns the actual effect one half.  Here the application supplies no
covariate catalogue or graphical witness: the new graph checker and subset
enumerator construct the list and its certificates automatically.

Further evaluator regressions retain the boundaries at zeros.  A covariate
cell with zero weight may skip its null conditional, whereas an entirely
unobserved requested action makes every generated formula unavailable.
These last records test literal support, not additional causal assumptions.
-/

/-- Explicit finite coordinate equality for this fixture.  Keeping the
instance as a closed declaration also lets kernel-only decision reduction
check list equality without an elaborator-local instance variable. -/
private instance nodeSetDecidableEq : DecidableEq (NodeSet signature) :=
  FiniteProduct.assignmentDecidableEq signature.count (fun _ => Bool) (fun _ => inferInstance)

/-- The permitted region consists of the two nonquery covariates.  The
finite equality instance explicitly checks coordinates; no function-choice
instance or classical node-set equality is used. -/
theorem generated_covariates_exact :
    Causality.BackdoorAdjustmentSearch.covariates projection.observedGraph query = [small, large] := by
  decide +kernel

/-- The runtime program discovers the supported smaller adjustment.  The
list order and graphical admissibility come from generation, not a supplied
handwritten `[small, large]` input to the implementation. -/
theorem automatically_selects_small :
    Causality.BackdoorAdjustmentSearch.select projection.observedGraph query model.observationalDist reference =
      some (Causality.BackdoorAdjustmentSearch.plan query small) := by
  have accepted : (Causality.BackdoorAdjustmentSearch.plan query small).available model.observationalDist reference = true :=
    small_available
  simp only [Causality.BackdoorAdjustmentSearch.select, Causality.BackdoorAdjustmentSearch.plans, generated_covariates_exact, List.map_cons,
    List.map_nil, ObservationalFormulaPlan.select, accepted, if_true]

/-- Putting the existing certified ID plan first still falls back here,
because its actual printed evaluator reports no value. -/
theorem id_then_automatic_fallback :
    Causality.BackdoorAdjustmentSearch.selectWithPreferred projection.observedGraph query idCandidate.plan
      model.observationalDist reference = some (Causality.BackdoorAdjustmentSearch.plan query small) := by
  have rejected : idCandidate.plan.available model.observationalDist reference = false := id_unavailable
  simpa only [Causality.BackdoorAdjustmentSearch.selectWithPreferred, ObservationalFormulaPlan.select,
    rejected, Bool.false_eq_true, if_false] using automatically_selects_small

/-- Soundness of the automatically selected literal plan is the universal
native theorem, not equality of two numbers computed for this fixture. -/
noncomputable def automatic_native_sound :
    model.TermEquivalentAt query.sourceTerm (Causality.BackdoorAdjustmentSearch.plan query small).formula reference :=
  Causality.BackdoorAdjustmentSearch.selected_soundAt model query reference _ automatically_selects_small

noncomputable def id_fallback_native_sound :
    model.TermEquivalentAt query.sourceTerm (Causality.BackdoorAdjustmentSearch.plan query small).formula reference :=
  Causality.BackdoorAdjustmentSearch.selectedWithPreferred_soundAt model query idCandidate reference _ id_then_automatic_fallback

/-- Reuse the separately checked nonzero value to ensure the generated
search has genuinely preserved the original intervention probability. -/
noncomputable def automatic_effect_half :
    ProbabilityResult.Equivalent (model.termDenote query.sourceTerm reference) (some half) :=
  ProbabilityResult.trans automatic_native_sound (by
    rw [← ProbabilityTerm.observationalDenote_eq_native model
      (Causality.BackdoorAdjustmentSearch.plan query small).formula (BackdoorAdjustmentWitness.formula_actionFree query small) reference]
    exact selected_value_half)

/-- A literal observed record with zeros.  A skipped covariate cell must
not force the evaluator to manufacture its undefined outcome conditional. -/
def pointRecord : FiniteProbRecord signature.Assignment where
  atoms := [(fun _ => true, 1)]
  den := 1
  den_pos := by decide
  total_mass := rfl

theorem zero_weight_cell_is_skipped :
    (Causality.BackdoorAdjustmentSearch.plan query small).available pointRecord reference = true := by
  decide +kernel

theorem generated_search_accepts_zero_containing_record :
    Causality.BackdoorAdjustmentSearch.select projection.observedGraph query pointRecord reference =
      some (Causality.BackdoorAdjustmentSearch.plan query small) := by
  simp only [Causality.BackdoorAdjustmentSearch.select, Causality.BackdoorAdjustmentSearch.plans, generated_covariates_exact, List.map_cons,
    List.map_nil, ObservationalFormulaPlan.select, zero_weight_cell_is_skipped, if_true]

/-- Request the opposite action while keeping the observed law fixed.
At its positive covariate cell, the actually used outcome conditioner is
null.  Generation cannot repair that failure by totalizing division. -/
def oppositeReference : signature.Assignment := fun node =>
  if node.val = x.val then false else true

theorem unsupported_action_returns_none :
    Causality.BackdoorAdjustmentSearch.select projection.observedGraph query pointRecord oppositeReference = none := by
  rw [Causality.BackdoorAdjustmentSearch.select, Causality.BackdoorAdjustmentSearch.plans, generated_covariates_exact]
  decide +kernel

/-- Empty action is a genuine boundary, not a missing enumeration case.
Its empty adjustment is retained by both executable separation checks. -/
def emptyActionQuery : JointKernelQuery signature :=
  ⟨query.outcome, NodeSet.empty, NodeSet.disjoint_empty_left _⟩

theorem empty_adjustment_is_generated :
    NodeSet.empty ∈ Causality.BackdoorAdjustmentSearch.covariates projection.observedGraph emptyActionQuery := by
  apply (Causality.BackdoorAdjustmentSearch.covariates_member_iff _ _ _).mpr
  decide +kernel

end BackdoorAdjustmentSearch
end Examples
end Causality
end Thesis
