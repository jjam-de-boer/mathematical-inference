import Thesis.CausalTransport.ObservationalFormulaSupport
import Thesis.Examples.BinaryInstrumental.Identification

namespace Thesis.Causality.Examples.SupportOnlyIdentificationObstruction

open Probability BinaryInstrumental
open BinaryInstrumentalCompatibility (assignment)

/-!
# Fixed-law identification can depend on masses inside positive support

The two compatible binary-IV laws below have all eight observed cells
positive. One saturates an instrumental inequality: its control risk is
identified at `2/5`. The uniform law has the very same singleton support,
but its control risk is not identified. Therefore no function of observed
support alone can classify fixed-law identification, even within this graph
and even on strictly positive observed laws.

This limits support-only classification of numerical special cases. It does
not refute ID/IDC graph-level completeness, the current support abstraction
for formula definedness, bounded proof search, or arbitrary-graph decision
procedures that inspect actual rational masses. In particular it does not
settle universal coverage relative to the current serialized proof grammar.
-/

abbrev projection := BinaryInstrumentalCompatibility.projection

def saturatedLaw : FiniteProbRecord signature.Assignment :=
  ⟨[(assignment false false false, 6), (assignment false false true, 1),
    (assignment false true false, 1), (assignment false true true, 2),
    (assignment true false false, 1), (assignment true false true, 4),
    (assignment true true false, 2), (assignment true true true, 3)], 20, by decide, rfl⟩

theorem saturated_compatible : (computedBounds saturatedLaw).compatible = true := by decide +kernel

theorem saturated_native_exists :
    ∃ native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native saturatedLaw :=
  (computedBounds_compatible_iff projection BinaryInstrumentalCompatibility.projected_iv_graph saturatedLaw).mp saturated_compatible

theorem saturated_control_bounds :
    QProb.Equiv ((computedBounds saturatedLaw).lowerRisk false) ⟨2, 5, by decide⟩ ∧
      QProb.Equiv ((computedBounds saturatedLaw).upperRisk false) ⟨2, 5, by decide⟩ := by decide +kernel

theorem saturated_control_identified : RiskIdentifiedAt projection saturatedLaw false :=
  (riskIdentifiedAt_iff_bounds_equiv projection BinaryInstrumentalCompatibility.projected_iv_graph
    saturatedLaw saturated_compatible false).mpr
    (QProb.equiv_trans saturated_control_bounds.1 (QProb.equiv_symm saturated_control_bounds.2))

/-- The identified number is the actual interventional risk in every fitted
original IV model, with no hidden-cardinality or response-denominator bound. -/
theorem saturated_native_control_value (native : FiniteHiddenDAGSCM signature projection)
    (fitted : HasObservedLaw native saturatedLaw) :
    QProb.Equiv (native.interventionalValue (intervention false) (fun sample => sample y)) ⟨2, 5, by decide⟩ := by
  have bounded := computedBounds_native_risks native BinaryInstrumentalCompatibility.projected_iv_graph saturatedLaw fitted false
  exact QProb.equiv_of_le_of_le
    (QProb.le_congr (QProb.equiv_refl _) saturated_control_bounds.2 bounded.2)
    (QProb.le_congr saturated_control_bounds.1 (QProb.equiv_refl _) bounded.1)

private theorem assignment_expansion (sample : signature.Assignment) :
    assignment (sample z) (sample x) (sample y) = sample := by
  funext node
  rcases node_cases node with rfl | rfl | rfl <;> rfl

theorem saturated_full_support (sample : signature.Assignment) : saturatedLaw.support sample = true := by
  have all : ∀ instrument treatment outcome : Bool,
      saturatedLaw.support (assignment instrument treatment outcome) = true := by decide +kernel
  simpa only [assignment_expansion] using all (sample z) (sample x) (sample y)

theorem uniform_full_support (sample : signature.Assignment) :
    BinaryInstrumentalCompatibility.uniformLaw.support sample = true := by
  have all : ∀ instrument treatment outcome : Bool,
      BinaryInstrumentalCompatibility.uniformLaw.support (assignment instrument treatment outcome) = true := by decide +kernel
  simpa only [assignment_expansion] using all (sample z) (sample x) (sample y)

theorem same_support : saturatedLaw.support = BinaryInstrumentalCompatibility.uniformLaw.support := by
  funext sample
  rw [saturated_full_support, uniform_full_support]

/-- The existing exact abstraction remains correct: every current term has
the same defined/zero/positive status on these two laws. The failure concerns
classification of fixed-law identification, not formula-status evaluation. -/
theorem same_formula_status (term : ProbabilityTerm signature) (reference : signature.Assignment) :
    ProbabilityResult.status (term.observationalDenote saturatedLaw reference) =
      ProbabilityResult.status (term.observationalDenote BinaryInstrumentalCompatibility.uniformLaw reference) :=
  term.status_eq_of_support_eq same_support reference

/-- A support-only Boolean answer cannot characterize identification on
both compatible positive laws. No computability or undecidability assumption
is used: equality of inputs forces equality of the two Boolean outputs. -/
theorem no_support_only_classifier
    (classify : (signature.Assignment → Bool) → Bool)
    (correct : ∀ law : FiniteProbRecord signature.Assignment,
      (computedBounds law).compatible = true →
      (classify law.support = true ↔ RiskIdentifiedAt projection law false)) : False := by
  have yes := (correct saturatedLaw saturated_compatible).mpr saturated_control_identified
  rw [same_support] at yes
  exact BinaryInstrumentalIdentification.uniform_risk_not_identified false
    ((correct BinaryInstrumentalCompatibility.uniformLaw (by decide +kernel)).mp yes)

end Thesis.Causality.Examples.SupportOnlyIdentificationObstruction
