import Thesis.Causality.Structural.Core

namespace Thesis
namespace Causality
namespace ModeTheory

open Probability
open CausalEpistemicRecord
open CausalEditPath

/-!
Mode theory of causal-epistemic states: a 1-category.

Objects are `CausalMode` (a named record).  Generating morphisms are the
constructors of `CausalEditOperation`; their action is `result` (below,
`act`).  Inverse laws are equalities of those morphisms
(`setVariable_unsetVariable` in `Modalities`; announce-then-commit in
`Structural.Commit`).  Composite morphisms are `CausalEditPath`.  Identity
is `nil`, composition is `append`; the unit and associativity laws are
already in `Structural.Core`.  `run` reads the target record; a singleton
path runs as `act`.
-/

/-! ## Current state -/

/--
The three fields of a record that current-state inferences read: model,
belief, and intervention.
-/
structure CurrentState (S : ObservedSignature) where
  model : ExactModel S
  belief : FiniteProbRecord model.latent.Assignment
  intervention : HardIntervention S

namespace CurrentState

/-- Unpack a record to its model, belief, and intervention. -/
def ofRecord {S : ObservedSignature} (R : CausalEpistemicRecord S) :
    CurrentState S where
  model := R.model
  belief := R.belief
  intervention := R.intervention

/-- Pack the three fields as a record with an empty modal stack. -/
def toRecord {S : ObservedSignature} (σ : CurrentState S) :
    CausalEpistemicRecord S where
  model := σ.model
  belief := σ.belief
  intervention := σ.intervention
  stack := .nil

@[simp] theorem ofRecord_toRecord {S : ObservedSignature}
    (σ : CurrentState S) :
    ofRecord σ.toRecord = σ :=
  rfl

@[simp] theorem toRecord_ofRecord {S : ObservedSignature}
    (R : CausalEpistemicRecord S) :
    (ofRecord R).toRecord = { R with stack := .nil } :=
  rfl

/-- Posterior from the three fields agrees with the record. -/
theorem observedValue_toRecord {S : ObservedSignature}
    (R : CausalEpistemicRecord S) (event : S.Assignment -> Bool) :
    R.observedValue event = (ofRecord R).toRecord.observedValue event :=
  rfl

/-- One-shot set updates only the intervention field. -/
theorem ofRecord_setVariable {S : ObservedSignature}
    (R : CausalEpistemicRecord S) (target : Fin S.count)
    (value : S.Value target) :
    ofRecord (R.setVariable target value) =
      { ofRecord R with
        intervention := R.intervention.set target value } :=
  rfl

/-- One-shot intervene updates only the intervention field. -/
theorem ofRecord_interveneNodes {S : ObservedSignature}
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment) :
    ofRecord (R.interveneNodes nodes reference) =
      { ofRecord R with
        intervention := R.intervention.setNodes nodes reference } :=
  rfl

/-- One-shot observe updates only the belief field. -/
theorem ofRecord_observeNodes {S : ObservedSignature}
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment)
    (hEvidence : R.belief.EventPositive
      (R.nodeObservationEvidence nodes reference)) :
    ofRecord (R.observeNodes nodes reference hEvidence) =
      { ofRecord R with
        belief :=
          R.belief.conditionOn
            (R.nodeObservationEvidence nodes reference) hEvidence } :=
  rfl

/-- Set then unset restores the current state (and the record). -/
theorem ofRecord_set_unset {S : ObservedSignature}
    (R : CausalEpistemicRecord S) (target : Fin S.count)
    (value : S.Value target) :
    ofRecord
        ((R.setVariable target value).unsetVariable target
          (setVariable_UnsetReady R target value)) =
      ofRecord R := by
  simp [setVariable_unsetVariable]

end CurrentState

/-! ## 1-cells and their action -/

/-- Action of a one-shot edit: the executable `result`. -/
def act {S T : ObservedSignature} {source : CausalEpistemicRecord S}
    (μ : CausalEditOperation source T) : CausalEpistemicRecord T :=
  μ.result

@[simp] theorem act_eq_result {S T : ObservedSignature}
    {source : CausalEpistemicRecord S} (μ : CausalEditOperation source T) :
    act μ = μ.result :=
  rfl

/-- Terminal learn as a one-shot is `learnRecord`. -/
theorem act_learningTerminal {S : ObservedSignature}
    (spec : TerminalVariableSpec S) (original : CausalEpistemicRecord S) :
    act (.learningTerminal (source := original) spec) =
      spec.learnRecord original :=
  rfl

/-- Terminal forget as a one-shot returns the stored original. -/
theorem act_forgettingTerminal {S : ObservedSignature}
    (spec : TerminalVariableSpec S) (original : CausalEpistemicRecord S) :
    act (.forgettingTerminal original spec) = original :=
  rfl

/-- Exogenous learn as a one-shot is `learnRecord`. -/
theorem act_learningExogenous {S : ObservedSignature}
    (spec : ExogenousVariableSpec) (original : CausalEpistemicRecord S) :
    act (.learningExogenous (source := original) spec) =
      spec.learnRecord original :=
  rfl

/-- Exogenous forget as a one-shot returns the stored original. -/
theorem act_forgettingExogenous {S : ObservedSignature}
    (spec : ExogenousVariableSpec) (original : CausalEpistemicRecord S) :
    act (.forgettingExogenous original spec) = original :=
  rfl

/-! ## Paths as the 1-category of named states -/

/-- Endpoint of a path: the target mode's record. -/
def run {S T : ObservedSignature} {source : CausalMode S}
    {target : CausalMode T} (_path : CausalEditPath source target) :
    CausalEpistemicRecord T :=
  target.record

@[simp] theorem run_nil {S : ObservedSignature} (mode : CausalMode S) :
    run (.nil mode) = mode.record :=
  rfl

/-- A singleton path runs as the underlying one-shot. -/
theorem run_single {S T : ObservedSignature}
    (transition : CausalEditTransition S T) :
    run (.single transition) = act transition.operation :=
  transition.realized

/-- Composition of paths keeps the second path's endpoint. -/
theorem run_append {S M T : ObservedSignature}
    {source : CausalMode S} {middle : CausalMode M} {target : CausalMode T}
    (first : CausalEditPath source middle)
    (second : CausalEditPath middle target) :
    run (append first second) = run second :=
  rfl

end ModeTheory
end Causality
end Thesis
