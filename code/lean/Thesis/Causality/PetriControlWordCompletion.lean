import Thesis.Causality.PetriControl
import Thesis.Causality.PetriWordCompletion

namespace Thesis.Causality.ControlledPetriNet

open PetriNet

/-!
# Partial counter endpoints along a supplied controlled word

The initial and final control states are fixed inputs; counter coordinates
may be fixed to exact natural values or left unspecified. Completion requires
both the literal control path and an enabled counter execution of the same
word. A state-changing path is allowed: returning to the initial state is a
pumping condition, not a requirement of this ordinary execution query.

The classifier checks the whole control path first. If it fails or reaches
the wrong final state, no counter supply can repair the query. Otherwise the
existing ordinary-net completion checker returns its actual counter data or
refutes all counter completions. Conversion preserves the returned endpoint
functions; it neither reruns their word folds nor selects data from a
propositional existence assertion.

Empty words retain both the control state and the counter marking. Zero
counter places do not remove the control check. Token counts and supplied
word lengths remain unbounded, with no imposed search cutoff. This adapter
does not choose a word, leave control states unspecified, or decide general
exact reachability.
-/

variable {places states transitions : Nat}
variable {system : ControlledPetriNet places states transitions}

/-- Exact partial endpoint constraints and the full controlled execution
share one supplied word. Unknown counter values are existentially completed. -/
def WordCompletable (system : ControlledPetriNet places states transitions)
    (state : Fin states) (word : List (Fin transitions)) (next : Fin states)
    (source target : PartialMarking places) : Prop :=
  ∃ before after, source.Matches before ∧ target.Matches after ∧
    system.Execution state before word next after

/-- The path is independent of the counter completion. Both directions
retain the actual endpoints and the same word, including an empty word. -/
theorem wordCompletable_iff_control_and_counters (system : ControlledPetriNet places states transitions)
    (state : Fin states) (word : List (Fin transitions)) (next : Fin states)
    (source target : PartialMarking places) :
    system.WordCompletable state word next source target ↔
      system.controlRun state word = some next ∧ system.net.WordCompletable word source target := by
  constructor
  · rintro ⟨before, after, sourceFits, targetFits, execution⟩
    exact ⟨execution.1, before, after, sourceFits, targetFits, execution.2⟩
  · rintro ⟨control, before, after, sourceFits, targetFits, counters⟩
    exact ⟨before, after, sourceFits, targetFits, control, counters⟩

structure WordCompletionWitness (system : ControlledPetriNet places states transitions)
    (state : Fin states) (word : List (Fin transitions)) (next : Fin states)
    (source target : PartialMarking places) where
  before : Marking places
  after : Marking places
  source_matches : source.Matches before
  target_matches : target.Matches after
  execution : system.Execution state before word next after

namespace WordCompletionWitness

variable {state next : Fin states} {word : List (Fin transitions)} {source target : PartialMarking places}

/-- Attach the computed path proof to actual ordinary-counter witness data.
The numeric fields are copied literally; only the proof of execution changes. -/
def ofCounter (witness : PetriNet.WordCompletionWitness system.net word source target)
    (control : system.controlRun state word = some next) :
    WordCompletionWitness system state word next source target where
  before := witness.before
  after := witness.after
  source_matches := witness.source_matches
  target_matches := witness.target_matches
  execution := ⟨control, witness.execution⟩

@[simp] theorem ofCounter_before (witness : PetriNet.WordCompletionWitness system.net word source target)
    (control : system.controlRun state word = some next) :
    (ofCounter witness control).before = witness.before := rfl

@[simp] theorem ofCounter_after (witness : PetriNet.WordCompletionWitness system.net word source target)
    (control : system.controlRun state word = some next) :
    (ofCounter witness control).after = witness.after := rfl

theorem completable (witness : WordCompletionWitness system state word next source target) :
    system.WordCompletable state word next source target :=
  ⟨witness.before, witness.after, witness.source_matches, witness.target_matches, witness.execution⟩

/-- The returned data agree with both executable components in the original
state/counter space, rather than only with a balance equation. -/
theorem run_exact (witness : WordCompletionWitness system state word next source target) :
    system.controlRun state word = some next ∧ system.net.run witness.before word = some witness.after :=
  ⟨witness.execution.1, (PetriNet.run_eq_some_iff system.net _ _ _).mpr witness.execution.2⟩

/-- Existing compilation also checks exactly these encoded endpoints. No
assumption about a malformed multi-control-token marking is introduced. -/
theorem compiled_run_exact (witness : WordCompletionWitness system state word next source target) :
    system.compiled.run (encode state witness.before) word = some (encode next witness.after) :=
  (PetriNet.run_eq_some_iff system.compiled _ _ _).mpr witness.execution.compile

end WordCompletionWitness

inductive WordCompletionResult (system : ControlledPetriNet places states transitions)
    (state : Fin states) (word : List (Fin transitions)) (next : Fin states)
    (source target : PartialMarking places) where
  | positive (witness : WordCompletionWitness system state word next source target)
  | negative (refuted : ¬ system.WordCompletable state word next source target)

def WordCompletionResult.isPositive {state next : Fin states} {word : List (Fin transitions)}
    {source target : PartialMarking places} : WordCompletionResult system state word next source target → Bool
  | .positive _ => true
  | .negative _ => false

theorem WordCompletionResult.positive_exact {state next : Fin states} {word : List (Fin transitions)}
    {source target : PartialMarking places} (result : WordCompletionResult system state word next source target) :
    result.isPositive = true ↔ system.WordCompletable state word next source target := by
  cases result with
  | positive witness => exact ⟨fun _ => witness.completable, fun _ => rfl⟩
  | negative refuted =>
      constructor
      · intro impossible; cases impossible
      · intro completion; exact False.elim (refuted completion)

theorem WordCompletionResult.negative_exact {state next : Fin states} {word : List (Fin transitions)}
    {source target : PartialMarking places} (result : WordCompletionResult system state word next source target) :
    result.isPositive = false ↔ ¬ system.WordCompletable state word next source target := by
  cases result with
  | positive witness =>
      constructor
      · intro impossible; cases impossible
      · intro refuted; exact False.elim (refuted witness.completable)
  | negative refuted => exact ⟨fun _ => refuted, fun _ => rfl⟩

/-- Decide the finite-state equality before calling the counter checker.
A failed control path excludes every completed marking, not merely the
ordinary checker's selected completion. No general Prop decision is used. -/
def classifyWordCompletion (system : ControlledPetriNet places states transitions)
    (state : Fin states) (word : List (Fin transitions)) (next : Fin states)
    (source target : PartialMarking places) : WordCompletionResult system state word next source target :=
  if control : system.controlRun state word = some next then
    match system.net.classifyWordCompletion word source target with
    | .positive witness => .positive (WordCompletionWitness.ofCounter witness control)
    | .negative refuted => .negative (fun completion =>
        refuted ((wordCompletable_iff_control_and_counters system _ _ _ _ _).mp completion).2)
  else .negative (fun completion =>
    control ((wordCompletable_iff_control_and_counters system _ _ _ _ _).mp completion).1)

theorem classifyWordCompletion_exact (system : ControlledPetriNet places states transitions)
    (state : Fin states) (word : List (Fin transitions)) (next : Fin states)
    (source target : PartialMarking places) :
    (system.classifyWordCompletion state word next source target).isPositive = true ↔
      system.WordCompletable state word next source target :=
  (system.classifyWordCompletion state word next source target).positive_exact

theorem classifyWordCompletion_negative_iff (system : ControlledPetriNet places states transitions)
    (state : Fin states) (word : List (Fin transitions)) (next : Fin states)
    (source target : PartialMarking places) :
    (system.classifyWordCompletion state word next source target).isPositive = false ↔
      ¬ system.WordCompletable state word next source target :=
  (system.classifyWordCompletion state word next source target).negative_exact

end Thesis.Causality.ControlledPetriNet
