import Thesis.Causality.PetriControl
import Thesis.Causality.PetriCoverabilitySearch

namespace Thesis.Causality.ControlledPetriNet

open PetriNet

/-!
# Coverability results in the original controlled counter space

The existing classifier is called once on the compiled single-control-token
source and target. A positive result is decoded back into the original
counter marking and the same literal transition word. Its execution reaches
the requested control state exactly; only the counter target may be exceeded.

The compiled endpoint is not assumed to be encoded. The compiler's decoder
proves its shape from the actual execution, and target coverage then forces
the recovered control state to equal the requested one. Original-space data
are read from that supplied endpoint; no word or marking is chosen from a
propositional existence statement.

A negative result refutes every finite controlled covering execution, with
no token or word cutoff. The search and its termination proof are unchanged.
This adapter adds no controlled pumping, partial-endpoint interpretation,
exact-reachability solver or runtime pilot.
-/

variable {places states transitions : Nat}
variable {system : ControlledPetriNet places states transitions}

structure CoverabilityWitness (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (next : Fin states) (target : Marking places) where
  word : List (Fin transitions)
  endpoint : Marking places
  execution : system.Execution state before word next endpoint
  covers : Below target endpoint

namespace CoverabilityWitness

variable {state next : Fin states} {before target : Marking places}

theorem coverable (witness : CoverabilityWitness system state before next target) :
    system.Coverable state before next target :=
  ⟨witness.word, witness.endpoint, witness.execution, witness.covers⟩

/-- Convert actual compiled witness data. The supplied source equality
allows decoding from the original encoded input, even if the witness was
assembled by lifting a smaller basis entry during saturation. -/
def ofCompiled (witness : PetriNet.CoverabilityWitness system.compiled (encode next target))
    (source : witness.source = encode state before) : CoverabilityWitness system state before next target := by
  have execution : system.compiled.Execution (encode state before) witness.word witness.endpoint := by
    simpa only [source] using witness.execution
  let decoded := decodeExecution execution
  have encoded : Below (encode next target) (encode decoded.finalState (project witness.endpoint)) := by
    rw [← decoded.endpoint]
    exact witness.covers
  have enough := (encode_below_iff _ _ _ _).mp encoded
  exact {
    word := witness.word
    endpoint := project witness.endpoint
    execution := by simpa only [← enough.1] using decoded.execution
    covers := enough.2 }

/-- Conversion preserves the concrete word, not only its existence or
transition counts. The counter endpoint is the literal counter projection. -/
@[simp] theorem ofCompiled_word
    (witness : PetriNet.CoverabilityWitness system.compiled (encode next target))
    (source : witness.source = encode state before) :
    (ofCompiled witness source).word = witness.word := rfl

@[simp] theorem ofCompiled_endpoint
    (witness : PetriNet.CoverabilityWitness system.compiled (encode next target))
    (source : witness.source = encode state before) :
    (ofCompiled witness source).endpoint = project witness.endpoint := rfl

end CoverabilityWitness

inductive CoverabilityResult (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (next : Fin states) (target : Marking places) where
  | positive (witness : CoverabilityWitness system state before next target)
  | negative (refuted : ¬ system.Coverable state before next target)

def CoverabilityResult.isPositive {state next : Fin states} {before target : Marking places} :
    CoverabilityResult system state before next target → Bool
  | .positive _ => true
  | .negative _ => false

theorem CoverabilityResult.positive_exact {state next : Fin states} {before target : Marking places}
    (result : CoverabilityResult system state before next target) :
    result.isPositive = true ↔ system.Coverable state before next target := by
  cases result with
  | positive witness => exact ⟨fun _ => witness.coverable, fun _ => rfl⟩
  | negative refuted =>
      constructor
      · intro impossible; cases impossible
      · intro coverable; exact False.elim (refuted coverable)

theorem CoverabilityResult.negative_exact {state next : Fin states} {before target : Marking places}
    (result : CoverabilityResult system state before next target) :
    result.isPositive = false ↔ ¬ system.Coverable state before next target := by
  cases result with
  | positive witness =>
      constructor
      · intro impossible; cases impossible
      · intro refuted; exact False.elim (refuted witness.coverable)
  | negative refuted => exact ⟨fun _ => refuted, fun _ => rfl⟩

/-- The sole search call is the existing compiled coverability classifier.
Positive data are recovered in the original counter space; failure is
transported through the proved exact compilation correspondence. -/
def classifyCoverability (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (next : Fin states) (target : Marking places) :
    CoverabilityResult system state before next target :=
  match system.compiled.classifyCoverability (encode state before) (encode next target) with
  | .positive witness source => .positive (CoverabilityWitness.ofCompiled witness source)
  | .negative refuted =>
      .negative (fun coverable => refuted ((coverable_compiled_iff system _ _ _ _).mpr coverable))

theorem classifyCoverability_exact (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (next : Fin states) (target : Marking places) :
    (system.classifyCoverability state before next target).isPositive = true ↔
      system.Coverable state before next target :=
  (system.classifyCoverability state before next target).positive_exact

theorem classifyCoverability_negative_iff (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (next : Fin states) (target : Marking places) :
    (system.classifyCoverability state before next target).isPositive = false ↔
      ¬ system.Coverable state before next target :=
  (system.classifyCoverability state before next target).negative_exact

end Thesis.Causality.ControlledPetriNet
