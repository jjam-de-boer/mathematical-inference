import Thesis.Causality.PetriPartialCoverability
import Thesis.Causality.PetriControlCoverability

namespace Thesis.Causality.ControlledPetriNet

open PetriNet

/-!
# Partial-source coverability with finite control

The source and target control states are supplied. Unspecified coordinates
belong only to the counter block. The compiled source fixes every control
coordinate to the exact single-token encoding, so completing the source
cannot introduce a different control state or an extra control token.

The ordinary partial-source solver returns actual compiled data. The
existing decoder extracts the same word and a counter endpoint in the
requested target state. That endpoint satisfies the target lower bounds.
-/

variable {places states transitions : Nat}
variable {system : ControlledPetriNet places states transitions}

/-- Copy the counter constraints and fix the entire control block. -/
def encodePartial (state : Fin states) (specified : PartialMarking places) :
    PartialMarking (places + states) :=
  Fin.addCases specified (fun other => some (if other = state then 1 else 0))

@[simp] theorem encodePartial_counter (state : Fin states) (specified : PartialMarking places)
    (place : Fin places) :
    encodePartial state specified (place.castAdd states) = specified place := by
  simp only [encodePartial, Fin.addCases_left]

@[simp] theorem encodePartial_control (state : Fin states) (specified : PartialMarking places)
    (other : Fin states) :
    encodePartial state specified (Fin.natAdd places other) =
      some (if other = state then 1 else 0) := by
  simp only [encodePartial, Fin.addCases_right]

/-- Even an arbitrary compiled marking matching this partial source must
have exactly the requested control token. The projected counters retain all
the original constraints. -/
theorem encodePartial_matches_iff (state : Fin states) (specified : PartialMarking places)
    (full : Marking (places + states)) :
    (encodePartial state specified).Matches full ↔
      specified.Matches (project full) ∧ full = encode state (project full) := by
  constructor
  · intro fits
    constructor
    · intro place
      have atPlace := fits (place.castAdd states)
      rw [encodePartial_counter] at atPlace
      exact atPlace
    · funext index
      refine Fin.addCases (fun place => ?_) (fun other => ?_) index
      · exact (encode_counter state (project full) place).symm
      · have atState := fits (Fin.natAdd places other)
        rw [encodePartial_control] at atState
        rw [encode_control]
        exact atState
  · rintro ⟨fits, shape⟩ index
    refine Fin.addCases (fun place => ?_) (fun other => ?_) index
    · rw [encodePartial_counter]
      exact fits place
    · rw [encodePartial_control]
      exact (congrFun shape (Fin.natAdd places other)).trans (encode_control _ _ _)

def PartialCoverable (system : ControlledPetriNet places states transitions)
    (state : Fin states) (specified : PartialMarking places)
    (next : Fin states) (target : Marking places) : Prop :=
  ∃ before, specified.Matches before ∧ system.Coverable state before next target

/-- Compilation preserves and reflects existence of a matching source and
a covering execution, with the same original control endpoints. -/
theorem partialCoverable_compiled_iff (system : ControlledPetriNet places states transitions)
    (state : Fin states) (specified : PartialMarking places)
    (next : Fin states) (target : Marking places) :
    system.compiled.PartialCoverable (encodePartial state specified) (encode next target) ↔
      system.PartialCoverable state specified next target := by
  constructor
  · rintro ⟨full, fits, coverable⟩
    obtain ⟨sourceFits, shape⟩ := (encodePartial_matches_iff state specified full).mp fits
    refine ⟨project full, sourceFits, (coverable_compiled_iff system state next _ target).mp ?_⟩
    rw [← shape]
    exact coverable
  · rintro ⟨before, fits, coverable⟩
    refine ⟨encode state before, (encodePartial_matches_iff state specified _).mpr ?_,
      (coverable_compiled_iff system state next before target).mpr coverable⟩
    rw [project_encode]
    exact ⟨fits, rfl⟩

structure PartialCoverabilityWitness (system : ControlledPetriNet places states transitions)
    (state : Fin states) (specified : PartialMarking places)
    (next : Fin states) (target : Marking places) where
  source : Marking places
  source_matches : specified.Matches source
  witness : CoverabilityWitness system state source next target

namespace PartialCoverabilityWitness

variable {state next : Fin states} {specified : PartialMarking places} {target : Marking places}

theorem coverable (result : PartialCoverabilityWitness system state specified next target) :
    system.PartialCoverable state specified next target :=
  ⟨result.source, result.source_matches, result.witness.coverable⟩

/-- Use the computed compiled source and endpoint directly. The shape proof
licenses the existing decoder and is erased during execution. -/
def ofCompiled
    (result : PetriNet.PartialCoverabilityWitness system.compiled (encodePartial state specified)
      (encode next target)) : PartialCoverabilityWitness system state specified next target :=
  let facts := (encodePartial_matches_iff state specified result.witness.source).mp result.source_matches
  ⟨project result.witness.source, facts.1, CoverabilityWitness.ofCompiled result.witness facts.2⟩

end PartialCoverabilityWitness

inductive PartialCoverabilityResult (system : ControlledPetriNet places states transitions)
    (state : Fin states) (specified : PartialMarking places)
    (next : Fin states) (target : Marking places) where
  | positive (witness : PartialCoverabilityWitness system state specified next target)
  | negative (refuted : ¬ system.PartialCoverable state specified next target)

def PartialCoverabilityResult.isPositive {state next : Fin states}
    {specified : PartialMarking places} {target : Marking places} :
    PartialCoverabilityResult system state specified next target → Bool
  | .positive _ => true
  | .negative _ => false

def classifyPartialCoverability (system : ControlledPetriNet places states transitions)
    (state : Fin states) (specified : PartialMarking places)
    (next : Fin states) (target : Marking places) :
    PartialCoverabilityResult system state specified next target :=
  match system.compiled.classifyPartialCoverability (encodePartial state specified) (encode next target) with
  | .positive witness => .positive (PartialCoverabilityWitness.ofCompiled witness)
  | .negative refuted => .negative (fun coverable =>
      refuted ((partialCoverable_compiled_iff system state specified next target).mpr coverable))

theorem classifyPartialCoverability_exact (system : ControlledPetriNet places states transitions)
    (state : Fin states) (specified : PartialMarking places) (next : Fin states) (target : Marking places) :
    (system.classifyPartialCoverability state specified next target).isPositive = true ↔
      system.PartialCoverable state specified next target := by
  cases system.classifyPartialCoverability state specified next target with
  | positive witness => exact ⟨fun _ => witness.coverable, fun _ => rfl⟩
  | negative refuted =>
      exact ⟨fun impossible => Bool.noConfusion impossible, fun possible => False.elim (refuted possible)⟩

theorem classifyPartialCoverability_negative_iff (system : ControlledPetriNet places states transitions)
    (state : Fin states) (specified : PartialMarking places) (next : Fin states) (target : Marking places) :
    (system.classifyPartialCoverability state specified next target).isPositive = false ↔
      ¬ system.PartialCoverable state specified next target := by
  cases system.classifyPartialCoverability state specified next target with
  | positive witness =>
      exact ⟨fun impossible => Bool.noConfusion impossible,
        fun refuted => False.elim (refuted witness.coverable)⟩
  | negative refuted => exact ⟨fun _ => refuted, fun _ => rfl⟩

end Thesis.Causality.ControlledPetriNet
