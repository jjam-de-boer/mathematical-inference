import Thesis.Causality.PetriControlPartialCoverability

namespace Thesis.Causality.Examples.PetriPartialCoverability

open PetriNet

/-!
# Finding covering words with missing initial counter values

The ordinary scan skips an incompatible empty execution and lifts a later
entry, preserving the fixed counter and filling the free counter with its
required token. Fixing that counter to zero excludes both entries.

The controlled example changes state. The first compiled entry fits the
counter constraints but starts in the wrong state. The next entry decodes
to the actual original word and an endpoint that exceeds the target.
The public success and failure theorems are also exercised without large
kernel reductions of the saturation procedure.
-/

def counters (first second : Nat) : Marking 2 :=
  fun place => if place = 0 then first else second

def transfer : Thesis.Causality.PetriNet 2 1 where
  consume := fun _ => counters 0 1
  produce := fun _ => counters 2 0

def freeSupply : PartialMarking 2 :=
  fun place => if place = 0 then some 3 else none

def zeroSupply : PartialMarking 2 :=
  fun place => if place = 0 then some 3 else some 0

def ordinaryInitial := CoverabilityWitness.initial transfer (counters 4 0)

def ordinaryEntries : List (CoverabilityWitness transfer (counters 4 0)) :=
  [ordinaryInitial, ordinaryInitial.prepend 0]

/-- The first entry needs four at coordinate zero. The second needs two
there and one at coordinate one, so the lifted word runs (3,1) to (5,0). -/
theorem scan_skips_first_and_lifts :
    (scanPartialCoverage ordinaryEntries freeSupply).map (fun hit =>
      (hit.witness.source 0, hit.witness.source 1, hit.witness.word, hit.witness.endpoint 0)) =
      some (3, 1, [0], 5) := rfl

theorem scan_respects_fixed_zero :
    (scanPartialCoverage ordinaryEntries zeroSupply).isSome = false := rfl

def move : ControlledPetriNet 2 2 1 where
  net := transfer
  source := fun _ => 0
  target := fun _ => 1

def controlledInitial :=
  CoverabilityWitness.initial move.compiled (ControlledPetriNet.encode (1 : Fin 2) (counters 1 0))

def controlledEntries := [controlledInitial, controlledInitial.prepend 0]

/-- The initial entry fits both counter coordinates. Its state-one token
cannot be kept when the requested initial state is zero. The next entry
reaches state one with the actual counter overshoot. -/
theorem controlled_scan_checks_whole_control_block :
    ((scanPartialCoverage controlledEntries
      (ControlledPetriNet.encodePartial (0 : Fin 2) freeSupply)).map (fun hit =>
        let decoded := ControlledPetriNet.PartialCoverabilityWitness.ofCompiled
          (system := move) (next := 1) (target := counters 1 0) hit
        (decoded.source 0, decoded.source 1, decoded.witness.word, decoded.witness.endpoint 0))) =
      some (3, 1, [0], 5) := rfl

theorem controlled_classifier_finds_word :
    (move.classifyPartialCoverability 0 freeSupply 1 (counters 1 0)).isPositive = true := by
  apply (ControlledPetriNet.classifyPartialCoverability_exact move _ _ _ _).mpr
  refine ⟨counters 3 1, ?_, [0], counters 5 0, ⟨rfl, ?_⟩, ?_⟩
  · intro place
    by_cases zero : place = 0
    · simp only [freeSupply, counters, if_pos zero]
    · simp only [freeSupply, if_neg zero]
  · exact (check_exact transfer _ _ _).mp (by decide +kernel)
  · intro place
    by_cases zero : place = 0
    · simpa only [counters, if_pos zero] using (by decide : 1 ≤ 5)
    · simpa only [counters, if_neg zero] using Nat.le_refl 0

/-- Zero supply prevents the first firing. The empty word cannot change
control state, so the refutation excludes every possible word. -/
theorem controlled_classifier_refutes_fixed_zero :
    (move.classifyPartialCoverability 0 zeroSupply 1 (counters 1 0)).isPositive = false := by
  apply (ControlledPetriNet.classifyPartialCoverability_negative_iff move _ _ _ _).mpr
  rintro ⟨before, fits, word, after, execution, _⟩
  have noSupply : before 1 = 0 := fits 1
  cases word with
  | nil =>
      have impossible : (some (0 : Fin 2)) = some 1 := execution.1
      cases impossible
  | cons edge rest =>
      have counterExecution := execution.2
      cases counterExecution with
      | cons fired _ =>
          have enough := fired.1 1
          change 1 ≤ before 1 at enough
          rw [noSupply] at enough
          exact Nat.not_succ_le_zero 0 enough

end Thesis.Causality.Examples.PetriPartialCoverability
