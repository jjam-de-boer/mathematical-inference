import Thesis.Causality.PetriNet

namespace Thesis.Causality

/-!
# Exact compilation of finite control into Petri places

A controlled net retains the existing consumption and production tables,
with a source and destination state for every literal transition index.
Compilation adds one place per control state. Encoded configurations have
exactly one control token; an edge consumes it at its source and produces
it at its destination. Self-loops still consume their control token, so
zero control displacement never removes the state's enabling requirement.

Only the control carrier is finite: all counter values and execution-word
lengths remain unbounded. Correctness starts from an encoded configuration.
Arbitrary compiled markings with several control tokens have no claimed
single-state interpretation. Every reachable endpoint is decoded, rather
than assuming that a solver happens to return another encoded marking.

The word is unchanged by compilation. The controlled semantics checks the
entire control path and the original enabled counter execution along that
same word. No graph-search oracle, finite counter bound, or representative
selected from a propositional existence assertion is used.
-/

structure ControlledPetriNet (places states transitions : Nat) where
  net : PetriNet places transitions
  source : Fin transitions → Fin states
  target : Fin transitions → Fin states

namespace ControlledPetriNet

open PetriNet

variable {places states transitions : Nat}
variable {system : ControlledPetriNet places states transitions}

/-- The two literal blocks are counters first and control places second.
Finite indices and Boolean equality give the displayed encoding directly. -/
def encode (state : Fin states) (marking : Marking places) : Marking (places + states) :=
  Fin.addCases marking (fun other => if other = state then 1 else 0)

def project (marking : Marking (places + states)) : Marking places :=
  fun place => marking (place.castAdd states)

@[simp] theorem encode_counter (state : Fin states) (marking : Marking places) (place : Fin places) :
    encode state marking (place.castAdd states) = marking place := by
  simp only [encode, Fin.addCases_left]

@[simp] theorem encode_control (state : Fin states) (marking : Marking places) (other : Fin states) :
    encode state marking (Fin.natAdd places other) = if other = state then 1 else 0 := by
  simp only [encode, Fin.addCases_right]

@[simp] theorem project_encode (state : Fin states) (marking : Marking places) :
    project (encode state marking) = marking := by
  funext place
  exact encode_counter state marking place

/-- Dominating an encoded target forces the exact same control state.
Counter values alone may overshoot. This lemma needs both markings encoded. -/
theorem encode_below_iff (leftState rightState : Fin states) (left right : Marking places) :
    Below (encode leftState left) (encode rightState right) ↔
      leftState = rightState ∧ Below left right := by
  constructor
  · intro enough
    have state : leftState = rightState := by
      by_cases same : leftState = rightState
      · exact same
      · have bound := enough (Fin.natAdd places leftState)
        simp only [encode_control, ite_true, if_neg same] at bound
        exact False.elim (by omega)
    refine ⟨state, ?_⟩
    intro place
    simpa only [encode_counter] using enough (place.castAdd states)
  · rintro ⟨rfl, enough⟩ index
    refine Fin.addCases (fun place => ?_) (fun state => ?_) index
    · simpa only [encode_counter] using enough place
    · simp only [encode_control]
      exact Nat.le_refl _

theorem encode_injective {leftState rightState : Fin states} {left right : Marking places}
    (equal : encode leftState left = encode rightState right) : leftState = rightState ∧ left = right := by
  have enough : Below (encode leftState left) (encode rightState right) := by
    intro index
    exact Nat.le_of_eq (congrFun equal index)
  refine ⟨((encode_below_iff _ _ _ _).mp enough).1, ?_⟩
  exact (project_encode leftState left).symm.trans
    ((congrArg project equal).trans (project_encode rightState right))

/-- Each compiled edge retains its original counter guard and adds a
control guard. There is one compiled transition per original edge. -/
def compiled (system : ControlledPetriNet places states transitions) : PetriNet (places + states) transitions where
  consume := fun edge => encode (system.source edge) (system.net.consume edge)
  produce := fun edge => encode (system.target edge) (system.net.produce edge)

def Fires (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (edge : Fin transitions)
    (next : Fin states) (after : Marking places) : Prop :=
  state = system.source edge ∧ next = system.target edge ∧ system.net.Fires before edge after

/-- Forward compilation preserves exact enabled firing, including control
self-loops and overlapping counter consumption/production requirements. -/
theorem Fires.compile {state next : Fin states} {before after : Marking places} {edge : Fin transitions}
    (fired : system.Fires state before edge next after) :
    system.compiled.Fires (encode state before) edge (encode next after) := by
  rcases fired with ⟨rfl, rfl, counter⟩
  constructor
  · intro index
    refine Fin.addCases (fun place => ?_) (fun state => ?_) index
    · simpa only [compiled, encode_counter] using counter.1 place
    · change encode (system.source edge) (system.net.consume edge) (Fin.natAdd places state) ≤
        encode (system.source edge) before (Fin.natAdd places state)
      simp only [encode_control]
      exact Nat.le_refl _
  · funext index
    refine Fin.addCases (fun place => ?_) (fun state => ?_) index
    · simpa only [compiled, encode_counter] using congrFun counter.2 place
    · change encode (system.target edge) after (Fin.natAdd places state) =
        encode (system.source edge) before (Fin.natAdd places state) -
          encode (system.source edge) (system.net.consume edge) (Fin.natAdd places state) +
          encode (system.target edge) (system.net.produce edge) (Fin.natAdd places state)
      simp only [encode_control, Nat.sub_self, Nat.zero_add]

/-- Decode an arbitrary successor. The source's single control token
forces the edge's source, and the exact firing equation supplies the entire
encoded successor shape, not only a conservation-of-token-count fact. -/
theorem decode_firing {state : Fin states} {before : Marking places}
    {edge : Fin transitions} {after : Marking (places + states)}
    (fired : system.compiled.Fires (encode state before) edge after) :
    state = system.source edge ∧
      after = encode (system.target edge) (project after) ∧
      system.net.Fires before edge (project after) := by
  have source : state = system.source edge := by
    by_cases same : state = system.source edge
    · exact same
    · have absent : system.source edge ≠ state := Ne.symm same
      have ready := fired.1 (Fin.natAdd places (system.source edge))
      change encode (system.source edge) (system.net.consume edge) (Fin.natAdd places (system.source edge)) ≤
        encode state before (Fin.natAdd places (system.source edge)) at ready
      simp only [encode_control, ite_true, if_neg absent] at ready
      exact False.elim (by omega)
  refine ⟨source, ?_, ?_⟩
  · funext index
    refine Fin.addCases (fun place => ?_) (fun control => ?_) index
    · rw [encode_counter]
      rfl
    · have result := congrFun fired.2 (Fin.natAdd places control)
      change after (Fin.natAdd places control) =
        encode state before (Fin.natAdd places control) -
          encode (system.source edge) (system.net.consume edge) (Fin.natAdd places control) +
          encode (system.target edge) (system.net.produce edge) (Fin.natAdd places control) at result
      simpa only [encode_control, source, Nat.sub_self, Nat.zero_add] using result
  · constructor
    · intro place
      simpa only [compiled, encode_counter] using fired.1 (place.castAdd states)
    · funext place
      simpa only [compiled, encode_counter, project] using congrFun fired.2 (place.castAdd states)

theorem firing_compiled_iff (system : ControlledPetriNet places states transitions)
    (state next : Fin states) (before after : Marking places) (edge : Fin transitions) :
    system.compiled.Fires (encode state before) edge (encode next after) ↔
      system.Fires state before edge next after := by
  constructor
  · intro fired
    have decoded := decode_firing fired
    have stateEqual := (encode_injective decoded.2.1).1
    exact ⟨decoded.1, stateEqual, by simpa only [project_encode] using decoded.2.2⟩
  · exact Fires.compile

/-- Read the supplied edge word literally. A wrong-state edge rejects the
whole path. The returned state is computed even before counter execution
is considered; no finite search over counter configurations is involved. -/
def controlRun (system : ControlledPetriNet places states transitions) :
    Fin states → List (Fin transitions) → Option (Fin states)
  | state, [] => some state
  | state, edge :: rest =>
      if state = system.source edge then controlRun system (system.target edge) rest else none

theorem controlRun_cons_iff (system : ControlledPetriNet places states transitions)
    (state : Fin states) (edge : Fin transitions) (rest : List (Fin transitions)) (next : Fin states) :
    system.controlRun state (edge :: rest) = some next ↔
      state = system.source edge ∧ system.controlRun (system.target edge) rest = some next := by
  change (if state = system.source edge then system.controlRun (system.target edge) rest else none) = some next ↔ _
  split
  · next same => exact ⟨fun accepted => ⟨same, accepted⟩, fun accepted => accepted.2⟩
  · next wrong =>
      constructor
      · intro impossible; cases impossible
      · intro accepted; exact False.elim (wrong accepted.1)

/-- Concatenation retains the actual intermediate state. A rejected first
word cannot become an accepted path by appending another word. -/
theorem controlRun_append (system : ControlledPetriNet places states transitions)
    (state : Fin states) (first second : List (Fin transitions)) :
    system.controlRun state (first ++ second) =
      (system.controlRun state first).bind (fun next => system.controlRun next second) := by
  induction first generalizing state with
  | nil => rfl
  | cons edge rest ih =>
      simp only [List.cons_append, controlRun]
      split
      · exact ih (system.target edge)
      · rfl

/-- The independent control and counter semantics share the very same
word. In particular an empty word retains both complete endpoints. -/
def Execution (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (word : List (Fin transitions))
    (next : Fin states) (after : Marking places) : Prop :=
  system.controlRun state word = some next ∧ system.net.Execution before word after

/-- Both halves join at the same control state and counter marking. This
is also the composition used when a returning pump is repeated. -/
theorem Execution.append {state middleState next : Fin states} {before middle after : Marking places}
    {first second : List (Fin transitions)} (left : system.Execution state before first middleState middle)
    (right : system.Execution middleState middle second next after) :
    system.Execution state before (first ++ second) next after := by
  refine ⟨?_, left.2.append right.2⟩
  rw [controlRun_append, left.1, Option.bind_some]
  exact right.1

theorem Execution.compile {state next : Fin states} {before after : Marking places}
    {word : List (Fin transitions)} (execution : system.Execution state before word next after) :
    system.compiled.Execution (encode state before) word (encode next after) := by
  rcases execution with ⟨control, counters⟩
  induction counters generalizing state with
  | nil =>
      have same := Option.some.inj control
      cases same
      exact .nil _
  | cons fired remaining ih =>
      have first := (controlRun_cons_iff system _ _ _ _).mp control
      exact .cons (Fires.compile ⟨first.1, rfl, fired⟩) (ih first.2)

/-- This forward decoding theorem quantifies over every compiled final
marking. Each actual firing restores the single-token encoding, so an
intermediate or final malformed control marking cannot be silently ignored. -/
theorem execution_decoding {state : Fin states} {before : Marking places}
    {word : List (Fin transitions)} {after : Marking (places + states)}
    (execution : system.compiled.Execution (encode state before) word after) :
    ∃ next, system.controlRun state word = some next ∧
      after = encode next (project after) ∧ system.net.Execution before word (project after) := by
  induction word generalizing state before after with
  | nil =>
      cases execution
      refine ⟨state, rfl, ?_, ?_⟩
      · simp only [project_encode]
      · rw [project_encode]
        exact .nil _
  | cons edge rest ih =>
      cases execution with
      | @cons _ middle _ _ _ fired remaining =>
          have first := decode_firing (system := system) fired
          rw [first.2.1] at remaining
          obtain ⟨next, control, shape, counters⟩ := ih remaining
          exact ⟨next, (controlRun_cons_iff system _ _ _ _).mpr ⟨first.1, control⟩,
            shape, .cons first.2.2 counters⟩

/-- Only the final control index is extra data: the counter marking is
read directly from the given endpoint and the literal word is unchanged. -/
structure DecodedExecution (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (word : List (Fin transitions))
    (after : Marking (places + states)) where
  finalState : Fin states
  execution : system.Execution state before word finalState (project after)
  endpoint : after = encode finalState (project after)

/-- Recover the final state from the computed option, not from the
existential theorem above. That theorem is used only to certify success and
the resulting proof fields. This remains executable after proofs are erased. -/
def decodeExecution {state : Fin states} {before : Marking places}
    {word : List (Fin transitions)} {after : Marking (places + states)}
    (execution : system.compiled.Execution (encode state before) word after) :
    DecodedExecution system state before word after := by
  have present : (system.controlRun state word).isSome = true := by
    obtain ⟨next, control, _, _⟩ := execution_decoding execution
    rw [control]
    rfl
  let next := (system.controlRun state word).get present
  have control : system.controlRun state word = some next := by
    cases computed : system.controlRun state word with
    | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at present
    | some value => simp only [next, computed, Option.get_some]
  have facts : system.Execution state before word next (project after) ∧
      after = encode next (project after) := by
    obtain ⟨other, checked, shape, counters⟩ := execution_decoding execution
    have same : other = next := Option.some.inj (checked.symm.trans control)
    rw [same] at shape
    exact ⟨⟨control, counters⟩, shape⟩
  exact ⟨next, facts.1, facts.2⟩

theorem execution_compiled_iff (system : ControlledPetriNet places states transitions)
    (state next : Fin states) (before after : Marking places) (word : List (Fin transitions)) :
    system.compiled.Execution (encode state before) word (encode next after) ↔
      system.Execution state before word next after := by
  constructor
  · intro execution
    let decoded := decodeExecution execution
    have same : next = decoded.finalState := (encode_injective decoded.endpoint).1
    simpa only [project_encode, ← same] using decoded.execution
  · exact Execution.compile

def Reachable (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (next : Fin states) (after : Marking places) : Prop :=
  ∃ word, system.Execution state before word next after

theorem reachable_compiled_iff (system : ControlledPetriNet places states transitions)
    (state next : Fin states) (before after : Marking places) :
    system.compiled.Reachable (encode state before) (encode next after) ↔
      system.Reachable state before next after := by
  constructor
  · rintro ⟨word, execution⟩
    exact ⟨word, (execution_compiled_iff system _ _ _ _ _).mp execution⟩
  · rintro ⟨word, execution⟩
    exact ⟨word, execution.compile⟩

/-- Coverability fixes the requested control state exactly and permits
only the counter values to overshoot. Counter values are never bounded. -/
def Coverable (system : ControlledPetriNet places states transitions)
    (state : Fin states) (before : Marking places) (next : Fin states) (target : Marking places) : Prop :=
  ∃ word after, system.Execution state before word next after ∧ Below target after

theorem coverable_compiled_iff (system : ControlledPetriNet places states transitions)
    (state next : Fin states) (before target : Marking places) :
    system.compiled.Coverable (encode state before) (encode next target) ↔
      system.Coverable state before next target := by
  constructor
  · rintro ⟨after, ⟨word, execution⟩, covers⟩
    let decoded := decodeExecution execution
    have encoded : Below (encode next target) (encode decoded.finalState (project after)) := by
      rw [← decoded.endpoint]
      exact covers
    have enough := (encode_below_iff _ _ _ _).mp encoded
    refine ⟨word, project after, ?_, enough.2⟩
    simpa only [← enough.1] using decoded.execution
  · rintro ⟨word, after, execution, enough⟩
    exact ⟨encode next after, ⟨word, execution.compile⟩,
      (encode_below_iff _ _ _ _).mpr ⟨rfl, enough⟩⟩

end ControlledPetriNet
end Thesis.Causality
