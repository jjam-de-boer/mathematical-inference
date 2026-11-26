import Thesis.Causality.PetriExactEndpointEncoding

namespace Thesis.Causality.PetriExactEndpoints

open PetriNet

/-!
# Recovering exact original endpoints and the original execution

An accepted transformed word gives a sound execution in the phased
system. Cleanup preserves every prescribed target coordinate. The
original phase preserves the literal edge sequence and can enter cleanup
only from the requested final state. Setup preserves prescribed source
coordinates and enters the requested initial state.

The decoder computes the marking after setup, erases the auxiliary
edges, and executes just the recovered original word to compute its
endpoint. The soundness proofs certify those computed values. The
resulting equivalence is a reduction to ordinary exact reachability.
-/

variable {places states transitions : Nat}

namespace Query

variable (query : Query places states transitions)

private theorem expose_step {state next : Fin (states + 2)} {before after : Marking places}
    {edge : Fin (edgeCount places transitions)} {rest : List (Fin (edgeCount places transitions))}
    (execution : query.phased.Execution state before (edge :: rest) next after) :
    state = query.edgeSource (Edge.decode edge) ∧
      ∃ middle, (Below (query.consume (Edge.decode edge)) before ∧
        middle = fun place => before place - query.consume (Edge.decode edge) place +
          query.produce (Edge.decode edge) place) ∧
        query.phased.Execution (query.edgeTarget (Edge.decode edge)) middle rest next after :=
  execution_cons_iff.mp execution

/-- Cleanup cannot use an original edge, and every cleanup firing leaves
the fixed target coordinates alone. -/
private theorem cleanup_sound {before after : Marking places}
    {word : List (Fin (edgeCount places transitions))}
    (execution : query.phased.Execution cleanup before word cleanup after)
    (fixedTarget : query.target.Matches after) :
    originalWord word = [] ∧ query.target.Matches before := by
  induction word generalizing before with
  | nil =>
      have counters := execution.2
      cases counters with
      | nil => exact ⟨rfl, fixedTarget⟩
  | cons edge rest ih =>
      have step := query.expose_step execution
      cases tagged : Edge.decode edge <;> rw [tagged] at step
      case original index => exact False.elim (cleanup_ne_running _ step.1)
      case enter => exact False.elim (cleanup_ne_setup step.1)
      case leave => exact False.elim (cleanup_ne_running _ step.1)
      case fill place => exact False.elim (cleanup_ne_setup step.1)
      case drain place =>
        obtain ⟨_, middle, fired, remaining⟩ := step
        obtain ⟨empty, matched⟩ := ih remaining
        refine ⟨by simp only [originalWord, tagged, empty], ?_⟩
        intro counter
        cases fixed : query.target counter with
        | none => exact True.intro
        | some value =>
            have atPlace := matched counter
            rw [fixed] at atPlace
            have unchanged := congrFun fired.2 counter
            simp only [consume, produce, freeUnit_fixed _ _ _ fixed,
              Nat.sub_zero, Nat.add_zero] at unchanged
            exact unchanged.symm.trans atPlace

/-- Decode the original part of any successful suffix that starts in an
original control state. Its endpoint is the counter marking just before
the switch into cleanup, so the fixed target values already hold there. -/
private theorem running_sound {state : Fin states} {before after : Marking places}
    {word : List (Fin (edgeCount places transitions))}
    (execution : query.phased.Execution (running state) before word cleanup after)
    (fixedTarget : query.target.Matches after) :
    ∃ endpoint, query.target.Matches endpoint ∧
      query.system.Execution state before (originalWord word) query.finish endpoint := by
  induction word generalizing state before with
  | nil => exact False.elim (running_ne_cleanup state (Option.some.inj execution.1))
  | cons edge rest ih =>
      have step := query.expose_step execution
      cases tagged : Edge.decode edge <;> rw [tagged] at step
      case enter => exact False.elim (running_ne_setup state step.1)
      case fill place => exact False.elim (running_ne_setup state step.1)
      case drain place => exact False.elim (running_ne_cleanup state step.1)
      case original index =>
        obtain ⟨located, middle, fired, remaining⟩ := step
        obtain ⟨endpoint, matchesTarget, originalTail⟩ := ih remaining
        refine ⟨endpoint, matchesTarget, ?_⟩
        simp only [originalWord, tagged]
        exact execution_cons_iff.mpr ⟨running_inj.mp located, middle, fired, originalTail⟩
      case leave =>
        obtain ⟨located, middle, fired, remaining⟩ := step
        obtain ⟨empty, matched⟩ := query.cleanup_sound remaining fixedTarget
        have unchanged : middle = before := by
          simpa only [consume, produce, Nat.sub_zero, Nat.add_zero] using fired.2
        subst middle
        have same : state = query.finish := running_inj.mp located
        subst state
        refine ⟨before, matched, ?_⟩
        simp only [originalWord, tagged, empty]
        exact ⟨rfl, .nil _⟩

private theorem fill_preserves_source {before : Marking places} {place : Fin places}
    (matchesSource : query.source.Matches before) :
    query.source.Matches (addMarking before (freeUnit query.source place)) := by
  intro counter
  cases fixed : query.source counter with
  | none => exact True.intro
  | some value =>
      have atPlace := matchesSource counter
      rw [fixed] at atPlace
      simpa only [addMarking, freeUnit_fixed _ _ _ fixed, Nat.add_zero] using atPlace

private theorem setup_sound {before after : Marking places}
    {word : List (Fin (edgeCount places transitions))}
    (execution : query.phased.Execution setup before word cleanup after)
    (fixedSource : query.source.Matches before) (fixedTarget : query.target.Matches after) :
    ∃ endpoint, query.source.Matches (query.sourceAfterSetup word before) ∧
      query.target.Matches endpoint ∧ query.system.Execution query.start
        (query.sourceAfterSetup word before) (originalWord word) query.finish endpoint := by
  induction word generalizing before with
  | nil => exact False.elim (setup_ne_cleanup (Option.some.inj execution.1))
  | cons edge rest ih =>
      have step := query.expose_step execution
      cases tagged : Edge.decode edge <;> rw [tagged] at step
      case original index => exact False.elim (setup_ne_running _ step.1)
      case leave => exact False.elim (setup_ne_running _ step.1)
      case drain place => exact False.elim (setup_ne_cleanup step.1)
      case enter =>
        obtain ⟨_, middle, fired, remaining⟩ := step
        have unchanged : middle = before := by
          simpa only [consume, produce, Nat.sub_zero, Nat.add_zero] using fired.2
        subst middle
        obtain ⟨endpoint, matched, original⟩ := query.running_sound remaining fixedTarget
        exact ⟨endpoint,
          by simpa only [sourceAfterSetup, tagged] using fixedSource, matched,
          by simpa only [sourceAfterSetup, originalWord, tagged] using original⟩
      case fill place =>
        obtain ⟨_, middle, fired, remaining⟩ := step
        have added : middle = addMarking before (freeUnit query.source place) := by
          simpa only [consume, produce, addMarking, Nat.sub_zero] using fired.2
        subst middle
        have recovered := ih remaining (query.fill_preserves_source fixedSource)
        simpa only [sourceAfterSetup, originalWord, tagged] using recovered

/-- Recover a concrete witness from any accepted compiled word. The
endpoint comes from the executable original counter run, and the proof
checks it against the endpoint recovered by the phase argument. -/
def decode (word : List (Fin (edgeCount places transitions)))
    (execution : query.compiled.Execution query.initial word query.final) : Witness query := by
  let before := query.sourceAfterSetup word (fixedValues query.source)
  let original := originalWord word
  have phased := (ControlledPetriNet.execution_compiled_iff query.phased setup cleanup
    (fixedValues query.source) (fixedValues query.target) word).mp execution
  have sound := query.setup_sound phased (fixedValues_matches query.source) (fixedValues_matches query.target)
  have ran : (query.system.net.run before original).isSome = true := by
    obtain ⟨endpoint, _, _, actual⟩ := sound
    rw [(run_eq_some_iff query.system.net before endpoint original).mpr actual.2]
    rfl
  let after := (query.system.net.run before original).get ran
  have facts : query.source.Matches before ∧ query.target.Matches after ∧
      query.system.Execution query.start before original query.finish after := by
    obtain ⟨endpoint, sourceFits, targetFits, actual⟩ := sound
    have same : after = endpoint :=
      Option.get_of_eq_some ran ((run_eq_some_iff query.system.net before endpoint original).mpr actual.2)
    exact ⟨sourceFits, same.symm ▸ targetFits, same.symm ▸ actual⟩
  exact ⟨before, after, original, facts.1, facts.2.1, facts.2.2⟩

@[simp] theorem decode_word (word : List (Fin (edgeCount places transitions)))
    (execution : query.compiled.Execution query.initial word query.final) :
    (query.decode word execution).word = originalWord word := rfl

/-- Extending a witness and then decoding its word recovers both original
markings and the literal word. Equality of final markings follows from the
determinism of the executable original counter run. -/
theorem decode_encode (witness : Witness query) :
    let recovered := query.decode (query.encodeWord witness) (query.encodeWord_execution witness)
    recovered.before = witness.before ∧ recovered.word = witness.word ∧ recovered.after = witness.after := by
  let recovered := query.decode (query.encodeWord witness) (query.encodeWord_execution witness)
  have sameSource : recovered.before = witness.before := query.sourceAfterSetup_encodeWord witness
  have sameWord : recovered.word = witness.word := query.originalWord_encodeWord witness
  refine ⟨sameSource, sameWord, ?_⟩
  have recoveredRun := (run_eq_some_iff query.system.net _ _ _).mpr recovered.execution.2
  have originalRun := (run_eq_some_iff query.system.net _ _ _).mpr witness.execution.2
  rw [sameSource, sameWord] at recoveredRun
  exact Option.some.inj (recoveredRun.symm.trans originalRun)

def PartialReachable : Prop :=
  ∃ before after, query.source.Matches before ∧ query.target.Matches after ∧
    query.system.Reachable query.start before query.finish after

/-- Every implementation of exact reachability on ordinary nets can use
this concrete instance and transport both positive and negative results. -/
theorem reachable_compiled_iff :
    query.compiled.Reachable query.initial query.final ↔ query.PartialReachable := by
  constructor
  · rintro ⟨word, execution⟩
    let witness := query.decode word execution
    exact ⟨witness.before, witness.after, witness.source_matches, witness.target_matches,
      witness.word, witness.execution⟩
  · rintro ⟨before, after, fixedSource, fixedTarget, word, execution⟩
    let witness : Witness query := ⟨before, after, word, fixedSource, fixedTarget, execution⟩
    exact ⟨query.encodeWord witness, query.encodeWord_execution witness⟩

end Query

/-- An ordinary net uses the same compiler with one original control state. -/
def ordinaryQuery (net : Thesis.Causality.PetriNet places transitions)
    (source target : PartialMarking places) : Query places 1 transitions where
  system := ⟨net, fun _ => 0, fun _ => 0⟩
  start := 0
  finish := 0
  source := source
  target := target

theorem ordinary_execution (net : Thesis.Causality.PetriNet places transitions)
    (source target : PartialMarking places) (before after : Marking places)
    (word : List (Fin transitions)) :
    (ordinaryQuery net source target).system.Execution 0 before word 0 after ↔
      net.Execution before word after := by
  let system := (ordinaryQuery net source target).system
  have path : system.controlRun 0 word = some 0 := by
    induction word with
    | nil => rfl
    | cons edge rest ih =>
        exact (ControlledPetriNet.controlRun_cons_iff system 0 edge rest 0).mpr ⟨rfl, ih⟩
  exact ⟨fun execution => execution.2, fun execution => ⟨path, execution⟩⟩

theorem ordinary_reachable_compiled_iff (net : Thesis.Causality.PetriNet places transitions)
    (source target : PartialMarking places) :
    let query := ordinaryQuery net source target
    query.compiled.Reachable query.initial query.final ↔
      ∃ before after, source.Matches before ∧ target.Matches after ∧ net.Reachable before after := by
  dsimp only
  rw [(ordinaryQuery net source target).reachable_compiled_iff]
  constructor
  · rintro ⟨before, after, sourceFits, targetFits, word, execution⟩
    exact ⟨before, after, sourceFits, targetFits, word,
      (ordinary_execution net source target before after word).mp execution⟩
  · rintro ⟨before, after, sourceFits, targetFits, word, execution⟩
    exact ⟨before, after, sourceFits, targetFits, word,
      (ordinary_execution net source target before after word).mpr execution⟩

end Thesis.Causality.PetriExactEndpoints
