import Thesis.Causality.PetriExactEndpointGadget
import Thesis.Causality.PetriPredecessors

namespace Thesis.Causality.PetriExactEndpoints

open PetriNet

/-!
# Extending a supplied execution to the compiled exact endpoints

The setup and cleanup words visit each free coordinate once per token
in the corresponding original marking. Their effects are proved by
induction on these finite lists. The embedded original word is unchanged
apart from its edge indices. Concatenation puts the two phase switches at
the actual original source and target, so all original guards still apply.
-/

variable {places states transitions : Nat}

-- Counting only needs decidable equality on finite place indices. Use its
-- direct lawfulness proof instead of synthesizing one through ordered types.
local instance placeBEq : BEq (Fin places) := instBEqOfDecidableEq
local instance lawfulPlaceBEq : LawfulBEq (Fin places) := instLawfulBEq

structure Witness (query : Query places states transitions) where
  before : Marking places
  after : Marking places
  word : List (Fin transitions)
  source_matches : query.source.Matches before
  target_matches : query.target.Matches after
  execution : query.system.Execution query.start before word query.finish after

private def repeatsAt (values : Marking places) (indices : List (Fin places)) : List (Fin places) :=
  indices.flatMap (fun index => List.replicate (values index) index)

private theorem count_repeatsAt (values : Marking places) (indices : List (Fin places))
    (distinct : indices.Nodup) (place : Fin places) :
    (repeatsAt values indices).count place = if indices.contains place then values place else 0 := by
  induction indices with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      change (List.replicate (values head) head ++ repeatsAt values tail).count place =
        (if (head :: tail).contains place then values place else 0)
      rw [List.count_append, List.count_replicate, ih tailDistinct, List.contains_cons]
      by_cases same : head = place
      · subst head
        have tailMiss : tail.contains place = false :=
          Bool.eq_false_iff.mpr (fun present => absent (List.contains_iff_mem.mp present))
        have self : (place == place) = true := decide_eq_true rfl
        simp only [self, Bool.true_or, tailMiss, Bool.false_eq_true, if_false,
          if_true, Nat.add_zero]
      · have beqOff : (head == place) = false := by
          exact Bool.eq_false_iff.mpr (fun yes => same (of_decide_eq_true yes))
        have reverseOff : (place == head) = false :=
          Bool.eq_false_iff.mpr (fun yes => same (of_decide_eq_true yes).symm)
        simp only [beqOff, reverseOff, Bool.false_eq_true, if_false, Nat.zero_add, Bool.false_or]

private theorem finRange_nodup : ∀ n, (List.finRange n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.finRange_succ]
      refine List.nodup_cons.mpr ⟨?_, List.Pairwise.map Fin.succ
        (fun _ _ different equal => different (Fin.succ_inj.mp equal)) (finRange_nodup n)⟩
      intro member
      obtain ⟨index, _, equal⟩ := List.mem_map.mp member
      exact Fin.succ_ne_zero index equal

private def visits (specified : PartialMarking places) (value : Marking places) :
    List (Fin places) :=
  repeatsAt (fun place => if (specified place).isNone then value place else 0)
    (List.finRange places)

private def adjustment (specified : PartialMarking places) (indices : List (Fin places)) :
    Marking places :=
  fun place => if (specified place).isNone then indices.count place else 0

private theorem adjustment_nil (specified : PartialMarking places) (place : Fin places) :
    adjustment specified [] place = 0 := by
  simp only [adjustment, List.count_nil, ite_self]

private theorem adjustment_cons (specified : PartialMarking places) (head : Fin places)
    (tail : List (Fin places)) (place : Fin places) :
    adjustment specified (head :: tail) place =
      freeUnit specified head place + adjustment specified tail place := by
  by_cases same : head = place
  · subst head
    simp only [adjustment, freeUnit, List.count_cons_self]
    split <;> simp only [if_true] <;> omega
  · simp only [adjustment, freeUnit, if_neg (Ne.symm same), List.count_cons_of_ne same, Nat.zero_add]

private theorem fixedValues_add_visits {specified : PartialMarking places} {value : Marking places}
    (fits : specified.Matches value) :
    addMarking (fixedValues specified) (adjustment specified (visits specified value)) = value := by
  funext place
  have count := count_repeatsAt (fun place => if (specified place).isNone then value place else 0)
    (List.finRange places) (finRange_nodup places) place
  rw [if_pos (List.contains_iff_mem.mpr (List.mem_finRange place))] at count
  have matched := fits place
  cases fixed : specified place with
  | none =>
      simp only [addMarking, fixedValues, adjustment, visits, fixed, Option.getD_none,
        Option.isNone_none, if_true, Nat.zero_add]
      simpa only [fixed, Option.isNone_none, if_true] using count
  | some tokens =>
      rw [fixed] at matched
      simp only [addMarking, fixedValues, adjustment, fixed, Option.getD_some,
        Option.isNone_some, Bool.false_eq_true, if_false, Nat.add_zero]
      exact matched.symm

namespace Query

variable (query : Query places states transitions)

private theorem step (edge : Edge places transitions) {before after : Marking places}
    (enough : Below (query.consume edge) before)
    (actual : after = fun place => before place - query.consume edge place + query.produce edge place) :
    query.phased.Execution (query.edgeSource edge) before [edge.encode] (query.edgeTarget edge) after := by
  refine execution_cons_iff.mpr ⟨(query.phased_source_encode edge).symm, after, ?_, ?_⟩
  · simp only [Fires, Enabled, phased_consume_encode, phased_produce_encode]
    exact ⟨enough, actual⟩
  · rw [phased_target_encode]
    exact ⟨rfl, .nil _⟩

private def fillWord (indices : List (Fin places)) : List (Fin (edgeCount places transitions)) :=
  indices.map (fun place => (Edge.fill place : Edge places transitions).encode)

private def drainWord (indices : List (Fin places)) : List (Fin (edgeCount places transitions)) :=
  indices.map (fun place => (Edge.drain place : Edge places transitions).encode)

/-- Compute the counters at the end of the initial fill block. The
controlled execution proof guarantees that a successful run then switches
into the original system. -/
def sourceAfterSetup (query : Query places states transitions) :
    List (Fin (edgeCount places transitions)) → Marking places → Marking places
  | [], before => before
  | edge :: rest, before =>
    match Edge.decode edge with
    | .fill place => sourceAfterSetup query rest (addMarking before (freeUnit query.source place))
    | _ => before

private theorem sourceAfterSetup_fill (indices : List (Fin places))
    (rest : List (Fin (edgeCount places transitions))) (before : Marking places) :
    query.sourceAfterSetup (fillWord indices ++ (Edge.enter : Edge places transitions).encode :: rest) before =
      addMarking before (adjustment query.source indices) := by
  induction indices generalizing before with
  | nil =>
      funext place
      simp only [fillWord, List.map_nil, List.nil_append, sourceAfterSetup, Edge.decode_encode,
        addMarking, adjustment_nil, Nat.add_zero]
  | cons head tail ih =>
      simp only [fillWord, List.map_cons, List.cons_append, sourceAfterSetup, Edge.decode_encode]
      rw [← fillWord, ih]
      funext place
      simp only [addMarking, adjustment_cons, Nat.add_assoc]

private theorem fill_execution (indices : List (Fin places)) (before : Marking places) :
    query.phased.Execution setup before (fillWord indices) setup
      (addMarking before (adjustment query.source indices)) := by
  induction indices generalizing before with
  | nil =>
      have same : addMarking before (adjustment query.source []) = before := by
        funext place
        simp only [addMarking, adjustment_nil, Nat.add_zero]
      rw [same]
      exact ⟨rfl, .nil _⟩
  | cons head tail ih =>
      let middle := addMarking before (freeUnit query.source head)
      have first := query.step (.fill head) (before := before) (after := middle)
        (fun place => Nat.zero_le (before place)) (by
          funext place
          simp only [middle, addMarking, consume, produce, Nat.sub_zero])
      have same : addMarking middle (adjustment query.source tail) =
          addMarking before (adjustment query.source (head :: tail)) := by
        funext place
        simp only [middle, addMarking, adjustment_cons, Nat.add_assoc]
      rw [← same]
      exact first.append (ih middle)

private theorem drain_execution (indices : List (Fin places)) (after : Marking places) :
    query.phased.Execution cleanup (addMarking after (adjustment query.target indices))
      (drainWord indices) cleanup after := by
  induction indices with
  | nil =>
      have same : addMarking after (adjustment query.target []) = after := by
        funext place
        simp only [addMarking, adjustment_nil, Nat.add_zero]
      rw [same]
      exact ⟨rfl, .nil _⟩
  | cons head tail ih =>
      let before := addMarking after (adjustment query.target (head :: tail))
      let middle := addMarking after (adjustment query.target tail)
      have first := query.step (.drain head) (before := before) (after := middle) (by
        intro place
        simp only [before, addMarking, adjustment_cons, consume]
        omega) (by
        funext place
        simp only [before, middle, addMarking, adjustment_cons, consume, produce, Nat.add_zero]
        omega)
      exact first.append ih

def embedWord (word : List (Fin transitions)) : List (Fin (edgeCount places transitions)) :=
  word.map (fun edge => (Edge.original edge : Edge places transitions).encode)

private theorem original_execution {state next : Fin states} {before after : Marking places}
    {word : List (Fin transitions)} (execution : query.system.Execution state before word next after) :
    query.phased.Execution (running state) before (embedWord word) (running next) after := by
  induction word generalizing state before after with
  | nil =>
      have same : state = next := Option.some.inj execution.1
      subst next
      have counters := execution.2
      cases counters with
      | nil => exact ⟨rfl, .nil _⟩
  | cons edge tail ih =>
      obtain ⟨atState, middle, first, remaining⟩ := execution_cons_iff.mp execution
      have step := query.step (.original edge) first.1 first.2
      rw [atState]
      exact step.append (ih remaining)

private theorem enter_execution (before : Marking places) :
    query.phased.Execution setup before [(Edge.enter : Edge places transitions).encode]
      (running query.start) before :=
  query.step .enter (fun place => Nat.zero_le (before place)) (by
    funext place
    simp only [consume, produce, Nat.sub_zero, Nat.add_zero])

private theorem leave_execution (after : Marking places) :
    query.phased.Execution (running query.finish) after [(Edge.leave : Edge places transitions).encode]
      cleanup after :=
  query.step .leave (fun place => Nat.zero_le (after place)) (by
    funext place
    simp only [consume, produce, Nat.sub_zero, Nat.add_zero])

/-- Extend the literal original word by the computable setup and cleanup
words. The two zero-effect switches delimit the original execution. -/
def encodeWord (witness : Witness query) : List (Fin (edgeCount places transitions)) :=
  ((fillWord (visits query.source witness.before) ++ [(Edge.enter : Edge places transitions).encode] ++
    embedWord witness.word) ++ [(Edge.leave : Edge places transitions).encode]) ++
    drainWord (visits query.target witness.after)

theorem sourceAfterSetup_encodeWord (witness : Witness query) :
    query.sourceAfterSetup (query.encodeWord witness) (fixedValues query.source) = witness.before := by
  simp only [encodeWord, List.append_assoc, List.cons_append, sourceAfterSetup_fill,
    fixedValues_add_visits witness.source_matches]

/-- The round trip retains the original word, including its order and
repeated edges. No phase edge becomes an original edge. -/
@[simp] theorem originalWord_encodeWord (witness : Witness query) :
    originalWord (query.encodeWord witness) = witness.word := by
  have discardFill (indices : List (Fin places)) :
      originalWord (fillWord (transitions := transitions) indices) = [] := by
    induction indices with
    | nil => rfl
    | cons place rest ih =>
        simp only [fillWord, List.map_cons, originalWord, Edge.decode_encode]
        exact ih
  have discardDrain (indices : List (Fin places)) :
      originalWord (drainWord (transitions := transitions) indices) = [] := by
    induction indices with
    | nil => rfl
    | cons place rest ih =>
        simp only [drainWord, List.map_cons, originalWord, Edge.decode_encode]
        exact ih
  have restore (word : List (Fin transitions)) :
      originalWord (embedWord (places := places) word) = word := by
    induction word with
    | nil => rfl
    | cons edge rest ih =>
        simp only [embedWord, List.map_cons, originalWord, Edge.decode_encode]
        exact congrArg (List.cons edge) ih
  simp only [encodeWord, originalWord_append, discardFill, discardDrain, restore,
    originalWord, Edge.decode_encode, List.nil_append, List.append_nil]

theorem encodeWord_execution (witness : Witness query) :
    query.compiled.Execution query.initial (query.encodeWord witness) query.final := by
  have initialized := query.fill_execution (visits query.source witness.before) (fixedValues query.source)
  rw [fixedValues_add_visits witness.source_matches] at initialized
  have drained := query.drain_execution (visits query.target witness.after) (fixedValues query.target)
  rw [fixedValues_add_visits witness.target_matches] at drained
  exact ((((initialized.append (query.enter_execution witness.before)).append
    (query.original_execution witness.execution)).append
    (query.leave_execution witness.after)).append drained).compile

end Query

end Thesis.Causality.PetriExactEndpoints
