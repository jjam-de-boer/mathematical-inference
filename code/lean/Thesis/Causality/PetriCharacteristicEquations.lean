import Thesis.Causality.PetriExecutionCounts
import Thesis.Causality.PetriWordCompletion

namespace Thesis.Causality.PetriCharacteristic

open PetriNet PetriExecutionCounts IntegerEquations Probability.IntegerLinearAlgebra

/-!
# Characteristic equations of a sequence of Petri segments

Each segment admits a supplied subset of literal edges between a fixed
pair of control states. It has exact requirements on any specified
entry and exit counters. A designated edge joins each consecutive pair.
The characteristic equations remember the multiplicities of the interior
edges, their signed counter effect and their flow at every control state.

Joining edges are single actual firings. Their control states are checked
and a shared nonnegative surplus retains both the consumption guard and
the exact counter change. A fixed endpoint coordinate is substituted as
a constant, and a forbidden edge has count zero without a solver column.
Interior counts forget firing order; the model of the equations alone
does not assert an enabled run.
-/

variable {places states transitions links : Nat}

structure Segment (places states transitions : Nat) where
  entry : Fin states
  exit : Fin states
  source : PartialMarking places
  target : PartialMarking places
  allowed : Fin transitions → Bool

structure Sequence (places states transitions links : Nat) where
  net : ControlledPetriNet places states transitions
  segment : Fin (links + 1) → Segment places states transitions
  bridge : Fin links → Fin transitions

/-- A single segment uses the same equations with no joining transitions. -/
def oneSegment (net : ControlledPetriNet places states transitions)
    (segment : Segment places states transitions) : Sequence places states transitions 0 :=
  ⟨net, fun _ => segment, Fin.elim0⟩

inductive Unknown (places transitions links : Nat) where
  | entry (segment : Fin (links + 1)) (place : Fin places)
  | exit (segment : Fin (links + 1)) (place : Fin places)
  | count (segment : Fin (links + 1)) (edge : Fin transitions)
  | surplus (link : Fin links) (place : Fin places)
  deriving DecidableEq

abbrev Assignment (places transitions links : Nat) :=
  Unknown places transitions links → Nat

namespace Sequence

variable (sequence : Sequence places states transitions links)

def before (values : Assignment places transitions links) (i : Fin (links + 1)) : Marking places :=
  fun place => ((sequence.segment i).source place).getD (values (.entry i place))

def after (values : Assignment places transitions links) (i : Fin (links + 1)) : Marking places :=
  fun place => ((sequence.segment i).target place).getD (values (.exit i place))

def counts (values : Assignment places transitions links) (i : Fin (links + 1)) :
    Fin transitions → Nat :=
  fun edge => if (sequence.segment i).allowed edge then values (.count i edge) else 0

structure Model (values : Assignment places transitions links) : Prop where
  tokens : ∀ i place, rowValue (tokenChange sequence.net.net place) (sequence.counts values i) =
    (sequence.after values i place : Int) - (sequence.before values i place : Int)
  flow : ∀ i state, rowValue (controlChange sequence.net state) (sequence.counts values i) =
    indicator state (sequence.segment i).exit - indicator state (sequence.segment i).entry
  bridgeStates : ∀ j, (sequence.segment j.castSucc).exit = sequence.net.source (sequence.bridge j) ∧
    (sequence.segment j.succ).entry = sequence.net.target (sequence.bridge j)
  bridgeBefore : ∀ j place, sequence.after values j.castSucc place =
    sequence.net.net.consume (sequence.bridge j) place + values (.surplus j place)
  bridgeAfter : ∀ j place, sequence.before values j.succ place =
    sequence.net.net.produce (sequence.bridge j) place + values (.surplus j place)

/-- Unlike the interior counts, a link in a model has full firing
semantics. Using only its signed displacement would lose the guard. -/
theorem Model.bridgeFires {values : Assignment places transitions links}
    (model : sequence.Model values) (j : Fin links) :
    sequence.net.Fires (sequence.segment j.castSucc).exit (sequence.after values j.castSucc)
      (sequence.bridge j) (sequence.segment j.succ).entry (sequence.before values j.succ) := by
  refine ⟨(model.bridgeStates j).1, (model.bridgeStates j).2, ?_, ?_⟩
  · intro place
    change sequence.net.net.consume (sequence.bridge j) place ≤ sequence.after values j.castSucc place
    rw [model.bridgeBefore j place]
    exact Nat.le_add_right _ _
  · funext place
    have before := model.bridgeBefore j place
    have after := model.bridgeAfter j place
    omega

private abbrev Key := Unknown places transitions links

private structure Expression (α : Type) where
  terms : List (α × Int)
  constant : Int

private def Expression.value (expression : Expression α) (values : α → Nat) : Int :=
  (NamedRow.mk expression.terms 0).value values + expression.constant

private def Expression.plus (first second : Expression α) : Expression α :=
  ⟨first.terms ++ second.terms, first.constant + second.constant⟩

private theorem Expression.plus_value (first second : Expression α) (values : α → Nat) :
    (first.plus second).value values = first.value values + second.value values := by
  simp only [Expression.plus, Expression.value, NamedRow.value, List.map_append, sum_append]
  omega

private def Expression.zeroRow (expression : Expression α) : NamedRow α :=
  ⟨expression.terms, -expression.constant⟩

private theorem Expression.zeroRow_exact (expression : Expression α) (values : α → Nat) :
    expression.zeroRow.value values = expression.zeroRow.rhs ↔ expression.value values = 0 := by
  simp only [Expression.zeroRow, Expression.value, NamedRow.value]
  constructor <;> intro equal <;> omega

private def endpoint (fixed : Option Nat) (key : α) (weight : Int) : Expression α :=
  match fixed with
  | some value => ⟨[], weight * (value : Int)⟩
  | none => ⟨[(key, weight)], 0⟩

private theorem endpoint_value (fixed : Option Nat) (key : α) (weight : Int) (values : α → Nat) :
    (endpoint fixed key weight).value values = weight * (fixed.getD (values key) : Int) := by
  cases fixed
  · simp only [endpoint, Expression.value, NamedRow.value, List.map_cons, List.map_nil,
      sum_singleton, Int.add_zero, Option.getD_none]
  · change 0 + _ = _
    exact Int.zero_add _

private def edgeTerms (i : Fin (links + 1)) (weight : Fin transitions → Int) :
    List (Key (places := places) (transitions := transitions) (links := links) × Int) :=
  ((List.finRange transitions).filter (sequence.segment i).allowed).map
    (fun edge => (.count i edge, weight edge))

private theorem filtered_count_sum (indices : List (Fin transitions))
    (allowed : Fin transitions → Bool) (weight : Fin transitions → Int)
    (values : Fin transitions → Nat) :
    sum ((indices.filter allowed).map (fun edge => weight edge * (values edge : Int))) =
      sum (indices.map (fun edge => weight edge * (if allowed edge then (values edge : Int) else 0))) := by
  induction indices with
  | nil => rfl
  | cons edge rest ih =>
      cases admitted : allowed edge <;>
        simp only [List.filter_cons, admitted, Bool.false_eq_true, if_true, if_false,
          List.map_cons, Int.mul_zero]
      · change _ = 0 + _
        rw [Int.zero_add]
        exact ih
      · change _ + _ = _ + _
        exact congrArg (fun tail => weight edge * (values edge : Int) + tail) ih

private theorem edgeTerms_value (i : Fin (links + 1)) (weight : Fin transitions → Int)
    (values : Assignment places transitions links) :
    (NamedRow.mk (sequence.edgeTerms i weight) 0).value values =
      rowValue weight (sequence.counts values i) := by
  simp only [NamedRow.value, edgeTerms, List.map_map, Function.comp_def, rowValue]
  rw [filtered_count_sum (List.finRange transitions) (sequence.segment i).allowed weight
    (fun edge => values (.count i edge))]
  congr 1
  apply List.map_congr_left
  intro edge _
  cases admitted : (sequence.segment i).allowed edge <;>
    simp only [counts, admitted, Bool.false_eq_true, if_false, if_true, Int.natCast_zero]

private def tokenRow (i : Fin (links + 1)) (place : Fin places) :
    NamedRow (Key (places := places) (transitions := transitions) (links := links)) :=
  let effect : Expression _ := ⟨sequence.edgeTerms i (tokenChange sequence.net.net place), 0⟩
  let entry := endpoint ((sequence.segment i).source place) (.entry i place) 1
  let exit := endpoint ((sequence.segment i).target place) (.exit i place) (-1)
  (effect.plus (entry.plus exit)).zeroRow

private def flowRow (i : Fin (links + 1)) (state : Fin states) :
    NamedRow (Key (places := places) (transitions := transitions) (links := links)) :=
  ⟨sequence.edgeTerms i (controlChange sequence.net state),
    indicator state (sequence.segment i).exit - indicator state (sequence.segment i).entry⟩

private def bridgeStateRow (j : Fin links) :
    NamedRow (Key (places := places) (transitions := transitions) (links := links)) :=
  ⟨[], if (sequence.segment j.castSucc).exit = sequence.net.source (sequence.bridge j) ∧
      (sequence.segment j.succ).entry = sequence.net.target (sequence.bridge j) then 0 else 1⟩

private def bridgeCounterRow (fixed : Option Nat)
    (marking slack : Key (places := places) (transitions := transitions) (links := links)) (arc : Nat) :
    NamedRow (Key (places := places) (transitions := transitions) (links := links)) :=
  ((endpoint fixed marking 1).plus ⟨[(slack, -1)], -(arc : Int)⟩).zeroRow

private def bridgeBeforeRow (j : Fin links) (place : Fin places) :
    NamedRow (Unknown places transitions links) :=
  bridgeCounterRow ((sequence.segment j.castSucc).target place) (.exit j.castSucc place)
    (.surplus j place) (sequence.net.net.consume (sequence.bridge j) place)

private def bridgeAfterRow (j : Fin links) (place : Fin places) :
    NamedRow (Unknown places transitions links) :=
  bridgeCounterRow ((sequence.segment j.succ).source place) (.entry j.succ place)
    (.surplus j place) (sequence.net.net.produce (sequence.bridge j) place)

def rows : List (NamedRow (Unknown places transitions links)) :=
  ((List.finRange (links + 1)).flatMap fun i =>
    (List.finRange places).map (sequence.tokenRow i) ++ (List.finRange states).map (sequence.flowRow i)) ++
  ((List.finRange links).flatMap fun j => sequence.bridgeStateRow j ::
    ((List.finRange places).map (sequence.bridgeBeforeRow j) ++
      (List.finRange places).map (sequence.bridgeAfterRow j)))

private theorem tokenRow_exact (values : Assignment places transitions links)
    (i : Fin (links + 1)) (place : Fin places) :
    (sequence.tokenRow i place).value values = (sequence.tokenRow i place).rhs ↔
      rowValue (tokenChange sequence.net.net place) (sequence.counts values i) =
        (sequence.after values i place : Int) - (sequence.before values i place : Int) := by
  unfold tokenRow
  rw [Expression.zeroRow_exact, Expression.plus_value, Expression.plus_value, endpoint_value, endpoint_value]
  change (NamedRow.mk (sequence.edgeTerms i _) 0).value values + 0 +
    (1 * (sequence.before values i place : Int) + (-1) * (sequence.after values i place : Int)) = 0 ↔ _
  rw [sequence.edgeTerms_value]
  constructor <;> intro equal <;> omega

private theorem flowRow_exact (values : Assignment places transitions links)
    (i : Fin (links + 1)) (state : Fin states) :
    (sequence.flowRow i state).value values = (sequence.flowRow i state).rhs ↔
      rowValue (controlChange sequence.net state) (sequence.counts values i) =
        indicator state (sequence.segment i).exit - indicator state (sequence.segment i).entry := by
  change (NamedRow.mk (sequence.edgeTerms i _) 0).value values = _ ↔ _
  rw [sequence.edgeTerms_value]
  rfl

private theorem bridgeStateRow_exact (values : Assignment places transitions links) (j : Fin links) :
    (sequence.bridgeStateRow j).value values = (sequence.bridgeStateRow j).rhs ↔
      (sequence.segment j.castSucc).exit = sequence.net.source (sequence.bridge j) ∧
        (sequence.segment j.succ).entry = sequence.net.target (sequence.bridge j) := by
  change 0 = (if _ ∧ _ then (0 : Int) else 1) ↔ _
  split
  · rename_i atStates
    exact ⟨fun _ => atStates, fun _ => rfl⟩
  · rename_i wrong
    exact ⟨fun equal => False.elim (by omega), fun states => False.elim (wrong states)⟩

private theorem bridgeCounterRow_exact (values : Assignment places transitions links)
    (fixed : Option Nat) (marking slack : Key (places := places) (transitions := transitions)
      (links := links)) (arc : Nat) :
    (bridgeCounterRow fixed marking slack arc).value values =
      (bridgeCounterRow fixed marking slack arc).rhs ↔
        fixed.getD (values marking) = arc + values slack := by
  unfold bridgeCounterRow
  rw [Expression.zeroRow_exact, Expression.plus_value, endpoint_value]
  change 1 * (fixed.getD (values marking) : Int) +
    (sum [(-1) * (values slack : Int)] + -(arc : Int)) = 0 ↔ _
  rw [sum_singleton]
  constructor <;> intro equal <;> omega

/-- Every named constraint is exactly one of the balances or the two
halves of an actual bridge. The row proof is separate from the arithmetic
overapproximation of enabled interior executions. -/
theorem rows_exact (values : Assignment places transitions links) :
    NamedRow.Satisfies sequence.rows values ↔ sequence.Model values := by
  constructor
  · intro satisfies
    have inside (i : Fin (links + 1)) {row : NamedRow _}
        (member : row ∈ (List.finRange places).map (sequence.tokenRow i) ++
            (List.finRange states).map (sequence.flowRow i)) : row.value values = row.rhs :=
      satisfies row (List.mem_append_left _ (List.mem_flatMap_of_mem (List.mem_finRange i) member))
    have joins (j : Fin links) {row : NamedRow _}
        (member : row ∈ sequence.bridgeStateRow j ::
          ((List.finRange places).map (sequence.bridgeBeforeRow j) ++
            (List.finRange places).map (sequence.bridgeAfterRow j))) : row.value values = row.rhs :=
      satisfies row (List.mem_append_right _ (List.mem_flatMap_of_mem (List.mem_finRange j) member))
    constructor
    · intro i place
      exact (sequence.tokenRow_exact values i place).mp
        (inside i (List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange place))))
    · intro i state
      exact (sequence.flowRow_exact values i state).mp
        (inside i (List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange state))))
    · intro j
      exact (sequence.bridgeStateRow_exact values j).mp (joins j (List.Mem.head _))
    · intro j place
      exact (bridgeCounterRow_exact values _ _ _ _).mp (joins j (List.Mem.tail _
        (List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange place)))))
    · intro j place
      exact (bridgeCounterRow_exact values _ _ _ _).mp (joins j (List.Mem.tail _
        (List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange place)))))
  · intro model row member
    rcases List.mem_append.mp member with inside | joining
    · obtain ⟨i, _, rowsInSegment⟩ := List.mem_flatMap.mp inside
      rcases List.mem_append.mp rowsInSegment with token | flow
      · obtain ⟨place, _, rfl⟩ := List.mem_map.mp token
        exact (sequence.tokenRow_exact values i place).mpr (model.tokens i place)
      · obtain ⟨state, _, rfl⟩ := List.mem_map.mp flow
        exact (sequence.flowRow_exact values i state).mpr (model.flow i state)
    · obtain ⟨j, _, atBridge⟩ := List.mem_flatMap.mp joining
      rcases List.mem_cons.mp atBridge with rfl | counters
      · exact (sequence.bridgeStateRow_exact values j).mpr (model.bridgeStates j)
      · rcases List.mem_append.mp counters with input | output
        · obtain ⟨place, _, rfl⟩ := List.mem_map.mp input
          exact (bridgeCounterRow_exact values _ _ _ _).mpr (model.bridgeBefore j place)
        · obtain ⟨place, _, rfl⟩ := List.mem_map.mp output
          exact (bridgeCounterRow_exact values _ _ _ _).mpr (model.bridgeAfter j place)

abbrev columnCount := (NamedRow.columns sequence.rows).length

def system := NamedRow.system sequence.rows

/-- Every allowed count can be passed to the integer coordinate
classifier, including counts with zero displacement and zero flow. -/
theorem count_column (i : Fin (links + 1)) (edge : Fin transitions)
    (admitted : (sequence.segment i).allowed edge = true) :
    ∃ index, NamedRow.columnIndex sequence.rows (.count i edge) = some index := by
  let state := (sequence.segment i).entry
  have inRows : sequence.flowRow i state ∈ sequence.rows :=
    List.mem_append_left _ (List.mem_flatMap_of_mem (List.mem_finRange i)
      (List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange state))))
  have inTerms : (Unknown.count i edge, controlChange sequence.net state edge) ∈
      (sequence.flowRow i state).terms :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange edge, admitted⟩)
  obtain ⟨index, located, _⟩ := NamedRow.columnIndex_of_mem sequence.rows
    (NamedRow.mem_columns inRows inTerms)
  exact ⟨index, located⟩

def decode (values : Fin sequence.columnCount → Nat) : Assignment places transitions links :=
  NamedRow.decode sequence.rows values

theorem system_exact (values : Fin sequence.columnCount → Nat) :
    sequence.system.Satisfies values ↔ sequence.Model (sequence.decode values) :=
  (NamedRow.system_exact sequence.rows values).trans (sequence.rows_exact _)

end Sequence
end Thesis.Causality.PetriCharacteristic
