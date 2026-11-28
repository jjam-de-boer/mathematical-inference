import Thesis.Causality.IntegerCoordinateClassification
import Thesis.Causality.PetriCharacteristicEquations
import Thesis.Causality.PetriExactEndpointReduction

namespace Thesis.Causality.PetriCharacteristic

open PetriNet PetriExecutionCounts IntegerEquations

/-!
# Sound arithmetic analysis of segmented Petri executions

An actual run supplies its concrete endpoints, the count of each literal
edge in each segment and the leftover tokens at every bridge. This gives
a solution of the characteristic equations without choosing any data out
of a proposition. Arithmetic infeasibility refutes every actual run, and
arithmetic bounds on a named variable apply to the corresponding datum of
every run. An arithmetic solution (even an unbounded family of solutions)
need not be realized by enabled interior words.
-/

variable {places states transitions links : Nat}

namespace Sequence

variable (sequence : Sequence places states transitions links)

structure Run where
  before : Fin (links + 1) → Marking places
  after : Fin (links + 1) → Marking places
  word : Fin (links + 1) → List (Fin transitions)
  source_matches : ∀ i, (sequence.segment i).source.Matches (before i)
  target_matches : ∀ i, (sequence.segment i).target.Matches (after i)
  execution : ∀ i, sequence.net.Execution (sequence.segment i).entry (before i)
    (word i) (sequence.segment i).exit (after i)
  allowed : ∀ i edge, edge ∈ word i → (sequence.segment i).allowed edge = true
  bridgeFires : ∀ j, sequence.net.Fires (sequence.segment j.castSucc).exit (after j.castSucc)
    (sequence.bridge j) (sequence.segment j.succ).entry (before j.succ)

variable {sequence}

namespace Run

def assignment (run : sequence.Run) : Assignment places transitions links
  | .entry i place => run.before i place
  | .exit i place => run.after i place
  | .count i edge => occurrences (run.word i) edge
  | .surplus j place =>
      run.after j.castSucc place - sequence.net.net.consume (sequence.bridge j) place

private theorem before_eq (run : sequence.Run) (i : Fin (links + 1)) :
    sequence.before run.assignment i = run.before i := by
  funext place
  have fits := run.source_matches i place
  cases fixed : (sequence.segment i).source place with
  | none => simp only [Sequence.before, fixed, Option.getD_none, assignment]
  | some value =>
      rw [fixed] at fits
      simpa only [Sequence.before, fixed, Option.getD_some] using fits.symm

private theorem after_eq (run : sequence.Run) (i : Fin (links + 1)) :
    sequence.after run.assignment i = run.after i := by
  funext place
  have fits := run.target_matches i place
  cases fixed : (sequence.segment i).target place with
  | none => simp only [Sequence.after, fixed, Option.getD_none, assignment]
  | some value =>
      rw [fixed] at fits
      simpa only [Sequence.after, fixed, Option.getD_some] using fits.symm

private theorem counts_eq (run : sequence.Run) (i : Fin (links + 1)) :
    sequence.counts run.assignment i = occurrences (run.word i) := by
  funext edge
  cases admitted : (sequence.segment i).allowed edge with
  | true => simp only [Sequence.counts, assignment, admitted, if_true]
  | false =>
      have absent : edge ∉ run.word i := by
        intro member
        have allowed := run.allowed i edge member
        rw [admitted] at allowed
        cases allowed
      simp only [Sequence.counts, admitted, Bool.false_eq_true, if_false,
        occurrences_zero_of_not_mem _ _ absent]

theorem model (run : sequence.Run) : sequence.Model run.assignment := by
  constructor
  · intro i place
    rw [run.counts_eq, run.before_eq, run.after_eq]
    exact tokenBalance sequence.net.net (run.execution i).2 place
  · intro i state
    rw [run.counts_eq]
    exact controlBalance sequence.net (run.execution i).1 state
  · intro j
    exact ⟨(run.bridgeFires j).1, (run.bridgeFires j).2.1⟩
  · intro j place
    rw [run.after_eq]
    have enabled := (run.bridgeFires j).2.2.1 place
    change sequence.net.net.consume (sequence.bridge j) place ≤ run.after j.castSucc place at enabled
    change run.after j.castSucc place = sequence.net.net.consume (sequence.bridge j) place +
      (run.after j.castSucc place - sequence.net.net.consume (sequence.bridge j) place)
    omega
  · intro j place
    rw [run.before_eq]
    have actual := congrFun (run.bridgeFires j).2.2.2 place
    change run.before j.succ place = run.after j.castSucc place -
      sequence.net.net.consume (sequence.bridge j) place + sequence.net.net.produce (sequence.bridge j) place at actual
    change run.before j.succ place = sequence.net.net.produce (sequence.bridge j) place +
      (run.after j.castSucc place - sequence.net.net.consume (sequence.bridge j) place)
    omega

def values (run : sequence.Run) : Fin sequence.columnCount → Nat :=
  NamedRow.encode sequence.rows run.assignment

theorem satisfies (run : sequence.Run) : sequence.system.Satisfies run.values :=
  NamedRow.encode_satisfies ((sequence.rows_exact _).mpr run.model)

/-- A bound computed by the integer classifier transfers directly to the
named datum of an actual run. In particular, a count column gives a bound
on the number of occurrences of that precise edge in its segment. -/
theorem bound_of_column (run : sequence.Run) {name : Unknown places transitions links}
    {index : Fin sequence.columnCount} (located : NamedRow.columnIndex sequence.rows name = some index)
    {bound : Nat} (bounds : ∀ values, sequence.system.Satisfies values → values index < bound) :
    run.assignment name < bound := by
  have bounded := bounds run.values run.satisfies
  change run.assignment ((NamedRow.columns sequence.rows).get index) < bound at bounded
  rwa [NamedRow.columnIndex_get located] at bounded

end Run

theorem model_iff_feasible :
    (∃ assignment, sequence.Model assignment) ↔ ∃ values, sequence.system.Satisfies values := by
  constructor
  · rintro ⟨assignment, model⟩
    exact ⟨NamedRow.encode sequence.rows assignment,
      NamedRow.encode_satisfies ((sequence.rows_exact _).mpr model)⟩
  · rintro ⟨values, valid⟩
    exact ⟨sequence.decode values, (sequence.system_exact values).mp valid⟩

/-- This is only a test of the characteristic equations. A feasible
result retains actual arithmetic data and its checked model. -/
inductive Analysis (sequence : Sequence places states transitions links) where
  | feasible (assignment : Assignment places transitions links) (valid : sequence.Model assignment)
  | infeasible (missing : ¬ ∃ assignment, sequence.Model assignment)

def analyze (sequence : Sequence places states transitions links) : sequence.Analysis :=
  match sequence.system.solve with
  | .feasible values valid => .feasible (sequence.decode values) ((sequence.system_exact values).mp valid)
  | .infeasible missing =>
      .infeasible (fun model => missing ((model_iff_feasible (sequence := sequence)).mp model))

theorem noRun_of_infeasible (sequence : Sequence places states transitions links)
    (missing : ¬ ∃ assignment, sequence.Model assignment) : ¬ Nonempty sequence.Run := by
  rintro ⟨run⟩
  exact missing ⟨run.assignment, run.model⟩

end Sequence

/-- Begin refinement with one segment admitting every original edge. The
existing endpoint interface supplies the controlled system; ordinary nets
use its one-state wrapper. -/
def ofEndpointQuery (query : PetriExactEndpoints.Query places states transitions) :
    Sequence places states transitions 0 :=
  oneSegment query.system ⟨query.start, query.finish, query.source, query.target, fun _ => true⟩

theorem ofEndpointQuery_run_iff (query : PetriExactEndpoints.Query places states transitions) :
    Nonempty (ofEndpointQuery query).Run ↔ query.PartialReachable := by
  constructor
  · rintro ⟨run⟩
    exact ⟨run.before 0, run.after 0, run.source_matches 0, run.target_matches 0,
      run.word 0, run.execution 0⟩
  · rintro ⟨before, after, sourceFits, targetFits, word, execution⟩
    exact ⟨{
      before := fun _ => before
      after := fun _ => after
      word := fun _ => word
      source_matches := fun _ => sourceFits
      target_matches := fun _ => targetFits
      execution := fun _ => execution
      allowed := fun _ _ _ => rfl
      bridgeFires := fun j => Fin.elim0 j }⟩

end Thesis.Causality.PetriCharacteristic
