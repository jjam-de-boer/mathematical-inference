import Thesis.Causality.BinaryIntegerCarry

namespace Thesis.Causality.IntegerEquations

open Probability

/-!
# Exact natural-number feasibility of signed linear equations

For arbitrary finite integer data A and b, `System.solve` returns either
an actual natural vector x with A*x = b, or a proof that no such vector
exists. Its search bound is derived from the finite signed-carry graph;
there is no assumed bound on x, its denominator, or its binary length.

The carry graph has (2*M+1)^rows states, where M is the computed sum of
the row absolute-coefficient and right-hand-side budgets. Every binary
digit column is enumerated explicitly. A materialized finite path table
retains the accepted word, so a successful witness is computed rather
than extracted from a propositional existence theorem by choice.

This deliberately simple exact core can be expensive: termination is a
mathematical guarantee, not a practical polynomial-time claim. It decides
equations over natural unknowns, not Petri execution order, coordinate
boundedness, pumping, or rational polynomial feasibility.
-/

variable {rows variables : Nat}

/-- Stored vectors have a two-sided finite presentation. Empty row
families give one empty carry, even when there are no variables either. -/
def System.carryWitness (system : System rows variables) : FiniteWitness system.Carry :=
  FiniteWitness.vector rows (List.finRange (2 * system.budget + 1)) List.mem_finRange

def digits (variables : Nat) : List (Digit variables) :=
  vectorEnumeration variables (List.finRange 2)

theorem mem_digits (digit : Digit variables) : digit ∈ digits variables :=
  mem_vectorEnumeration variables (List.finRange 2) List.mem_finRange digit

/-- Both branches carry their mathematical justification. The feasible
branch additionally retains the actual computed natural vector as data. -/
inductive Result (system : System rows variables) where
  | feasible (values : Fin variables → Nat) (valid : system.Satisfies values)
  | infeasible (missing : ¬ ∃ values, system.Satisfies values)

/-- A total, witness-producing decision procedure, with no user cutoff.
The completeness direction encodes any proposed solution as a word, then
uses finite-graph path shortening to justify the table's finite depth. -/
def System.solve (system : System rows variables) : Result system :=
  match FiniteLabelledReachability.solve system.carryWitness (digits variables)
      system.advance system.initialCarry system.zeroCarry with
  | .found word accepted => .feasible (decodeWord word) (system.run_satisfies accepted)
  | .unreachable missing => .infeasible (by
      rintro ⟨values, valid⟩
      apply missing
      exact FiniteLabelledReachability.reachable_of_run system.carryWitness (digits variables)
        system.advance mem_digits (system.satisfies_run values valid))

def System.isFeasible (system : System rows variables) : Bool :=
  match system.solve with
  | .feasible _ _ => true
  | .infeasible _ => false

/-- The Boolean interface is exact for all natural vectors, not only for
vectors below a supplied or experimentally observed bound. -/
theorem System.isFeasible_exact (system : System rows variables) :
    system.isFeasible = true ↔ ∃ values, system.Satisfies values := by
  unfold isFeasible
  cases system.solve with
  | feasible values valid =>
      constructor
      · intro _
        exact ⟨values, valid⟩
      · intro _
        rfl
  | infeasible missing =>
      constructor
      · intro impossible
        cases impossible
      · intro witness
        exact False.elim (missing witness)

theorem System.isFeasible_false_exact (system : System rows variables) :
    system.isFeasible = false ↔ ¬ ∃ values, system.Satisfies values := by
  cases result : system.isFeasible with
  | false =>
      constructor
      · intro _ witness
        have accepted := system.isFeasible_exact.mpr witness
        rw [result] at accepted
        cases accepted
      · intro _
        rfl
  | true =>
      constructor
      · intro impossible
        cases impossible
      · intro missing
        exact False.elim (missing (system.isFeasible_exact.mp result))

/-- Explicit finite-data decidability. This is not a classical decision
instance for arbitrary propositions: both alternatives are computed by
the carry procedure for the supplied equation system. -/
def System.decideSolvable (system : System rows variables) : Decidable (∃ values, system.Satisfies values) :=
  match system.solve with
  | .feasible values valid => isTrue ⟨values, valid⟩
  | .infeasible missing => isFalse missing

end Thesis.Causality.IntegerEquations
