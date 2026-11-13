import Thesis.Probability.FiniteFunctionTables

namespace Thesis.Probability.Examples.FiniteFunctionTables

/-!
# Empty rows, vacuous inputs and complete finite truth tables

These deliberately tiny kernel checks exercise the boundaries needed by
native roots: an absent parent has one vacuous proof-function slot, even if
its unused value type is empty. Tables with no rows also have one empty table;
an inhabited row domain and empty output type instead give no tables. The
all-function theorem is symbolic and does not rely on these numerical tests.
-/

def codeWitness (card : Nat) : FiniteWitness (Fin card) :=
  ⟨card, id, id, fun _ => rfl, fun _ => rfl⟩

theorem absent_parent_has_one_choice :
    (ProofFunction.enumeration False ([] : List (Fin 0))).length = 1 := rfl

theorem present_empty_parent_has_no_choices :
    (ProofFunction.enumeration True ([] : List (Fin 0))).length = 0 := rfl

theorem empty_row_empty_output_has_one_table :
    (FiniteFunctionTable.enumeration (codeWitness 0) ([] : List Bool)).length = 1 := rfl

theorem inhabited_row_empty_output_has_no_table :
    (FiniteFunctionTable.enumeration (codeWitness 1) ([] : List Bool)).length = 0 := rfl

theorem two_boolean_rows_have_four_tables :
    (FiniteFunctionTable.enumeration (codeWitness 2) [false, true]).length = 4 := by decide +kernel

theorem every_boolean_function_listed (function : Fin 2 → Bool) :
    FiniteFunctionTable.tabulate (codeWitness 2) function ∈
      FiniteFunctionTable.enumeration (codeWitness 2) [false, true] :=
  FiniteFunctionTable.tabulation_mem_enumeration _ _ (fun value => by cases value <;> simp) function

theorem every_boolean_function_recovered (function : Fin 2 → Bool) :
    FiniteFunctionTable.lookup (codeWitness 2) (FiniteFunctionTable.tabulate (codeWitness 2) function) = function :=
  FiniteFunctionTable.lookup_tabulate _ function

end Thesis.Probability.Examples.FiniteFunctionTables
