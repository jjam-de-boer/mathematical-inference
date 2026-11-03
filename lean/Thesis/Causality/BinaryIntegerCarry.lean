import Thesis.Causality.IntegerEquations
import Thesis.Causality.FiniteLabelledReachability
import Thesis.Probability.FiniteVectorWitness

namespace Thesis.Causality.IntegerEquations

open Probability

/-!
# A finite signed-carry graph for natural solutions of integer equations

Digits are read least significant first. A carry c and a binary column d
permit the next carry (c - A*d)/2 only when every residual is even. Carries
are represented by stored finite coordinates in the interval determined by
the equation's computed coefficient budget. The quotient stays in that
interval; no candidate solution is rejected by a supplied numerical cutoff.

The one-step row identity proves that every word ending at zero decodes to
a solution. Conversely, every supplied natural solution gives a finite word
ending at zero. The encoding proof may pad high zero digits; its fuel depends
on that supplied solution and is not the solver's search bound. Finite-graph
reachability later replaces this arbitrary witness length by a proved finite
carrier bound. No Petri firing order, boundedness classifier or pumping test
is asserted here.
-/

variable {rows variables : Nat}

abbrev Digit (variables : Nat) := Vector (Fin 2) variables

def digitValues (digit : Digit variables) : Fin variables → Nat := fun index => (digit[index]).val

def lowDigit (values : Fin variables → Nat) : Digit variables :=
  vectorOfFn (fun index => ⟨values index % 2, Nat.mod_lt _ (by decide)⟩)

theorem digitValues_lowDigit (values : Fin variables → Nat) :
    digitValues (lowDigit values) = (fun index => values index % 2) := by
  funext index
  simp only [digitValues, lowDigit, Fin.getElem_fin, getElem_vectorOfFn]

def decodeWord : List (Digit variables) → Fin variables → Nat
  | [] => fun _ => 0
  | digit :: rest => fun index => digitValues digit index + 2 * decodeWord rest index

def binaryWord : Nat → (Fin variables → Nat) → List (Digit variables)
  | 0, _ => []
  | fuel + 1, values => lowDigit values :: binaryWord fuel (fun index => values index / 2)

abbrev System.Carry (system : System rows variables) := Vector (Fin (2 * system.budget + 1)) rows

def System.carryValue (system : System rows variables) (carry : system.Carry) (row : Fin rows) : Int :=
  ((carry[row]).val : Int) - (system.budget : Int)

theorem System.carry_bounds (system : System rows variables) (carry : system.Carry) (row : Fin rows) :
    -(system.budget : Int) ≤ system.carryValue carry row ∧ system.carryValue carry row ≤ system.budget := by
  have bound := (carry[row]).isLt
  unfold carryValue
  constructor <;> omega

/-- Translate a proved bounded integer vector into stored finite codes.
The proof does not select coordinates or invent a default carry. -/
def System.packCarry (system : System rows variables) (values : Fin rows → Int)
    (bounded : ∀ row, -(system.budget : Int) ≤ values row ∧ values row ≤ system.budget) : system.Carry :=
  vectorOfFn (fun row => ⟨(values row + (system.budget : Int)).toNat, by
    have range := bounded row
    omega⟩)

theorem System.carryValue_pack (system : System rows variables) (values : Fin rows → Int)
    (bounded : ∀ row, -(system.budget : Int) ≤ values row ∧ values row ≤ system.budget) (row : Fin rows) :
    system.carryValue (system.packCarry values bounded) row = values row := by
  simp only [carryValue, packCarry, Fin.getElem_fin, getElem_vectorOfFn, Fin.eta]
  have range := bounded row
  omega

theorem System.carry_ext (system : System rows variables) (left right : system.Carry)
    (equal : ∀ row, system.carryValue left row = system.carryValue right row) : left = right := by
  apply Vector.ext
  intro index bounded
  apply Fin.ext
  have coordinate := equal ⟨index, bounded⟩
  simp only [carryValue, Fin.getElem_fin] at coordinate
  omega

def System.initialCarry (system : System rows variables) : system.Carry :=
  system.packCarry system.rhs (by
    intro row
    have absolute := coefficient_bounds (system.rhs row)
    have bound := system.rhs_abs_le_budget row
    constructor <;> omega)

theorem System.initialCarry_value (system : System rows variables) (row : Fin rows) :
    system.carryValue system.initialCarry row = system.rhs row := system.carryValue_pack _ _ row

def System.zeroCarry (system : System rows variables) : system.Carry :=
  system.packCarry (fun _ => 0) (fun _ => by
    change -(system.budget : Int) ≤ 0 ∧ (0 : Int) ≤ system.budget
    constructor <;> omega)

theorem System.zeroCarry_value (system : System rows variables) (row : Fin rows) :
    system.carryValue system.zeroCarry row = 0 := system.carryValue_pack _ _ row

/-- The quotient is bounded even before the parity gate. The transition
below still refuses odd residuals, whose quotients would round an equation. -/
def System.quotientCarry (system : System rows variables) (carry : system.Carry) (digit : Digit variables) : system.Carry :=
  system.packCarry (fun row => (system.carryValue carry row - rowValue (system.coefficients row) (digitValues digit)) / 2)
    (by
      intro row
      have before := system.carry_bounds carry row
      have contribution := digit_row_bounds (system.coefficients row) (fun index => digit[index])
      change -(rowWeight (system.coefficients row) : Int) ≤
        rowValue (system.coefficients row) (digitValues digit) ∧
        rowValue (system.coefficients row) (digitValues digit) ≤ rowWeight (system.coefficients row) at contribution
      have budget := system.rowWeight_le_budget row
      change -(system.budget : Int) ≤
          (system.carryValue carry row - rowValue (system.coefficients row) (digitValues digit)) / 2 ∧
        (system.carryValue carry row - rowValue (system.coefficients row) (digitValues digit)) / 2 ≤ (system.budget : Int)
      constructor <;> omega)

theorem System.quotientCarry_value (system : System rows variables) (carry : system.Carry)
    (digit : Digit variables) (row : Fin rows) :
    system.carryValue (system.quotientCarry carry digit) row =
      (system.carryValue carry row - rowValue (system.coefficients row) (digitValues digit)) / 2 :=
  system.carryValue_pack _ _ row

def System.evenDigit (system : System rows variables) (carry : system.Carry) (digit : Digit variables) : Bool :=
  (List.finRange rows).all (fun row =>
    decide ((system.carryValue carry row - rowValue (system.coefficients row) (digitValues digit)) % 2 = 0))

theorem System.evenDigit_exact (system : System rows variables) (carry : system.Carry) (digit : Digit variables) :
    system.evenDigit carry digit = true ↔
      ∀ row, (system.carryValue carry row - rowValue (system.coefficients row) (digitValues digit)) % 2 = 0 := by
  simp only [evenDigit, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro ready row
    exact ready row (List.mem_finRange row)
  · intro ready row _
    exact ready row

def System.advance (system : System rows variables) (carry : system.Carry) (digit : Digit variables) : Option system.Carry :=
  if system.evenDigit carry digit then some (system.quotientCarry carry digit) else none

/-- Every accepted transition retains the exact signed row equation;
in particular, integer division never rounds an odd residual into success. -/
theorem System.advance_sound (system : System rows variables) {before after : system.Carry}
    {digit : Digit variables} (advanced : system.advance before digit = some after) (row : Fin rows) :
    system.carryValue before row = rowValue (system.coefficients row) (digitValues digit) +
      2 * system.carryValue after row := by
  unfold advance at advanced
  split at advanced
  · next ready =>
      cases Option.some.inj advanced
      rw [quotientCarry_value]
      have exactDivision := (system.evenDigit_exact before digit).mp ready row
      omega
  · cases advanced

theorem System.lowDigit_even (system : System rows variables) (carry : system.Carry) (values : Fin variables → Nat)
    (atValue : ∀ row, system.carryValue carry row = rowValue (system.coefficients row) values) :
    system.evenDigit carry (lowDigit values) = true := by
  apply (system.evenDigit_exact carry _).mpr
  intro row
  rw [atValue row, digitValues_lowDigit]
  have binary := rowValue_binary (system.coefficients row) values
  omega

theorem System.quotient_lowDigit_value (system : System rows variables) (carry : system.Carry)
    (values : Fin variables → Nat) (atValue : ∀ row, system.carryValue carry row = rowValue (system.coefficients row) values)
    (row : Fin rows) : system.carryValue (system.quotientCarry carry (lowDigit values)) row =
      rowValue (system.coefficients row) (fun index => values index / 2) := by
  rw [quotientCarry_value, atValue row, digitValues_lowDigit]
  have binary := rowValue_binary (system.coefficients row) values
  omega

theorem System.run_to_zero_sound (system : System rows variables) {carry : system.Carry} {word : List (Digit variables)}
    (accepted : FiniteLabelledReachability.run system.advance carry word = some system.zeroCarry) :
    ∀ row, rowValue (system.coefficients row) (decodeWord word) = system.carryValue carry row := by
  induction word generalizing carry with
  | nil =>
      cases Option.some.inj accepted
      intro row
      rw [decodeWord, rowValue_zero, zeroCarry_value]
  | cons digit rest ih =>
      rcases Option.bind_eq_some_iff.mp accepted with ⟨next, advanced, remaining⟩
      intro row
      have first := system.advance_sound advanced row
      have tail := ih remaining row
      simp only [decodeWord, rowValue_add, rowValue_scale]
      rw [tail]
      exact first.symm

/-- Encode any already supplied solution. The arithmetic decrease of
halving natural values is proved, rather than assumed as a termination bound. -/
theorem System.binaryWord_run (system : System rows variables) (fuel : Nat) (values : Fin variables → Nat)
    (carry : system.Carry) (small : ∀ index, values index ≤ fuel)
    (atValue : ∀ row, system.carryValue carry row = rowValue (system.coefficients row) values) :
    FiniteLabelledReachability.run system.advance carry (binaryWord fuel values) = some system.zeroCarry := by
  induction fuel generalizing values carry with
  | zero =>
      have allZero : values = (fun _ => 0) := by
        funext index
        exact Nat.eq_zero_of_le_zero (small index)
      have zero : carry = system.zeroCarry := by
        apply system.carry_ext
        intro row
        rw [atValue row, allZero, rowValue_zero, zeroCarry_value]
      cases zero
      rfl
  | succ fuel ih =>
      change (system.advance carry (lowDigit values)).bind _ = _
      rw [advance, system.lowDigit_even carry values atValue, if_pos rfl, Option.bind_some]
      apply ih (fun index => values index / 2) (system.quotientCarry carry (lowDigit values))
      · intro index
        have before := small index
        omega
      · exact system.quotient_lowDigit_value carry values atValue

theorem System.satisfies_run (system : System rows variables) (values : Fin variables → Nat)
    (valid : system.Satisfies values) :
    FiniteLabelledReachability.run system.advance system.initialCarry (binaryWord (encodingFuel values) values) =
      some system.zeroCarry :=
  system.binaryWord_run _ values system.initialCarry (le_encodingFuel values)
    (fun row => (system.initialCarry_value row).trans (valid row).symm)

theorem System.run_satisfies (system : System rows variables) {word : List (Digit variables)}
    (accepted : FiniteLabelledReachability.run system.advance system.initialCarry word = some system.zeroCarry) :
    system.Satisfies (decodeWord word) :=
  fun row => (system.run_to_zero_sound accepted row).trans (system.initialCarry_value row)

end Thesis.Causality.IntegerEquations
