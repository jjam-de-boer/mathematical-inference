import Thesis.Probability.BooleanChannelTable
import Thesis.Probability.FiniteSignedProduct

namespace Thesis
namespace Probability
namespace BooleanChannelTable

/-!
# Complete finite expansion of actual Boolean channel-row numerators

`BooleanChannelTable.record` is an ordinary positive normalized record.
Its singleton numerator can also be written as capacity plus a finite sum
of amplitude-weighted parity characters.  The equality below relates those
integer terms to the actual natural atom mass, including coincident centres.

Expanding products of these row sums retains every simultaneous channel
selection and all interactions.  An intervened row has just one constant
choice, its actual forced-value indicator, and no hidden channel term.
Thus action cuts are respected by the same complete expansion, not added
later as a heuristic deletion of polynomial terms.

Only numerators are expanded.  The actual probability cells and their
positive denominators are retained on the left, so the expansion is not a
claim of normalized equality for unrelated denominator presentations.
SCM likelihood integration and graph-specific coefficient matching remain
separate semantic steps.
-/

variable {Channel : Type u}

/-- Exact integer presentation of the row's natural singleton numerator. -/
def cellNumerator (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) : Int :=
  (table.capacity : Int) + (table.channels.map fun channel =>
    (table.amplitude channel : Int) * FiniteProbRecord.characterSign (Bool.xor value (signals channel))).sum

private theorem centre_character (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) :
    (table.channels.map fun channel => (table.amplitude channel : Int) *
      FiniteProbRecord.characterSign (Bool.xor value (signals channel))).sum =
        (FiniteProbRecord.eventMass (table.centreAtoms signals) (FiniteProbRecord.singletonEvent value) : Int) -
        (FiniteProbRecord.eventMass (table.centreAtoms signals) (FiniteProbRecord.singletonEvent (!value)) : Int) := by
  have presentation :
      FiniteProbRecord.signedAtomMass (table.centreAtoms signals)
        (fun centre => FiniteProbRecord.characterSign (Bool.xor value centre)) =
      (table.channels.map fun channel => (table.amplitude channel : Int) *
        FiniteProbRecord.characterSign (Bool.xor value (signals channel))).sum := by
    simp only [centreAtoms, FiniteProbRecord.signedAtomMass, List.map_map, Function.comp_def]
  rw [← presentation]
  have same := FiniteProbRecord.signedAtomMass_congr (table.centreAtoms signals)
    (fun centre => FiniteProbRecord.characterSign (Bool.xor value centre))
    (fun centre => FiniteProbRecord.characterSign (FiniteProbRecord.singletonEvent (!value) centre))
    (fun centre => by cases value <;> cases centre <;> rfl)
  rw [same, FiniteProbRecord.signedAtomMass_character]
  have complement := FiniteProbRecord.eventMass_congr (table.centreAtoms signals)
    (fun centre => !(FiniteProbRecord.singletonEvent (!value) centre)) (FiniteProbRecord.singletonEvent value)
    (fun centre => by cases value <;> cases centre <;> rfl)
  rw [complement]

/-- Connect the full character sum to the numerator of the actual positive
record, without truncating a negative term or assuming a signed probability. -/
theorem record_num_cast (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) :
    (((table.record signals).probVal (FiniteProbRecord.singletonEvent value)).num : Int) =
      table.cellNumerator signals value := by
  change (FiniteProbRecord.eventMass (table.record signals).atoms (FiniteProbRecord.singletonEvent value) : Int) = _
  rw [table.record_singleton_mass signals value]
  unfold cellNumerator
  rw [centre_character]
  have partition := table.centre_mass_partition signals value
  simp only [capacity, Int.natCast_add, Int.natCast_mul]
  omega

/-- One local choice is either the fair capacity or one channel summand. -/
def expansionChoices (table : BooleanChannelTable Channel) : List (Option Channel) :=
  none :: table.channels.map some

/-- The background capacity or one amplitude-weighted parity character.
The list of choices determines which terms actually enter the local sum. -/
def expansionTerm (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) :
    Option Channel -> Int
  | none => table.capacity
  | some channel => (table.amplitude channel : Int) *
      FiniteProbRecord.characterSign (Bool.xor value (signals channel))

theorem expansionChoices_sum (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) :
    ((table.expansionChoices).map (table.expansionTerm signals value)).sum = table.cellNumerator signals value := by
  simp only [expansionChoices, List.map_cons, List.map_map, List.sum_cons,
    expansionTerm, cellNumerator, Function.comp_def]

/-- The actual row cell under an optional hard intervention. -/
def cellUnder (table : BooleanChannelTable Channel) (signals : Channel -> Bool)
    (target : Option Bool) (value : Bool) : QProb :=
  match target with
  | none => (table.record signals).probVal (FiniteProbRecord.singletonEvent value)
  | some fixed => if fixed = value then QProb.one else QProb.zero

/-- Free rows keep their full record denominator; forced rows use the
literal denominator one, also at a conflicting zero cell.  Consequently
the whole likelihood denominator does not depend on hidden signals. -/
theorem cellUnder_den (table : BooleanChannelTable Channel) (signals : Channel -> Bool)
    (target : Option Bool) (value : Bool) :
    (table.cellUnder signals target value).den =
      match target with
      | none => 2 * table.capacity
      | some _ => 1 := by
  cases target with
  | none => exact table.record_den signals
  | some fixed => cases fixed <;> cases value <;> rfl

/-- A forced row has only its indicator choice; no channel can be selected
at an intervened vertex in the complete product expansion. -/
def expansionChoicesUnder (table : BooleanChannelTable Channel) (target : Option Bool) : List (Option Channel) :=
  match target with
  | none => table.expansionChoices
  | some _ => [none]

/-- Unsupported channel choices at a forced row are also zero, making
the term function total outside its actual enumeration. -/
def expansionTermUnder (table : BooleanChannelTable Channel) (signals : Channel -> Bool)
    (target : Option Bool) (value : Bool) (choice : Option Channel) : Int :=
  match target with
  | none => table.expansionTerm signals value choice
  | some fixed =>
      match choice with
      | none => if fixed = value then 1 else 0
      | some _ => 0

/-- Hidden-input-independent coefficient of one row-choice term.  A
forced row retains its consistency indicator only at the background choice;
every forced channel coefficient is zero even outside the actual list. -/
def expansionCoefficientUnder (table : BooleanChannelTable Channel)
    (target : Option Bool) (value : Bool) (choice : Option Channel) : Int :=
  match target with
  | none => match choice with | none => table.capacity | some channel => table.amplitude channel
  | some fixed => match choice with | none => if fixed = value then 1 else 0 | some _ => 0

/-- Factor a complete local term into its scalar coefficient and one
character, retaining zero coefficients at invalid forced channel choices.
This total identity precedes any grouping or connected-channel cancellation. -/
theorem expansionTermUnder_eq_coefficient_mul (table : BooleanChannelTable Channel)
    (signals : Channel -> Bool) (target : Option Bool) (value : Bool) (choice : Option Channel) :
    table.expansionTermUnder signals target value choice =
      table.expansionCoefficientUnder target value choice *
        (match choice with | none => 1 | some channel => FiniteProbRecord.characterSign (Bool.xor value (signals channel))) := by
  cases target with
  | none => cases choice <;> simp only [expansionTermUnder, expansionTerm, expansionCoefficientUnder, Int.mul_one]
  | some fixed => cases choice <;> simp only [expansionTermUnder, expansionCoefficientUnder, Int.mul_one, Int.zero_mul]

/-- Each complete local sum is exactly the actual cell's natural numerator,
including both a matching and a conflicting forced assignment. -/
theorem expansionChoicesUnder_sum (table : BooleanChannelTable Channel) (signals : Channel -> Bool)
    (target : Option Bool) (value : Bool) :
    ((table.expansionChoicesUnder target).map (table.expansionTermUnder signals target value)).sum =
      ((table.cellUnder signals target value).num : Int) := by
  cases target with
  | none => exact (table.expansionChoices_sum signals value).trans (table.record_num_cast signals value).symm
  | some fixed => cases fixed <;> cases value <;> rfl

/-- Full expansion of the actual row-factor product for any intervention.
All dependent channel types and repeated local terms are retained.  The left
side is the existing rational product's actual numerator, embedded in Int. -/
theorem product_num_expansion (n : Nat) (Channel : Fin n -> Type u)
    (tables : (index : Fin n) -> BooleanChannelTable (Channel index))
    (signals : (index : Fin n) -> Channel index -> Bool)
    (target : Fin n -> Option Bool) (sample : Fin n -> Bool) :
    ((FiniteProduct.qProduct n (fun index => (tables index).cellUnder (signals index) (target index) (sample index))).num : Int) =
      ((FiniteProduct.enumeration n (fun index => Option (Channel index))
        (fun index => (tables index).expansionChoicesUnder (target index))).map fun assignment =>
          FiniteProduct.iProduct n (fun index => (tables index).expansionTermUnder (signals index)
            (target index) (sample index) (assignment index))).sum := by
  refine Eq.trans (FiniteProduct.iProduct_qProduct_num n _).symm ?_
  refine Eq.trans (FiniteProduct.iProduct_congr n _ _ (fun index =>
    ((tables index).expansionChoicesUnder_sum (signals index) (target index) (sample index)).symm)) ?_
  exact FiniteProduct.iProduct_finite_sum n (fun index => Option (Channel index))
    (fun index => (tables index).expansionChoicesUnder (target index))
    (fun index => (tables index).expansionTermUnder (signals index) (target index) (sample index))

end BooleanChannelTable
end Probability
end Thesis
