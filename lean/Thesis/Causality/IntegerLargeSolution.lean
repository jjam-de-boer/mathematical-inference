import Thesis.Causality.IntegerFeasibility
import Thesis.Causality.IntegerCarryLoops
import Thesis.Causality.FiniteLabelledRepetition

namespace Thesis.Causality.IntegerEquations

/-!
# Large natural solutions yield positive homogeneous directions

Let N be the length of the equation system's finite carry enumeration.
From a supplied solution whose selected coordinate is at least 2^N, this
module computes a natural vector h with A*h = 0 and a positive coordinate
at that same index. The threshold is determined by the input equations;
there is no assumed bound on candidate solutions or their binary lengths.

Three connections are essential. Decoding the constructed binary word must
recover the supplied solution, since equation satisfaction alone does not
determine its coordinates. A word of length k has every coordinate below
2^k. Finally, literal repetition ending within the first N transitions
must leave a positive suffix when the full coordinate is at least 2^N.
The earlier loop-to-direction theorem then supplies the actual witness.

The existing padded encoding is retained; evaluating large supplied vectors
can be expensive. The proofs work with symbolic inputs and use no logarithm,
infinite selection, or general propositional decision principle. This is
the large-coordinate implication only. A coordinate classifier and Petri
execution or pumping tests remain separate constructions.
-/

variable {rows variables : Nat}

/-- The existing sufficient encoding fuel also preserves every individual
coordinate, including leading zero digits and the zero-fuel case. -/
theorem decodeWord_binaryWord (fuel : Nat) (values : Fin variables → Nat)
    (small : ∀ index, values index ≤ fuel) : decodeWord (binaryWord fuel values) = values := by
  induction fuel generalizing values with
  | zero =>
      funext index
      have zero := small index
      change 0 = values index
      omega
  | succ fuel ih =>
      have smaller : ∀ index, values index / 2 ≤ fuel := by
        intro index
        have before := small index
        omega
      have tail := ih (fun index => values index / 2) smaller
      funext index
      change digitValues (lowDigit values) index +
        2 * decodeWord (binaryWord fuel (fun index => values index / 2)) index = values index
      rw [digitValues_lowDigit, tail]
      change values index % 2 + 2 * (values index / 2) = values index
      omega

/-- Every coordinate of a literal binary word fits strictly below the
power of two determined by its length; zero padding does not break this. -/
theorem decodeWord_lt_pow_length (word : List (Digit variables)) (index : Fin variables) :
    decodeWord word index < 2 ^ word.length := by
  induction word with
  | nil => exact Nat.zero_lt_one
  | cons digit rest ih =>
      have bitBound : digitValues digit index < 2 := (digit[index]).isLt
      change digitValues digit index + 2 * decodeWord rest index < 2 ^ (rest.length + 1)
      rw [Nat.pow_succ]
      omega

/-- A large decoded coordinate forces enough transitions for the finite
repetition theorem. The strict conclusion also records the binary boundary. -/
theorem length_gt_of_large_decode (word : List (Digit variables)) (index : Fin variables)
    (bound : Nat) (large : 2 ^ bound ≤ decodeWord word index) : bound < word.length := by
  have capacity := decodeWord_lt_pow_length word index
  by_cases short : word.length ≤ bound
  · have powers : 2 ^ word.length ≤ 2 ^ bound := Nat.pow_le_pow_right (by decide) short
    omega
  · omega

/-- If the loop ends by N, the earlier digits cannot account for a full
coordinate at least 2^N. Thus the literal suffix has a positive coordinate.
This concerns actual values; an accepting zero-padded word alone is weaker. -/
theorem suffix_positive_of_large_decode (initial cycle suffix : List (Digit variables))
    (index : Fin variables) (bound : Nat) (within : initial.length + cycle.length ≤ bound)
    (large : 2 ^ bound ≤ decodeWord (initial ++ (cycle ++ suffix)) index) :
    0 < decodeWord suffix index := by
  have capacity := decodeWord_lt_pow_length (initial ++ cycle) index
  have powers : 2 ^ (initial ++ cycle).length ≤ 2 ^ bound :=
    Nat.pow_le_pow_right (by decide) (by simpa only [List.length_append] using within)
  have combined : decodeWord (initial ++ (cycle ++ suffix)) index =
      decodeWord (initial ++ cycle) index + 2 ^ (initial ++ cycle).length * decodeWord suffix index := by
    simpa only [List.append_assoc] using decodeWord_append (initial ++ cycle) suffix index
  by_cases zero : decodeWord suffix index = 0
  · rw [combined, zero, Nat.mul_zero, Nat.add_zero] at large
    omega
  · omega

/-- A supplied large solution computes a nonnegative homogeneous direction
positive at the same coordinate. Both the loop and the direction are data
from finite constructions; no witness is selected from an existential Prop.
All signed coefficients and right-hand sides remain unrestricted. -/
def System.directionOfLargeSolution (system : System rows variables) (values : Fin variables → Nat)
    (valid : system.Satisfies values) (index : Fin variables)
    (large : 2 ^ system.carryWitness.enumeration.length ≤ values index) :
    {direction : Fin variables → Nat // system.homogeneous.Satisfies direction ∧ 0 < direction index} := by
  let word := binaryWord (encodingFuel values) values
  have decoded : decodeWord word = values := decodeWord_binaryWord _ values (le_encodingFuel values)
  have wordLarge : 2 ^ system.carryWitness.enumeration.length ≤ decodeWord word index := by
    rw [decoded]
    exact large
  have lengthEnough : system.carryWitness.enumeration.length ≤ word.length :=
    Nat.le_of_lt (length_gt_of_large_decode word index _ wordLarge)
  let repetition := FiniteLabelledReachability.factorRepetition system.carryWitness system.advance
    system.initialCarry system.zeroCarry word (system.satisfies_run values valid) lengthEnough
  have suffixPositive : 0 < decodeWord repetition.suffix index :=
    suffix_positive_of_large_decode repetition.initial repetition.cycle repetition.suffix index _
      repetition.within (by rw [← repetition.word_eq]; exact wordLarge)
  exact ⟨loopDirection repetition.cycle repetition.suffix,
    system.loopDirection_satisfies repetition.cycle_run repetition.suffix_run,
    loopDirection_pos repetition.nonempty index suffixPositive⟩

end Thesis.Causality.IntegerEquations
