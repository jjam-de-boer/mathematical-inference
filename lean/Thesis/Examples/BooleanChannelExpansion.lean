import Thesis.Probability.BooleanChannelExpansion

namespace Thesis
namespace Probability
namespace Examples
namespace BooleanChannelExpansion

/-!
# Small exact checks for complete channel expansions and integration

The row-product checks retain the interaction between two nonuniform rows.
They also test a matching hard intervention and a conflicting forced value:
forced rows contribute their actual indicators, never hidden channel choices.
The numerical checks are deliberately limited to two Boolean rows with two
channels each; no graph search or SCM response-function space is evaluated.

The integration check uses unequal record denominators, repeated labels and
a zero-weight atom.  One character has a negative integral, but another has
zero integral, so their actual independent product cancels.  These are signed
integrands against ordinary nonnegative records, not signed probabilities.
-/

private def amplitude (channel : Bool) : Nat := if channel then 2 else 1

private def table : BooleanChannelTable Bool :=
  BooleanChannelTable.ofCapacity [false, true] amplitude 5 (by decide +kernel)

private def tables (_index : Fin 2) : BooleanChannelTable Bool := table
private def signals (_index : Fin 2) (channel : Bool) : Bool := channel
private def sample (index : Fin 2) : Bool := decide (index.val = 1)
private def noTargets (_index : Fin 2) : Option Bool := none

private def matchingTarget (index : Fin 2) : Option Bool :=
  if index.val = 0 then some false else none

private def conflictingTarget (index : Fin 2) : Option Bool :=
  if index.val = 0 then some true else none

private def expandedNumerator (target : Fin 2 -> Option Bool) : Int :=
  ((FiniteProduct.enumeration 2 (fun _ => Option Bool)
    (fun index => (tables index).expansionChoicesUnder (target index))).map fun assignment =>
      FiniteProduct.iProduct 2 (fun index => (tables index).expansionTermUnder
        (signals index) (target index) (sample index) (assignment index))).sum

/-- The actual product has numerator 24, including the negative interaction
between its row deviations from capacity.  The complete expansion agrees. -/
theorem interaction_retained :
    ((FiniteProduct.qProduct 2 (fun index => (tables index).cellUnder
      (signals index) (noTargets index) (sample index))).num : Int) = 24 ∧
    expandedNumerator noTargets = 24 := by
  constructor
  · decide +kernel
  · exact (BooleanChannelTable.product_num_expansion 2 (fun _ => Bool)
      tables signals noTargets sample).symm.trans (by decide +kernel)

/-- A matching forced row has numerator and denominator one.  Its channel
summands disappear, leaving exactly the other actual row's numerator. -/
theorem matching_intervention :
    expandedNumerator matchingTarget = 6 ∧
    (FiniteProduct.qProduct 2 (fun index => (tables index).cellUnder
      (signals index) (matchingTarget index) (sample index))).den = 10 := by
  constructor
  · exact (BooleanChannelTable.product_num_expansion 2 (fun _ => Bool)
      tables signals matchingTarget sample).symm.trans (by decide +kernel)
  · decide +kernel

/-- A conflicting forced sample has zero numerator in both the actual
row product and its complete expansion.  No division by that cell occurs. -/
theorem conflicting_intervention : expandedNumerator conflictingTarget = 0 :=
  (BooleanChannelTable.product_num_expansion 2 (fun _ => Bool)
    tables signals conflictingTarget sample).symm.trans (by decide +kernel)

private def negativeRecord : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 2)]
  den := 3
  den_pos := by decide
  total_mass := rfl

private def balancedRecord : FiniteProbRecord Bool where
  atoms := [(false, 2), (true, 2), (true, 0)]
  den := 4
  den_pos := by decide
  total_mass := rfl

/-- A negative integrand integral is allowed without changing any natural
probability weight.  The repeated, zero-weight atom is retained exactly. -/
theorem individual_signed_masses :
    negativeRecord.signedMass FiniteProbRecord.characterSign = -1 ∧
    balancedRecord.signedMass FiniteProbRecord.characterSign = 0 := by
  decide +kernel

/-- Cancellation uses the actual independent-product integration theorem,
not an inference from unrelated marginal records or matching denominators. -/
theorem weighted_product_cancels :
    (negativeRecord.product balancedRecord).signedMass (fun pair =>
      FiniteProbRecord.characterSign pair.1 * FiniteProbRecord.characterSign pair.2) = 0 := by
  rw [FiniteProbRecord.signedMass_product, individual_signed_masses.2, Int.mul_zero]

/-- The exact finite-sum expansion also covers an empty local choice list.
There are then no full assignments and the corresponding product is zero. -/
theorem empty_local_choices :
    FiniteProduct.iProduct 2 (fun index : Fin 2 =>
      ((if index.val = 0 then [] else [false]).map fun bit =>
        FiniteProbRecord.characterSign bit).sum) = 0 ∧
    ((FiniteProduct.enumeration 2 (fun _ => Bool)
      (fun index => if index.val = 0 then [] else [false])).map fun assignment =>
        FiniteProduct.iProduct 2 (fun index => FiniteProbRecord.characterSign (assignment index))).sum = 0 := by
  constructor
  · decide +kernel
  · exact (FiniteProduct.iProduct_finite_sum 2 (fun _ => Bool)
      (fun index => if index.val = 0 then [] else [false])
      (fun _ => FiniteProbRecord.characterSign)).symm.trans (by decide +kernel)

end BooleanChannelExpansion
end Examples
end Probability
end Thesis
