import Thesis.Probability.FiniteBooleanCharacter

namespace Thesis
namespace Probability
namespace Examples
namespace FiniteBooleanCharacter

/-!
# Complete false-cylinder character sums on a three-coordinate cube

The tests keep both free values, rather than merely masking a complete
enumeration and counting the repeated fixed values.  Fixing the two parity
coordinates leaves two positive assignments; fixing only one leaves a free
odd coordinate whose two signs cancel.  Empty and fully fixed products keep
their single explicit assignment.

The negative constant-phase boundary is intentional.  It shows why the
general nonnegativity theorem requires a homogeneous phase.  These tiny
kernel computations supplement, rather than establish, the symbolic
coordinate-induction theorem.
-/

private def first : Fin 3 := ⟨0, by decide⟩
private def last : Fin 3 := ⟨2, by decide⟩
private def parity (assignment : Fin 3 -> Bool) := Bool.xor (assignment first) (assignment last)
private def parityFixed : Fin 3 -> Bool := fun index => decide (index = first ∨ index = last)
private def firstFixed : Fin 3 -> Bool := fun index => decide (index = first)
private def characterSum (fixed : Fin 3 -> Bool) (phase : (Fin 3 -> Bool) -> Bool) : Int :=
  ((FiniteProduct.falseCylinderEnumeration 3 fixed).map
    (fun assignment => FiniteProbRecord.characterSign (phase assignment))).sum

/-- A nonzero linear character is either retained positively or cancelled
by an unfixed parity coordinate.  There is no contribution from a duplicated
false choice at a fixed coordinate. -/
theorem exact_projected_sums :
    characterSum (fun _ => false) parity = 0 ∧
    characterSum parityFixed parity = 2 ∧
    characterSum firstFixed parity = 0 ∧
    characterSum (fun _ => true) parity = 1 := by decide +kernel

/-- A repeated XOR coefficient cancels algebraically and becomes the
constant even character, whose sum is the whole eight-assignment cube. -/
theorem repeated_coefficient_cancels :
    characterSum (fun _ => false) (fun assignment => Bool.xor (assignment first) (assignment first)) = 8 := by
  decide +kernel

/-- Empty products have one assignment and one positive even sign.  A
fully fixed nonempty product likewise has exactly one assignment. -/
theorem empty_and_fixed_support :
    (FiniteProduct.falseCylinderEnumeration 0 (fun _ => false)).length = 1 ∧
    ((FiniteProduct.falseCylinderEnumeration 0 (fun _ => false)).map
      (fun _ => FiniteProbRecord.characterSign false)).sum = 1 ∧
    (FiniteProduct.falseCylinderEnumeration 3 (fun _ => true)).length = 1 := by decide +kernel

/-- A constant odd offset is not homogeneous and can negate the complete
cylinder sum.  It must not silently satisfy the general theorem's premises. -/
theorem odd_offset_boundary : characterSum parityFixed (fun _ => true) = -2 := by decide +kernel

/-- Symbolic application of the general theorem to every fixed-coordinate
mask.  The proof checks the phase's XOR law, not a finite list of mask cases. -/
theorem parity_projection_nonnegative (fixed : Fin 3 -> Bool) : 0 <= characterSum fixed parity := by
  apply FiniteProduct.falseCylinder_characterSum_nonneg 3 fixed parity rfl
  intro left right
  change Bool.xor (Bool.xor (left first) (right first)) (Bool.xor (left last) (right last)) =
    Bool.xor (Bool.xor (left first) (left last)) (Bool.xor (right first) (right last))
  generalize left first = leftFirst
  generalize right first = rightFirst
  generalize left last = leftLast
  generalize right last = rightLast
  cases leftFirst <;> cases rightFirst <;> cases leftLast <;> cases rightLast <;> rfl

/-- The public theorem also applies to filtering the original complete
enumeration, with both unqueried values still present. -/
theorem filtered_original_cube_nonnegative (fixed : Fin 3 -> Bool) :
    0 <= (((FiniteProduct.enumeration 3 (fun _ => Bool) (fun _ => [false, true])).filter
      (FiniteProduct.falseCylinder 3 fixed)).map
      (fun assignment => FiniteProbRecord.characterSign (parity assignment))).sum := by
  have same := FiniteSupportedSum.sum_eq_of_perm
    ((FiniteProduct.falseCylinderEnumeration_perm_filter 3 fixed).map
      (fun assignment => FiniteProbRecord.characterSign (parity assignment)))
  rw [← same]
  exact parity_projection_nonnegative fixed

end FiniteBooleanCharacter
end Examples
end Probability
end Thesis
