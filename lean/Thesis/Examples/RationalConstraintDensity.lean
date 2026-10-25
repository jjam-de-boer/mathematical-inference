import Thesis.Probability.ConstructiveRealRationalConstraints

namespace Thesis.Examples.RationalConstraintDensity
open Probability Probability.Distros ConstructiveReal
open RationalLinear

/-- The same rational equality is supplied with two different unreduced,
signed coefficient presentations. Its unique feasible coordinate is 1/2. -/
private def upper : RationalConstraint 1 := ⟨fun _ => ⟨2, 6, by decide⟩, ⟨1, 6, by decide⟩⟩
private def lower : RationalConstraint 1 := ⟨fun _ => ⟨-3, 9, by decide⟩, ⟨-1, 6, by decide⟩⟩
private def rows : List (RationalConstraint 1) := [upper, lower, upper]
private def vector : Fin 1 → SignedRatio := fun _ => ⟨1, 2, by decide⟩
private theorem valid : ∀ row ∈ rows, row.Holds vector := by decide +kernel

private theorem real_valid : ∀ row ∈ rows, row.RealHolds (fun i => ofSignedRatio (vector i)) := by
  intro row member
  apply (row.clear_real_iff _).mp
  exact (le_congr (realDot_ofSignedRatio 1 row.clear.coefficients vector) (equiv_refl _)).mpr
    ((ofSignedRatio_le_iff _ _).mpr ((row.clear_iff vector).mpr (valid row member)))

private theorem exactly_half (rational : Fin 1 → SignedRatio) (valid : ∀ row ∈ rows, row.Holds rational) :
    SignedRatio.Equiv (rational 0) ⟨1, 2, by decide⟩ := by
  have above := valid upper (List.mem_cons_self ..)
  have below := valid lower (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  change SignedRatio.LE (SignedRatio.add (SignedRatio.mul (⟨2, 6, by decide⟩ : SignedRatio) (rational 0)) SignedRatio.zero) ⟨1, 6, by decide⟩ at above
  change SignedRatio.LE (SignedRatio.add (SignedRatio.mul (⟨-3, 9, by decide⟩ : SignedRatio) (rational 0)) SignedRatio.zero) ⟨-1, 6, by decide⟩ at below
  have upperBound := (SignedRatio.le_congr (SignedRatio.add_zero _) (SignedRatio.equiv_refl _)).mp above
  have lowerBound := (SignedRatio.le_congr (SignedRatio.add_zero _) (SignedRatio.equiv_refl _)).mp below
  rw [SignedRatio.le_iff_cross] at upperBound lowerBound
  simp only [SignedRatio.mul, Int.natCast_mul, Int.one_mul, Int.neg_one_mul] at upperBound lowerBound
  change (rational 0).num * (2 : Int) = (1 : Int) * (rational 0).den
  rw [Int.one_mul]
  omega

/-- Exact feasibility survives clearing, redundant rows and arbitrary
requested approximation precision. No tolerance is inserted in the equality. -/
example (precision : PositiveRatio) : SignedRatio.Equiv
    ((approximateRationalConstraints rows (fun i => ofSignedRatio (vector i)) real_valid precision).val 0) ⟨1, 2, by decide⟩ :=
  exactly_half _ (approximateRationalConstraints rows (fun i => ofSignedRatio (vector i)) real_valid precision).property.1

end Thesis.Examples.RationalConstraintDensity
