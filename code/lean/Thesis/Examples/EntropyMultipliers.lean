import Thesis.Probability.ConstructiveRealEntropyMultipliers

namespace Thesis.Examples.EntropyMultipliers
open Probability Probability.Distros ConstructiveReal
open IntegerRowSpace RationalLinear

/-- A negative pivot away from the final column, an all-zero row, and two
proportional rows force all three elimination branches to participate. -/
private def matrix : Matrix 4 3 := fun row column =>
  if row = 0 then (if column = 0 then 2 else 0)
  else if row = 1 then (if column = 0 then 4 else 0)
  else if row = 2 then 0
  else if column = 1 then -3 else 0

private def original (first second : ConstructiveReal) : Fin 4 → ConstructiveReal :=
  fun row => if row = 0 then first else if row = 1 then second else if row = 2 then zero else one

private def gradient (first second : ConstructiveReal) (column : Fin 3) : ConstructiveReal :=
  realDot 4 (fun row => matrix row column) (original first second)

private def represented (first second : ConstructiveReal) : Multipliers matrix (gradient first second) :=
  ⟨original first second, fun _ => equiv_refl _⟩

private def computed (first second : ConstructiveReal) : Multipliers matrix (gradient first second) :=
  ofAnnihilator 4 3 matrix (gradient first second) (represented first second).annihilates

/-- Dropped zero/redundant equations actually receive zero coefficients in
the returned data; these equalities inspect the constructor's finite path. -/
example (first second : ConstructiveReal) : (computed first second).value 2 = zero := by rfl
example (first second : ConstructiveReal) : (computed first second).value 0 = zero := by rfl

example (first second : ConstructiveReal) (column : Fin 3) :
    Equiv (gradient first second column) (realDot 4 (fun row => matrix row column) (computed first second).value) :=
  (computed first second).represents column

/-- The multiplier conclusion holds for arbitrary analytic first and second
coefficients, rather than relying on a test of their sign or equality. -/
example (first second : ConstructiveReal) : AnnihilatesKernel matrix (gradient first second) :=
  (computed first second).annihilates

private def repeated : RationalConstraint 1 := ⟨fun _ => ⟨-2, 14, by decide⟩, ⟨-1, 7, by decide⟩⟩
private def slack : RationalConstraint 1 := ⟨fun _ => SignedRatio.zero, SignedRatio.one⟩
private def problem : RationalEntropyProblem 1 := ⟨by decide, [repeated, slack, repeated]⟩
private def anchor : problem.RealLaw :=
  .ofRationalVector problem (fun _ => SignedRatio.one) ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)
private theorem positive (index : Fin 1) : LE (ofSignedRatio PositiveRatio.one.toSignedRatio) (anchor.mass index).value := le_refl _

/-- This actual example has a maximum without assuming a multiplier or an
optimization witness: normalization forces its sole probability to one. -/
private theorem maximal : anchor.Maximal := by
  intro other
  have normalized := other.normalized
  change Equiv (add (mul one (other.mass 0).value) zero) one at normalized
  have coordinate : Equiv (other.mass 0).value (anchor.mass 0).value :=
    equiv_trans (equiv_symm (equiv_trans (add_congr (one_mul _) (equiv_refl zero)) (add_zero _))) normalized
  have entropy : Equiv other.entropy anchor.entropy := by
    change Equiv (add ((other.mass 0).value.realEntropyTerm (other.mass 0).nonnegative (other.mass 0).bounded) zero)
      (add ((anchor.mass 0).value.realEntropyTerm (anchor.mass 0).nonnegative (anchor.mass 0).bounded) zero)
    exact add_congr (realEntropyTerm_congr coordinate _ _ _ _) (equiv_refl zero)
  exact entropy.1

/-- A checked opaque body prevents downstream symbolic checks from reducing
the entire elimination algorithm during type comparison. -/
private opaque bits : problem.LagrangeCoefficients (fun i => entropyBitGradient (anchor.mass i).value PositiveRatio.one (positive i)) :=
  anchor.lagrangeMultipliers maximal (fun _ => PositiveRatio.one) positive

example : Equiv (entropyBitGradient (anchor.mass 0).value PositiveRatio.one (positive 0))
    (add bits.offset (realRationalDot problem.rows.length (fun row => (problem.rows[row.val]).coefficients 0) bits.coefficient)) :=
  bits.represents 0

private def natural : problem.LagrangeCoefficients (fun i => entropyNaturalGradient (anchor.mass i).value PositiveRatio.one (positive i)) :=
  bits.scale lnTwo _ (fun i => entropyGradient_units _ _ _)

example : natural.offset = mul bits.offset lnTwo := rfl
example (row : Fin problem.rows.length) : natural.coefficient row = mul (bits.coefficient row) lnTwo := rfl

example : Equiv (entropyNaturalGradient (anchor.mass 0).value PositiveRatio.one (positive 0))
    (add natural.offset (realRationalDot problem.rows.length (fun row => (problem.rows[row.val]).coefficients 0) natural.coefficient)) :=
  natural.represents 0

end Thesis.Examples.EntropyMultipliers
