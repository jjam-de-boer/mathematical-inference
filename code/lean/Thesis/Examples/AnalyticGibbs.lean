import Thesis.Probability.ConstructiveRealEntropyGlobalOptimality

namespace Thesis.Examples.AnalyticGibbs
open Probability Probability.Distros ConstructiveReal
open RationalLinear RationalEntropyProblem

private def signedConstant : RationalConstraint 2 := ⟨fun _ => ⟨-2, 14, by decide⟩, ⟨-1, 7, by decide⟩⟩
private def features := [signedConstant, signedConstant]
private def problem : RationalEntropyProblem 2 := equalities 2 (by decide) features
private def uniform : problem.RealLaw :=
  .ofRationalVector problem (fun _ => ⟨2, 4, by decide⟩) ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)
private def boundary : problem.RealLaw :=
  .ofRationalVector problem (fun i => if i = 0 then SignedRatio.one else SignedRatio.zero)
    ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)
private def floor : PositiveRatio := ⟨1, 4, by decide, by decide⟩
private theorem positive (i : Fin 2) : LE (ofSignedRatio floor.toSignedRatio) (uniform.mass i).value :=
  (ofSignedRatio_le_iff _ _).mpr (by
    change SignedRatio.LE (⟨1, 4, by decide⟩ : SignedRatio) ⟨2, 4, by decide⟩
    decide +kernel)

/-- Constant gradient with zero moment coefficients. The sufficiency proof
below receives this certificate without an assumed maximum. -/
private def certificate : problem.LagrangeCoefficients
    (fun i => entropyBitGradient (uniform.mass i).value floor (positive i)) where
  offset := entropyBitGradient (uniform.mass 0).value floor (positive 0)
  coefficient _ := zero
  represents column := by
    have scoreZero : Equiv (realRationalDot problem.rows.length (fun row => (problem.rows[row.val]).coefficients column) (fun _ => zero)) zero :=
      equiv_trans (realRationalDot_pair _ _ _) (FiniteLinear.pair_zero_second _ _)
    exact equiv_symm (equiv_trans (add_congr (equiv_refl _) scoreZero) (add_zero _))

private theorem maximal : uniform.Maximal :=
  equalities_maximal_of_coefficients (by decide) features uniform (fun _ => floor) positive certificate

/-- The competitor really contains a zero coordinate, so no positivity
assumption on the observed law can be silently inserted in these bounds. -/
example : Equiv (boundary.mass 1).value zero := equiv_refl _

example : LE boundary.entropy uniform.entropy := maximal boundary

example : LE zero (realRelativeEntropySum boundary.mass uniform.mass (fun _ => floor) positive) :=
  realRelativeEntropySum_nonnegative boundary.mass uniform.mass boundary.normalized uniform.normalized (fun _ => floor) positive

example : LE zero (naturalRelativeEntropySum boundary.mass uniform.mass (fun _ => floor) positive) :=
  naturalRelativeEntropySum_nonnegative boundary.mass uniform.mass boundary.normalized uniform.normalized (fun _ => floor) positive

/-- The constant-cross-entropy conclusion is derived from the actual
paired signed rows, including their duplicate and unreduced presentations. -/
private theorem fixed (observed : problem.RealLaw) (row : RationalConstraint 2) (member : row ∈ problem.rows) :
    Equiv (realRationalDot 2 row.coefficients (fun i => (observed.mass i).value))
      (realRationalDot 2 row.coefficients (fun i => (uniform.mass i).value)) :=
  equiv_trans (equalities_allRows_exact (by decide) features observed row member)
    (equiv_symm (equalities_allRows_exact (by decide) features uniform row member))

example (observed : problem.RealLaw) : Equiv (realCrossEntropySum observed.mass uniform.mass (fun _ => floor) positive) uniform.entropy :=
  uniform.crossEntropy_eq_of_coefficients observed (fun _ => floor) positive certificate (fixed observed)

/-- KL is exactly the entropy gap for these fixed expectations. -/
example : Equiv (realRelativeEntropySum boundary.mass uniform.mass (fun _ => floor) positive)
    (sub uniform.entropy boundary.entropy) :=
  uniform.relativeEntropy_eq_gap_of_coefficients boundary (fun _ => floor) positive certificate (fixed boundary)

example (other : problem.RealLaw) (optimal : other.Maximal) (index : Fin 2) :
    Equiv (other.mass index).value (uniform.mass index).value := other.maximal_unique uniform optimal maximal index

/-- The sampled path stays positive when approaching the zero endpoint. -/
example (n : Nat) (later : 0 < n) : LE (ofSignedRatio floor.half.toSignedRatio)
    ((uniform.mass 1).towards (boundary.mass 1) n).value :=
  (uniform.mass 1).towards_positive (boundary.mass 1) floor (positive 1) n later

end Thesis.Examples.AnalyticGibbs
