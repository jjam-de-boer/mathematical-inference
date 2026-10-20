import Thesis.Examples.DistroPartialMoments

namespace Thesis.Examples.DistroRanks
open Probability Probability.Distros RationalVector

/-- Two positive categories separated by a retained null category. -/
def multinomialRankFixture := multinomial_covarianceRank 2 [1, 0, 2] (by decide) (by decide)
def multinomialKernelFixture := multinomial_covarianceKernelBasis 2 [1, 0, 2] (by decide) (by decide)

example : positiveColourCount [1, 0, 2] = 2 := by decide +kernel
example : multinomialRankFixture.basis.indices = [⟨2, by decide⟩] := by rfl
example : multinomialKernelFixture.indices = [none, some ⟨1, by decide⟩] := by decide +kernel

/-- The chosen image vector is an actual covariance column. -/
example : SignedRatio.Equiv (multinomialRankFixture.basis.vectors ⟨2, by decide⟩ ⟨0, by decide⟩)
    ⟨-4, 9, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (multinomialRankFixture.basis.vectors ⟨2, by decide⟩ ⟨2, by decide⟩)
    ⟨4, 9, by decide⟩ := by decide +kernel

/-- Public independence and spanning witnesses can be used directly. -/
example (coefficients : Fin 3 → SignedRatio)
    (vanished : RationalVector.Equiv
      (combine multinomialRankFixture.basis.indices multinomialRankFixture.basis.vectors coefficients) RationalVector.zero) :
    SignedRatio.Equiv (coefficients ⟨2, by decide⟩) SignedRatio.zero :=
  multinomialRankFixture.basis.independent coefficients vanished ⟨2, by decide⟩ (List.mem_singleton_self _)

example (source : Vector 3) : ∃ coefficients, RationalVector.Equiv
    (combine multinomialRankFixture.basis.indices multinomialRankFixture.basis.vectors coefficients)
    (((multinomialDistro 2 [1, 0, 2] (by decide)).occupancyOperator 3).apply source) :=
  multinomialRankFixture.basis.spanning _ ⟨source, RationalVector.equiv_refl _⟩

/-- An unreduced common positive coefficient and an arbitrary signed null
coefficient have the expected explicit kernel expansion. -/
def kernelCoordinates : Option (Fin 3) → SignedRatio
  | none => ⟨2, 4, by decide⟩
  | some i => if i.val = 1 then ⟨-2, 1, by decide⟩ else SignedRatio.zero

example : RationalVector.Equiv
    (combine multinomialKernelFixture.indices multinomialKernelFixture.vectors kernelCoordinates)
    (fun i => if i.val = 1 then ⟨-3, 2, by decide⟩ else ⟨1, 2, by decide⟩) := by decide +kernel

example : (reinforcedCount_covarianceRank 2 2 [1, 0, 2] (by decide) (by decide)).basis.indices =
    [⟨2, by decide⟩] := by rfl

example : (multivariateHypergeometric_covarianceRank 2 [1, 0, 2] (by decide) (by decide) (by decide)).basis.indices =
    [⟨2, by decide⟩] := by rfl
example : SignedRatio.Equiv
    ((multivariateHypergeometric_covarianceRank 2 [1, 0, 2] (by decide) (by decide) (by decide)).basis.vectors
      ⟨2, by decide⟩ ⟨0, by decide⟩) ⟨-2, 9, by decide⟩ := by decide +kernel

/-- One positive category has rank zero even with positive trials. The
kernel basis still covers all three original coordinates. -/
example : (multinomial_covarianceRank 2 [0, 3, 0] (by decide) (by decide)).basis.indices = [] := by decide +kernel
example : (multinomial_covarianceKernelBasis 2 [0, 3, 0] (by decide) (by decide)).indices =
    [none, some ⟨0, by decide⟩, some ⟨2, by decide⟩] := by decide +kernel

/-- Zero-trial and full-population kernels have the full coordinate basis. -/
example : (multinomial_covarianceRank_zero [1, 0, 2] (by decide)).basis.indices = [] := by decide +kernel
example : (reinforcedCount_covarianceKernelBasis_zero 2 [1, 0, 2] (by decide)).indices =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := by decide +kernel
example : (multivariateHypergeometric_covarianceRank_full [1, 0, 2] (by decide)).basis.indices = [] := by decide +kernel
example : (multivariateHypergeometric_covarianceKernelBasis_full [1, 0, 2] (by decide)).indices =
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := by decide +kernel

/-- Empty and one-ball populations need no artificial positive pivot. -/
example : (multivariateHypergeometric_covarianceKernelBasis_zero [] (by decide)).indices = [] := by decide +kernel
example : (multivariateHypergeometric_covarianceKernelBasis_full [1] (by decide)).indices = [⟨0, by decide⟩] := by decide +kernel

end Thesis.Examples.DistroRanks
