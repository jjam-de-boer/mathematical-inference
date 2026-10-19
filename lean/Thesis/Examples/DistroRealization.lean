import Thesis.Examples.DistributionExtensions

namespace Thesis.Examples.DistroRealization
open Probability Probability.Distros DistributionExtensions

/-- Refinement fails at the recorded null outcome 99, while the tower law
still holds at every outcome, not only at positive ones. -/
example (x : Nat) : SignedRatio.Equiv
    (partitionMomentFixture.conditionalExpectation predictionCoarse
      (partitionMomentFixture.conditionalExpectation predictionFine partitionMomentObservable) x)
    (partitionMomentFixture.conditionalExpectation predictionCoarse partitionMomentObservable x) :=
  Distro.conditionalExpectation_tower_almostSurely _ predictionFine predictionCoarse predictionMerge
    (by decide +kernel) partitionMomentObservable x

example : predictionCoarse 99 ≠ predictionMerge (predictionFine 99) := by decide +kernel

example : (∀ i ∈ List.range 3, SignedRatio.Equiv
    ((multinomialDistro 2 [1, 0, 2] (by decide)).rationalCovarianceRow (List.range 3) countResponse nullDirectionCoefficients i)
      SignedRatio.zero) :=
  (multinomial_covarianceRows_zero_iff 2 [1, 0, 2] (by decide) nullDirectionCoefficients).mpr
    (Or.inr nullDirectionCoefficients_constant)

/-- Repeated indices, empty indices and unreduced coefficients need no
additional assumptions in the row characterization. -/
example : (partitionMomentFixture.rationalCovarianceForm []
    (fun _ : Nat => partitionMomentObservable) (fun _ => SignedRatio.one)).num = 0 :=
  (Distro.rationalCovarianceForm_zero_iff_rows _ _ _ _).mpr (by intro i member; exact False.elim (List.not_mem_nil member))

example : (partitionMomentFixture.rationalCovarianceForm [0, 0]
    (fun _ : Nat => partitionMomentObservable) (fun i => if i = 0 then ⟨0, 7, by decide⟩ else SignedRatio.one)).num = 0 :=
  (Distro.rationalCovarianceForm_zero_iff_rows _ _ _ _).mpr (by decide +kernel)

example : (match checkFactorialMomentTable suppliedFactorialTable 2 with | .inl _ => True | .inr _ => False) := by decide +kernel
example : (match checkFactorialMomentTable negativeCellFactorialTable 2 with | .inl _ => False | .inr (.negative value _ _) => value = 1 | .inr (.unnormalized _) => False) := by decide +kernel
example : (match checkFactorialMomentTable (fun _ => QProb.zero) 0 with | .inr (.unnormalized _) => True | _ => False) := by decide +kernel
example : (match checkFactorialMomentTable (fun _ => QProb.one) 0 with | .inl _ => True | .inr _ => False) := by decide +kernel

end Thesis.Examples.DistroRealization
