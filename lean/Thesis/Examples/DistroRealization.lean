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

example : (match checkFactorialMomentTable suppliedFactorialTable 2 with | .inl _ => true | .inr _ => false) = true := by decide +kernel
example : (match checkFactorialMomentTable negativeCellFactorialTable 2 with | .inl _ => false | .inr (.negative value _ _) => decide (value = 1) | .inr (.unnormalized _) => false) = true := by decide +kernel
example : (match checkFactorialMomentTable (fun _ => QProb.zero) 0 with | .inr (.unnormalized _) => true | _ => false) = true := by decide +kernel
example : (match checkFactorialMomentTable (fun _ => QProb.one) 0 with | .inl _ => true | .inr _ => false) = true := by decide +kernel

/-- Supplied mixed moments for equal mass at [0,0,0] and [1,0,2].
This definition does not presuppose a realizing distribution. -/
def suppliedJointTable : List Nat → QProb
  | [0, 0, 0] => QProb.one
  | [1, 0, 0] => ⟨1, 2, by decide⟩
  | [0, 0, 1] => QProb.one
  | [0, 0, 2] => QProb.one
  | [1, 0, 1] => QProb.one
  | [1, 0, 2] => QProb.one
  | _ => QProb.zero

theorem suppliedJointTable_valid : JointFactorialMomentTableValid suppliedJointTable [1, 0, 2] := by
  constructor
  · intro value within
    have checked : ∀ value ∈ factorialRectangle [1, 0, 2],
        SignedRatio.Nonnegative (inverseJointFactorialTable suppliedJointTable [1, 0, 2] value) := by decide +kernel
    exact checked value (factorialRectangle_complete _ _ within)
  · decide +kernel

example (orders : List Nat) (within : CoordinateBounds orders [1, 0, 2]) :
    QProb.Equiv (jointFactorialMoment (realizedJointFactorialDistro suppliedJointTable [1, 0, 2] suppliedJointTable_valid) orders)
      (suppliedJointTable orders) := realizedJointFactorialDistro_moments _ _ _ _ within

example : SignedRatio.Equiv
    ((realizedJointFactorialDistro suppliedJointTable [1, 0, 2] suppliedJointTable_valid).pmf [1, 0, 2]).toSignedRatio
    ⟨1, 2, by decide⟩ :=
  SignedRatio.equiv_trans (realizedJointFactorialDistro_pmf _ _ _ _ rfl) (by decide +kernel)

example : ([0, 0, 1], 0) ∈ (realizedJointFactorialDistro suppliedJointTable [1, 0, 2] suppliedJointTable_valid).record.atoms := by decide +kernel

def alternativeJointLaw : Distro (List Nat) :=
  ofWeightedAtoms [([1, 0, 2], 2), ([0, 0, 0], 2), ([], 0), ([99, 99], 0)] (by decide)

example : alternativeJointLaw.SameLaw (realizedJointFactorialDistro suppliedJointTable [1, 0, 2] suppliedJointTable_valid) := by
  apply realizedJointFactorialDistro_unique _ _ _ alternativeJointLaw (by decide +kernel)
  intro orders within
  have checked : ∀ orders ∈ factorialRectangle [1, 0, 2],
      QProb.Equiv (jointFactorialMoment alternativeJointLaw orders) (suppliedJointTable orders) := by decide +kernel
  exact checked orders (factorialRectangle_complete _ _ within)

example : (match checkJointFactorialMomentTable suppliedJointTable [1, 0, 2] with | .inl _ => true | .inr _ => false) = true := by decide +kernel

/-- Invalid cross-moment data can have normalized inverse masses while
forcing negative joint cells. The checker returns the first such cell. -/
def invalidJointTable : List Nat → QProb
  | [0, 0] => QProb.one
  | [1, 1] => QProb.one
  | _ => QProb.zero

example : (match checkJointFactorialMomentTable invalidJointTable [1, 1] with
    | .inr (.negative value _ _) => decide (value = [0, 1]) | _ => false) = true := by decide +kernel

example : (match checkJointFactorialMomentTable (fun _ => QProb.zero) [] with
    | .inr (.unnormalized _) => true | _ => false) = true := by decide +kernel

example : (match checkJointFactorialMomentTable (fun _ => QProb.one) [] with
    | .inl law => decide ((law.distro.pmf []).num = (law.distro.pmf []).den) | .inr _ => false) = true := by decide +kernel

example : (match checkJointFactorialMomentTable (fun _ => QProb.one) [0, 0] with
    | .inl law => decide ((law.distro.pmf [0, 0]).num = (law.distro.pmf [0, 0]).den) | .inr _ => false) = true := by decide +kernel

end Thesis.Examples.DistroRealization
