import Thesis.Examples.DistroRealization

namespace Thesis.Examples.DistroPartialMoments
open Probability Probability.Distros DistributionExtensions DistroRealization

/-- Three different label spaces, including an unsupported intermediate
label at the retained null outcome 99. -/
def stageLabels : Nat → Nat
  | 0 => 1
  | 1 => 3
  | _ => 4

def stageObserve : (stage : Nat) → Nat → Fin (stageLabels stage)
  | 0, _ => 0
  | 1, x => unsupportedCoarse x
  | _ + 2, x => predictionFine x

def stageMerge : (stage : Nat) → Fin (stageLabels (stage + 1)) → Fin (stageLabels stage)
  | 0, _ => 0
  | 1, label => unsupportedMerge label
  | _ + 2, label => label

def finiteChain : ObservationChain partitionMomentFixture 2 where
  labels := stageLabels
  observe := stageObserve
  merge := stageMerge
  agrees := by
    intro stage within
    have alternatives : stage = 0 ∨ stage = 1 := by omega
    rcases alternatives with rfl | rfl <;> decide +kernel

example : finiteChain.observe 1 99 ≠ finiteChain.merge 1 (finiteChain.observe 2 99) := by decide +kernel

example (x : Nat) : SignedRatio.Equiv
    (partitionMomentFixture.conditionalExpectation (finiteChain.observe 0)
      (partitionMomentFixture.conditionalExpectation (finiteChain.observe 2) partitionMomentObservable) x)
    (partitionMomentFixture.conditionalExpectation (finiteChain.observe 0) partitionMomentObservable x) :=
  finiteChain.tower 0 2 (by decide) partitionMomentObservable x

example (x : Nat) : SignedRatio.Equiv
    (partitionMomentFixture.conditionalExpectation (finiteChain.observe 1)
      (finiteChain.increment partitionMomentObservable 1) x) SignedRatio.zero :=
  finiteChain.increment_conditional_zero partitionMomentObservable 1 (by decide) x

example : SignedRatio.Equiv (partitionMomentFixture.rationalExpectation (fun x => SignedRatio.mul
    (finiteChain.increment partitionMomentObservable 0 x) (finiteChain.increment partitionMomentObservable 1 x))) SignedRatio.zero :=
  finiteChain.increments_orthogonal partitionMomentObservable 0 0 (by decide)

example : SignedRatio.Equiv (finiteChain.energy partitionMomentObservable 0) SignedRatio.one := by decide +kernel
example : SignedRatio.Equiv (finiteChain.energy partitionMomentObservable 1) ⟨1, 4, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (finiteChain.gain partitionMomentObservable 0 2) ⟨5, 4, by decide⟩ := by decide +kernel

example : SignedRatio.Equiv
    (partitionMomentFixture.rationalSquaredError partitionMomentObservable (finiteChain.mean partitionMomentObservable 0))
    (SignedRatio.add
      (partitionMomentFixture.rationalSquaredError partitionMomentObservable (finiteChain.mean partitionMomentObservable 2))
      (SignedRatio.listSum ((List.range 2).map (fun step => finiteChain.energy partitionMomentObservable step)))) :=
  finiteChain.prediction_error_sum partitionMomentObservable 0 2 (by decide)

example : SignedRatio.Equiv
    (partitionMomentFixture.rationalSquaredError partitionMomentObservable (finiteChain.mean partitionMomentObservable 1))
    (SignedRatio.add
      (partitionMomentFixture.rationalSquaredError partitionMomentObservable (finiteChain.mean partitionMomentObservable 1))
      (finiteChain.gain partitionMomentObservable 1 0)) :=
  finiteChain.prediction_error_decomposition partitionMomentObservable 1 0 (by decide)

example : SignedRatio.Equiv (finiteChain.gain (fun _ => SignedRatio.one) 0 2) SignedRatio.zero := by decide +kernel

/-- The interval subsolver computes an actual rational endpoint witness. -/
example : (match checkRationalInterval [⟨-1, 2, by decide⟩, SignedRatio.zero, ⟨2, 3, by decide⟩]
    [⟨3, 4, by decide⟩, SignedRatio.one] with
    | .feasible value _ _ => decide (value.num * 3 = 2 * (value.den : Int)) | _ => false) = true := by decide +kernel

example : (match checkRationalInterval [SignedRatio.one] [SignedRatio.zero] with
    | .infeasible _ _ _ _ _ => true | _ => false) = true := by decide +kernel

example : (match checkRationalInterval [] [⟨-2, 1, by decide⟩] with
    | .feasible value _ _ => decide (value.num = -2 * (value.den : Int)) | _ => false) = true := by decide +kernel

example : (match checkRationalInterval [⟨2, 4, by decide⟩] [⟨1, 2, by decide⟩] with
    | .feasible _ _ _ => true | _ => false) = true := by decide +kernel

example : (match checkRationalInterval [] [] with
    | .feasible value _ _ => decide (value.num = 0) | _ => false) = true := by decide +kernel

end Thesis.Examples.DistroPartialMoments
