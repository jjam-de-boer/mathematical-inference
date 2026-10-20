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
  | 0, _ => ⟨0, Nat.zero_lt_one⟩
  | 1, x => unsupportedCoarse x
  | _ + 2, x => predictionFine x

def stageMerge : (stage : Nat) → Fin (stageLabels (stage + 1)) → Fin (stageLabels stage)
  | 0, _ => ⟨0, Nat.zero_lt_one⟩
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
  by simpa only [Nat.zero_add] using finiteChain.prediction_error_sum partitionMomentObservable 0 2 (by decide)

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

def linearRow (first second : Int) (bound : SignedRatio) : RationalLinear.Inequality 2 :=
  ⟨fun i => if i.val = 0 then first else second, bound⟩

/-- x,y are nonnegative, x+y=1 and 1/4≤x≤1/3. Back-substitution
computes x=1/4 and y=3/4, without a denominator grid being supplied. -/
def feasibleLinearRows : List (RationalLinear.Inequality 2) :=
  [linearRow (-1) 0 SignedRatio.zero, linearRow 0 (-1) SignedRatio.zero,
    linearRow 1 1 SignedRatio.one, linearRow (-1) (-1) ⟨-1, 1, by decide⟩,
    linearRow 1 0 ⟨1, 3, by decide⟩, linearRow (-1) 0 ⟨-1, 4, by decide⟩]

example : (match RationalLinear.solve 2 feasibleLinearRows with
    | .feasible values _ => decide ((values 0).num * 4 = (values 0).den ∧
        (values 1).num * 4 = 3 * ((values 1).den : Int))
    | .infeasible _ => false) = true := by decide +kernel

/-- Incompatibility is discovered after projecting a genuinely coupled
system, rather than by inspecting an individually false constant input. -/
def impossibleLinearRows : List (RationalLinear.Inequality 2) :=
  [linearRow 1 1 ⟨1, 4, by decide⟩,
    linearRow (-1) (-1) ⟨-3, 4, by decide⟩]

example : (match RationalLinear.solve 2 impossibleLinearRows with
    | .infeasible _ => true | .feasible _ _ => false) = true := by decide +kernel

example : (match RationalLinear.solve 0 [] with
    | .feasible _ _ => true | .infeasible _ => false) = true := by decide +kernel

example : (match RationalLinear.solve 1 [⟨fun _ => -1, ⟨1, 1, by decide⟩⟩] with
    | .feasible values _ => decide ((values 0).num = -((values 0).den : Int)) | .infeasible _ => false) = true := by decide +kernel

/-- The public partial-moment interface constructs a fractional law from
one selected first moment, without a completed table or denominator cap. -/
def fractionalProblem := scalarPartialMomentProblem 1
  [factorialMomentInterval 1 ⟨1, 3, by decide⟩ ⟨1, 3, by decide⟩]

example : (match fractionalProblem.solve with
    | .feasible law => decide (QProb.Equiv (law.distro.pmf 0) ⟨2, 3, by decide⟩ ∧
        QProb.Equiv (law.distro.pmf 1) ⟨1, 3, by decide⟩)
    | .infeasible _ => false) = true := by decide +kernel

/-- Each specified moment lies within its individual range, but the two
cannot hold together: the second factorial moment forces all mass onto 2. -/
def incompatibleMomentProblem := scalarPartialMomentProblem 2
  [factorialMomentInterval 1 QProb.one QProb.one,
    factorialMomentInterval 2 (QProb.ofNat 2) (QProb.ofNat 2)]

example : (match incompatibleMomentProblem.solve with
    | .infeasible _ => true | .feasible _ => false) = true := by decide +kernel

/-- A zero-dimensional joint count vector still has its one-cell law. -/
def emptyJointProblem := jointPartialMomentProblem [] []

example : (match emptyJointProblem.solve with
    | .feasible law => decide (QProb.Equiv (law.distro.pmf []) QProb.one)
    | .infeasible _ => false) = true := by decide +kernel

/-- The rectangle includes a forced zero coordinate. The mixed moment
selects one of its two cells with a fractional mass. -/
def mixedProblem := jointPartialMomentProblem [0, 1]
  [mixedFactorialMomentInterval [0, 1] ⟨1, 2, by decide⟩ ⟨1, 2, by decide⟩]

example : (match mixedProblem.solve with
    | .feasible law => decide (QProb.Equiv (law.distro.pmf [0, 0]) ⟨1, 2, by decide⟩ ∧
        QProb.Equiv (law.distro.pmf [0, 1]) ⟨1, 2, by decide⟩)
    | .infeasible _ => false) = true := by decide +kernel

/-- A partial first moment does not determine the law. Optimization gives
0 and 1/2 for P(X=2), with compatible laws at both endpoints. -/
def ambiguousProblem := scalarPartialMomentProblem 2
  [factorialMomentInterval 1 QProb.one QProb.one]

example : (match ambiguousProblem.solveEventBounds (fun x => decide (x = 2)) with
    | .bounded bounds => decide (SignedRatio.Equiv bounds.lower SignedRatio.zero ∧
        SignedRatio.Equiv bounds.upper ⟨1, 2, by decide⟩ ∧
        QProb.Equiv (bounds.lowerLaw.distro.pmf 1) QProb.one ∧
        QProb.Equiv (bounds.upperLaw.distro.pmf 0) ⟨1, 2, by decide⟩ ∧
        QProb.Equiv (bounds.upperLaw.distro.pmf 2) ⟨1, 2, by decide⟩)
    | .infeasible _ => false) = true := by decide +kernel

example : (match incompatibleMomentProblem.solveBounds (fun x => (x : Int)) with
    | .infeasible _ => true | .bounded _ => false) = true := by decide +kernel

/-- Genuine interval input leaves a range of laws, and each rational
endpoint is attained by a constructed probability record. -/
def intervalProblem := scalarPartialMomentProblem 1
  [factorialMomentInterval 1 ⟨1, 3, by decide⟩ ⟨2, 3, by decide⟩]

example : (match intervalProblem.solveBounds (fun x => (x : Int)) with
    | .bounded bounds => decide (SignedRatio.Equiv bounds.lower ⟨1, 3, by decide⟩ ∧
        SignedRatio.Equiv bounds.upper ⟨2, 3, by decide⟩)
    | .infeasible _ => false) = true := by decide +kernel

/-- The original retained null outcome 99 is outside the declared grid,
yet the necessity/completeness direction accepts its unchanged law. -/
example : (match (scalarPartialMomentProblem 3 []).solve with | .feasible _ => True | .infeasible _ => False) := by
  apply ((scalarPartialMomentProblem 3 []).solve_success_iff).mpr
  refine ⟨partitionMomentFixture, by decide +kernel, ?_⟩
  intro constraint member
  exact False.elim (List.not_mem_nil member)

end Thesis.Examples.DistroPartialMoments
