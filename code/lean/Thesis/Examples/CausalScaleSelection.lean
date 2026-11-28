import Thesis.CausalTransport.CausalScaleSelection
import Thesis.CausalTransport.ModelDescriptionCost
import Thesis.Examples.CausalAbstractionInverse

/-!
# Select a scale for the AND merge

The first candidate only measures observation. The second also admits
the required experiment forcing both parents true. The third uses one more
fine experiment, forcing only the first parent true, with the same recorded
AND law as in observation. The additional law identifies the second
parent's probability, while the first parent's probability still ranges
from one quarter to one.
-/

namespace Thesis.Examples.CausalScaleSelection

open Probability Probability.Distros Causality
open Causality.CausalAbstractionInverse Causality.CausalScaleSelection Causality.ModelDescriptionCost
open Causality.CausalAbstractionSynthesis (interventionDecidableEq)
open Thesis.Examples.CausalAbstractionInverse hiding observed
open Thesis.Examples.CausalAbstractionSynthesis (compactSignature compactDoTrue)

def forceFirst : HardIntervention fine :=
  (HardIntervention.empty fine).set (0 : Fin 2) true

def observeOnly : Specification fine compactSignature :=
  { spec with
    omega := fun action => if action = .empty fine then some (.empty compactSignature) else none
    required := [.empty compactSignature]
    measurements := [⟨.empty compactSignature, Thesis.Examples.CausalAbstractionInverse.observed⟩] }

def singlesOutFirst : Specification fine compactSignature :=
  { spec with omega := fun action =>
      if action = forceFirst then some (.empty compactSignature)
      else spec.omega action }

def secondRoot : EventQuery fine :=
  .intervention (.empty fine) (fun state => state (1 : Fin 2))

def firstRoot : EventQuery fine :=
  .intervention (.empty fine) (fun state => state (0 : Fin 2))

def bothRootAnswersAfter : Bool :=
    (match singlesOutFirst.solveQuery secondRoot with
      | .point _ sharp _ => decide (SignedRatio.Equiv sharp.lower ⟨1, 4, by decide⟩)
      | _ => false) &&
    (match singlesOutFirst.solveQuery firstRoot with
      | .interval _ sharp _ =>
          decide (SignedRatio.Equiv sharp.lower ⟨1, 4, by decide⟩ ∧ SignedRatio.Equiv sharp.upper .one)
      | _ => false)

#guard bothRootAnswersAfter

private def macroLayout : Layout 1 1 where
  values _ := 2
  latentValues _ := 2
  incident _ _ := true
  directed _ _ := false

private def macroLabels : FiniteWitness compactSignature.Assignment :=
  FiniteWitness.ofList compactSignature.assignmentEnumeration
    compactSignature.assignmentEnumeration_complete compactSignature.assignmentEnumeration_nodup

/-- Count the dense macro layout and record one rational-law description
per admitted measured fine experiment, including an additional experiment
that shares the same coarse tag. -/
def priced (scale : Specification fine compactSignature) : Candidate fine where
  coarse := compactSignature
  specification := scale
  cost := macroLayout.cost +
    (scale.comparisons.map (fun pair => distributionCost macroLabels ⟨pair.2.law⟩)).sum

def workload : Workload fine where
  requiredExperiments := [.empty fine, bothForced]
  requests := [.event secondRoot .zero]

def observationOnlyMissesRequired : Bool :=
    (match (priced observeOnly).check workload with
    | .fail (.missingExperiment action _ _) => decide (action = bothForced)
    | _ => false)

#guard observationOnlyMissesRequired

def originalQueryTooWide : Bool :=
    (match (priced spec).check workload with
    | .fail (.query _ _ (.tooWide lower upper) _) =>
        decide (SignedRatio.Equiv lower ⟨1, 4, by decide⟩ ∧ SignedRatio.Equiv upper .one)
    | _ => false)

#guard originalQueryTooWide

def candidates : List (Candidate fine) := [priced observeOnly, priced spec, priced singlesOutFirst]

def selection : Selection workload candidates := select workload candidates

def winnerCost : Option Nat :=
  match selection with
  | .none _ => none
  | .best winner _ _ _ => some winner.cost

#guard (priced observeOnly).cost == 16 && (priced spec).cost == 22 &&
      (priced singlesOutFirst).cost == 33 && winnerCost == some 33

/-- The support setting is consequential even for a zero-width conditional
range. The same candidate fails if all compatible models must support it. -/
def conditionalSupportPolicy : Bool :=
    (match (priced spec).check ⟨[], [.conditional firstFalse observedBothTrue .zero true]⟩ with
    | .pass _ => true
    | _ => false) &&
    (match (priced spec).check ⟨[], [.conditional firstFalse observedBothTrue .zero false]⟩ with
    | .fail (.query _ _ .sometimesUndefined _) => true
    | _ => false)

#guard conditionalSupportPolicy

end Thesis.Examples.CausalScaleSelection
