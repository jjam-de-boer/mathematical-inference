import Thesis.CausalTransport.CausalAbstractionOrbits
import Thesis.Examples.CausalScaleSelection

/-!
# Exchangeable AND parents and a symmetry-breaking experiment

Swapping the two root nodes also swaps their complete response tables
and hard settings. Observation and forcing both roots permit the swap.
A setting of the first parent alone destroys the checked row symmetry.
Even with symmetric measurements, a query specifically about one parent
removes the swap from its own stabilizer.
-/

namespace Thesis.Examples.CausalAbstractionOrbits

open Probability Probability.Distros Causality
open Causality.CausalAbstractionInverse Causality.FiniteSymmetry Causality.ResponseOrbitReduction
open Causality.CausalScaleSelection Causality.ModelDescriptionCost
open Causality.CausalAbstractionSynthesis (interventions interventions_complete)
open Thesis.Examples.CausalAbstractionInverse
open Thesis.Examples.CausalScaleSelection

def swapNode (node : Fin 2) : Fin 2 := if node.val = 0 then 1 else 0

private theorem swapNode_twice : ∀ node, swapNode (swapNode node) = node := by decide +kernel

def swapTable (table : SharedResponse.Table fine) : SharedResponse.Table fine :=
  fun node => table (swapNode node)

def swapSetting (setting : HardIntervention fine) : HardIntervention fine :=
  ⟨fun node => setting.value (swapNode node)⟩

def rootSwap : Action bitGroup (SharedResponse.Table fine) where
  act swap table := bif (show Bool from swap) then swapTable table else table
  one_act _ := rfl
  mul_act g h table := by
    cases g <;> cases h
    · rfl
    · rfl
    · rfl
    · funext node
      change table node = table (swapNode (swapNode node))
      rw [swapNode_twice]

private theorem swapEvaluationCheck :
    ∀ table ∈ SharedResponse.enumeration fine, ∀ setting ∈ interventions fine, ∀ node : Fin 2,
      SharedResponse.eval fine (swapSetting setting).value (swapTable table) node =
        SharedResponse.eval fine setting.value table (swapNode node) := by
  decide +kernel

/-- This is an actual permutation of intervention responses, with the
setting carried along, including all unfixed roots. -/
theorem swap_evaluates (table : SharedResponse.Table fine) (setting : HardIntervention fine)
    (node : Fin 2) :
    SharedResponse.eval fine (swapSetting setting).value (swapTable table) node =
      SharedResponse.eval fine setting.value table (swapNode node) :=
  swapEvaluationCheck table (SharedResponse.enumeration_complete _ _) setting
    (interventions_complete _ _) node

def eitherRoot : EventQuery fine :=
  .intervention (.empty fine) (fun state => state (0 : Fin 2) || state (1 : Fin 2))

def neitherRoot : EventQuery fine :=
  .intervention (.empty fine) (fun state => !(state (0 : Fin 2) || state (1 : Fin 2)))

def symmetric := spec.orbitReduction rootSwap [eitherRoot.onTable]
def broken := singlesOutFirst.orbitReduction rootSwap [eitherRoot.onTable]
def movedQuery := spec.orbitReduction rootSwap [firstRoot.onTable]

theorem swap_retained : symmetric.Fixes true := by decide +kernel
theorem swap_excluded_by_experiment : ¬ broken.Fixes true := by decide +kernel
theorem swap_excluded_by_query : ¬ movedQuery.Fixes true := by decide +kernel

def sizes (scale : Specification fine compactSignature) : Nat × Nat × Nat × Nat :=
  let reduced := scale.orbitReduction rootSwap [eitherRoot.onTable]
  (scale.problem.cells.length, reduced.problem.cells.length,
    scale.problem.rows.length, reduced.problem.rows.length)

theorem solver_sizes :
    sizes spec = (4, 3, 14, 13) ∧ sizes singlesOutFirst = (4, 4, 18, 18) := by
  decide +kernel

private def correctEitherRange (scale : Specification fine compactSignature)
    (result : scale.QueryResult eitherRoot) : Bool :=
  match result with
  | .interval _ sharp _ =>
    decide (SignedRatio.Equiv sharp.lower ⟨1, 4, by decide⟩ ∧ SignedRatio.Equiv sharp.upper .one ∧
      QProb.Equiv (eitherRoot.value sharp.lowerModel) ⟨1, 4, by decide⟩ ∧
      QProb.Equiv (eitherRoot.value sharp.upperModel) QProb.one)
  | _ => false

def both_orbit_ranges : Bool :=
  correctEitherRange spec (spec.solveQueryWithOrbits rootSwap eitherRoot) &&
    correctEitherRange singlesOutFirst (singlesOutFirst.solveQueryWithOrbits rootSwap eitherRoot)

#guard both_orbit_ranges

def broken_orbit_distinguishes_parents : Bool :=
  (match singlesOutFirst.solveQueryWithOrbits rootSwap secondRoot with
  | .point _ sharp _ => decide (SignedRatio.Equiv sharp.lower ⟨1, 4, by decide⟩)
  | _ => false) &&
  (match singlesOutFirst.solveQueryWithOrbits rootSwap firstRoot with
  | .interval _ sharp _ => decide (SignedRatio.Equiv sharp.lower ⟨1, 4, by decide⟩ ∧
      SignedRatio.Equiv sharp.upper .one)
  | _ => false)

#guard broken_orbit_distinguishes_parents

/-- The reduction keeps a compatible null-evidence model as well as
the supported zero answer. -/
def conditional_has_mixed_support : Bool :=
  match spec.solveConditionalWithOrbits rootSwap neitherRoot observedBothTrue with
  | .supported _ sharp (.possible ..) =>
      decide ((sharp.lower.value observedBothTrue).num = 0 ∧ (sharp.upper.value observedBothTrue).num = 0)
  | _ => false

#guard conditional_has_mixed_support

/-- Values of the queried event outside the conditioning event do not
restrict the stabilizer. The first-root query moves, but its intersection
with the evidence is the symmetric AND event. -/
theorem joint_numerator_retains_swap :
    (spec.orbitReduction rootSwap [observedBothTrue.onTable,
      fun table => observedBothTrue.onTable table && firstRoot.onTable table]).Fixes true := by
  decide +kernel

end Thesis.Examples.CausalAbstractionOrbits
