import Thesis.Examples.ConditionalFailureActivationSelection
import Thesis.CausalTransport.HedgeChannelEnvironmentCovariance

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureActivationSelection

open Probability PathSpecification HedgeChannelInstallation
open HedgeChannelEnvironmentInstallation FiniteBooleanInteraction

/-!
# A full original countermodel with activation rows already inside Small

The graph/selection companion proves that the complete collider-trace union
lies inside the displayed hedge's Small forest.  Its outside-Small interaction
selection is consequently empty.  Here the installed signal still retains
*every* Small row once: `P`, `C xor Y`, and `Z xor C`.  Their combined phase
is `P xor Z xor Y`, which equals the original outcome bit on the original
conditioning cylinder fixing `X,P,Z` to false.

Exact finite coefficient conservation proves that identity over the whole
cube, including the original reserved roots.  The general covariance theorem
then supplies positive models on all three original labels, full observational
equality, and a gap for the unchanged conditional query.  No probability mass
enumeration, artificial shared switch, matched denominator, or proposed
Small/activation disjointness is used.  Keeping this semantic assembly
separate from the finite graph checks also keeps local verification capped.
This closes this genuine overlap instance, not the universal conditional leaf.
-/

/-- `C` reads its declared parent `Y`; `Z` reads its declared parent `C`.
The row at `P` still contributes its own bit.  All original reserved roots
remain in the environment, although this particular parity uses none. -/
def signalData : LinearSignal graph where
  parentMask := fun child parent => decide
    ((child = collider ∧ parent = outcome) ∨ (child = evidence ∧ parent = collider))
  rootMask := fun _ _ => false

def direction : Cube graph :=
  basisAssignment (pairRootCount graph.binary + signature.count) (Fin.natAdd (pairRootCount graph.binary) outcome)

private theorem observed_balance : forall coordinate,
    NodeSet.union query.action query.condition coordinate = false ->
    Bool.xor (LinearSignal.forestObservedCoefficient signalData witness.small coordinate)
        (cubeMask graph query.outcome (Fin.natAdd (pairRootCount graph.binary) coordinate)) =
      LinearSignal.selectedObservedCoefficient signalData outsideRows coordinate := by
  rw [outside_rows_empty]
  decide +kernel

private theorem root_balance : forall coordinate,
    Bool.xor (LinearSignal.forestRootCoefficient signalData witness.small coordinate)
        (cubeMask graph query.outcome (coordinate.castAdd signature.count)) =
      LinearSignal.selectedRootCoefficient signalData outsideRows coordinate := by
  rw [outside_rows_empty]
  decide +kernel

/-- The full original-cylinder identity comes from the local graph
conservation equations.  Only the tiny masks are checked: no main-prior
enumeration or normalized probability-gap premise is supplied. -/
def parityWitness : ConditionalParityWitness witness signalData signalData :=
  ConditionalParityWitness.ofConservation
    (outcomeMask := cubeMask graph query.outcome)
    (outcomeMask_member := by decide +kernel)
    (direction := direction)
    (direction_member := by apply (basisAssignment_member_iff _ _ _).mpr; decide +kernel)
    (outcome_odd := by change (maskPhase _ _).value (basisAssignment _ _) = true; rw [maskPhase_basis]; decide +kernel)
    (selected := outsideRows)
    (selected_outside_small := normal.activationTraceOutside_not_mandatory pivot.toRetained forest.toCutForest witness.small)
    (selected_avoids_action := normal.activationTraceOutside_action_free pivot.toRetained forest.toCutForest witness.small)
    (selected_even := by rw [outside_rows_empty]; intro _ impossible; cases impossible)
    (observed_balance := observed_balance)
    (root_balance := root_balance)

/-- A genuine positive, full-original-alphabet countermodel follows from
the same complete Small phase and pruned outside selection used above. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfParity witness rich signalData signalData parityWitness

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

end CurrentConditionalFailureActivationSelection
end Examples
end Causality
end Thesis
