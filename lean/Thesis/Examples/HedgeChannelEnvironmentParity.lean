import Thesis.Examples.HedgeChannelEnvironment
import Thesis.CausalTransport.HedgeChannelEnvironmentCovariance

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelEnvironmentParity

open Probability
open FiniteBooleanInteraction
open HedgeChannelLatentBoundary
open HedgeChannelEnvironmentInstallation
open HedgeChannelEnvironment (readoutRoot)

/-!
# A shared-latent countermodel from parity, without mass enumeration

The original three-valued query remains `P(U | do(A), R)` on the graph
`A -> R`, `A <-> R`, `U <-> R`.  The older fixture computes its complete
event masses independently.  Here the general covariance constructor is
exercised instead: `R` and `U` read their actual common reserved root, and
the explicit direction toggles that root together with `U`.

Only the small finite mask, incidence, support and free-coordinate tests are
decided.  The actual row phases are `R xor L` and `U xor L`, where `L` is
their genuine common reserved bit.  Conditioning fixes `R` to false; checking
each free coordinate establishes the needed coefficient balance.  The general
homogeneous-phase basis theorem proves matching for *every* supported cube
point, and derives small-phase oddness from the other parity data.  Neither
a large main-prior enumeration nor a proposed positive integral is supplied.
The resulting positive pair has the full original alphabet and unchanged query.

This verifies a nonempty instance of the graph-facing parity obligation.
It does not infer arbitrary terminal-path coverage from this one-edge case.
-/

/-- Only the small row at `R` reads its genuine incident `U <-> R` bit. -/
def smallData : LinearSignal graph where
  parentMask := fun _ _ => false
  rootMask := fun child root => decide (child = rootNode ∧ root = readoutRoot)

/-- Only the background row at `U` reads the same genuine incident bit. -/
def backgroundData : LinearSignal graph where
  parentMask := fun _ _ => false
  rootMask := fun child root => decide (child = outcomeNode ∧ root = readoutRoot)

/-- Toggle the actual reserved root and `U`, keeping the forced action and
conditioner false.  The other original pair-root bit is not identified with
this root or removed from the environment support. -/
def direction : Cube graph := joinCube graph
  (fun root => decide (root = readoutRoot))
  (fun child => decide (child = outcomeNode))

/-- `U` is the only free observed coordinate, and contributes once through
the outcome mask and once through its selected background row.  Fixed `A`
and `R` are excluded by the original conditioning mask, not by deleting their
actual rows.  These are finite local graph-mask equations, not likelihoods. -/
private theorem observed_balance : forall coordinate,
    NodeSet.union query.action query.condition coordinate = false ->
    Bool.xor (LinearSignal.forestObservedCoefficient smallData witness.small coordinate)
        (cubeMask graph query.outcome (Fin.natAdd (pairRootCount graph.binary) coordinate)) =
      LinearSignal.selectedObservedCoefficient backgroundData (NodeSet.singleton outcomeNode) coordinate := by
  decide +kernel

/-- The original `U <-> R` root contributes once on each side; the other
original root contributes zero on each side.  Both roots remain in the
environment and are checked, rather than identified or removed. -/
private theorem root_balance : forall coordinate,
    Bool.xor (LinearSignal.forestRootCoefficient smallData witness.small coordinate)
        (cubeMask graph query.outcome (coordinate.castAdd signature.count)) =
      LinearSignal.selectedRootCoefficient backgroundData (NodeSet.singleton outcomeNode) coordinate := by
  decide +kernel

/-- The conditioner `R` is deliberately not balanced as a globally free
coordinate.  Its bit is fixed on the original cylinder, so the constructive
whole-cylinder theorem does not impose this stronger, incorrect requirement. -/
theorem conditioned_root_not_globally_balanced :
    Bool.xor (LinearSignal.forestObservedCoefficient smallData witness.small rootNode)
        (cubeMask graph query.outcome (Fin.natAdd (pairRootCount graph.binary) rootNode)) ≠
      LinearSignal.selectedObservedCoefficient backgroundData (NodeSet.singleton outcomeNode) rootNode := by
  decide +kernel

/-- All finite parity fields are proved for the actual locally installed
signals; no event-mass or countermodel-separation premise is used. -/
def parityWitness : ConditionalParityWitness witness smallData backgroundData :=
  ConditionalParityWitness.ofConservation (w := witness) (small := smallData) (background := backgroundData)
    (outcomeMask := cubeMask graph query.outcome)
    (outcomeMask_member := by decide +kernel)
    (direction := direction)
    (direction_member := by decide +kernel)
    (outcome_odd := by decide +kernel)
    (selected := NodeSet.singleton outcomeNode)
    (selected_outside_small := by decide +kernel)
    (selected_avoids_action := by decide +kernel)
    (selected_even := by decide +kernel)
    (observed_balance := observed_balance)
    (root_balance := root_balance)

/-- A positive full-original-alphabet pair from the general parity theorem,
without computing its potentially large complete likelihood numerators. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfParity (S := signature) (G := graph) (query := query)
    witness rich smallData backgroundData parityWitness

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

end HedgeChannelEnvironmentParity
end Examples
end Causality
end Thesis
