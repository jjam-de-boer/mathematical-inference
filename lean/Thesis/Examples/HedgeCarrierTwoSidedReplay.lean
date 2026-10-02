import Thesis.CausalTransport.HedgeCarrierTwoSidedReplay
import Thesis.Examples.HedgeCarrierRouteObstruction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeCarrierOuterReplay

open Probability
open HedgeCarrierRouteObstruction

/-!
# Actual two-sided replay at a free outer-only re-entry vertex

Use the seven-node obstruction, with kept chain `A → V → B → Q` and
small roots `R,Q`.  Unlike the negative action-overwrite regression, the
updated vertex `V` is not an action.  It belongs to the large forest but
not the small forest, and a routed signal genuinely needs to visit it.

Both original carriers have an explicit all-first latent realization with
the same full retained state.  Toggle `V` at the represented fresh input.
The kept child `B` responds on both sides.  Its child `Q` responds only on
the large side: the nested equation at `Q` omits the outer parent `B`.
The two exact replays therefore disagree even on a state that has positive
probability under the actual common retained-state law.

This is a check of mechanism response, not a substitute for a probability
comparison.  Unequal pointwise replays need not have unequal pushforward
laws.  In particular, the example does not rule out a nontrivial state-law
recoding or another countermodel family.  It rules out silently extending
the old *common pointwise replay* by deleting its geometric hypothesis.
The public evaluation theorems below also check arbitrary interventions
against the actual installed SCMs, rather than only a hand-computed signal.

The repeated-instruction checks use two different supplied bits at `V`.
They distinguish the new occurrence encoding from a node-indexed family,
and instantiate the exact fully averaged event law without a pivot-
distinctness premise.  No full observational equality is asserted for this
outer-only plan; its necessary-and-sufficient comparison remains explicit.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := fun _ => (by decide : (⟨0, by decide⟩ : Fin 3) ≠ ⟨1, by decide⟩)

/-- A supported biased input, with weight two for no flip and one for a
flip.  The regression uses the actual `true` input, not a zero-weight unit. -/
def noise : FiniteProbRecord Bool := ⟨[(false, 2), (true, 1)], 3, by decide, rfl⟩

private theorem noise_positive (bit : Bool) :
    noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  cases bit <;> decide +kernel

/-- Keep the original `V` bit and XOR the fresh input.  Even this simple
update has responding descendants; it is not a coordinate-only map. -/
def outerStep : HedgeReadoutStep signature :=
  ⟨outerReentry, noise, true, fun _ => false⟩

def plan : List (HedgeReadoutStep signature) := [outerStep]

def freshInputs : Fin signature.count -> Bool := fun _ => true

theorem pivot_free_outer :
    query.action outerReentry = false ∧ witness.large outerReentry = true ∧
      witness.small outerReentry = false := by decide +kernel

/-- The parent maps really differ at `Q`.  Neither side has discarded the
kept `V → B` response at the outer row `B`. -/
theorem responding_parent_maps :
    witness.carrierParentMap false secondAction outerReentry = some secondAction ∧
      witness.carrierParentMap true secondAction outerReentry = some secondAction ∧
      witness.carrierParentMap false lastRoot secondAction = some lastRoot ∧
      witness.carrierParentMap true lastRoot secondAction = none := by decide +kernel

def factual : signature.Assignment := fun node => rich.first node

def backgrounds : HedgePrivateCoordinates signature :=
  fun node => ⟨0, hedgePrivateCard_pos signature node⟩

def state : HedgeCarrierObservedState signature := (factual, (backgrounds, false))

/-- This is an actual typed latent assignment, including every unused
pair coordinate and private background, not an existentially selected unit. -/
def oldUnit (nested : Bool) :
    (witness.carrierDefectParityModelFor rich nested).latent.Assignment := by
  cases nested <;> exact hedgeDefectLatentDefault graph

/-- Both actual originals realize the same complete state, so the replay
discrepancy below cannot be dismissed as unreachable input data. -/
theorem retained_state_realized (nested : Bool) :
    witness.carrierRetainedState rich nested (oldUnit nested) = state := by
  cases nested <;> decide +kernel

/-- The realized state even has strictly positive probability.  We use
singleton positivity of the real defect prior and event inclusion, avoiding
enumeration of the entire seven-node probability table. -/
theorem retained_state_positive :
    (witness.carrierRetainedStateDist rich).EventPositive
      (FiniteProbRecord.singletonEvent state) := by
  have included : forall unit,
      FiniteProbRecord.singletonEvent (oldUnit false) unit = true ->
      FiniteProbRecord.singletonEvent state
        (witness.carrierRetainedState rich false unit) = true := by
    intro unit singleton
    have same : unit = oldUnit false := of_decide_eq_true singleton
    subst unit
    rw [retained_state_realized]
    exact decide_eq_true rfl
  have monotone := FiniteProbRecord.eventMass_mono
    (witness.carrierDefectParityModelFor rich false).prior.atoms
    (FiniteProbRecord.singletonEvent (oldUnit false))
    (fun unit => FiniteProbRecord.singletonEvent state
      (witness.carrierRetainedState rich false unit)) included
  have positive : 0 < FiniteProbRecord.eventMass
      (witness.carrierDefectParityModelFor rich false).prior.atoms
      (FiniteProbRecord.singletonEvent (oldUnit false)) :=
    hedgeDefectPrior_singleton_mass_pos graph (oldUnit false)
  have pushed := Nat.lt_of_lt_of_le positive monotone
  simpa only [HedgeWitness.carrierRetainedStateDist, FiniteProbRecord.EventPositive,
    FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels,
    HedgeWitness.carrierDefectParityModelFor, Bool.false_eq_true, if_false,
    HedgeWitness.carrierRetainedState] using pushed

def replay (nested : Bool) : signature.Assignment :=
  witness.carrierPlanReplay rich nested state plan freshInputs
    (FiniteLatentSCM.noIntervention signature)

/-- The free pivot and its outer kept child change on both sides.  At the
small root `Q`, only the large equation propagates the changed outer input.
All comparisons retain full three-valued observations, not merely parities. -/
theorem replay_coordinates :
    replay false outerReentry = rich.second outerReentry ∧
      replay true outerReentry = rich.second outerReentry ∧
      replay false secondAction = rich.second secondAction ∧
      replay true secondAction = rich.second secondAction ∧
      replay false lastRoot = rich.second lastRoot ∧
      replay true lastRoot = rich.first lastRoot := by decide +kernel

theorem replays_differ : replay false ≠ replay true := by
  intro same
  have coordinate := congrFun same lastRoot
  have checked := replay_coordinates
  rw [checked.2.2.2.2.1, checked.2.2.2.2.2] at coordinate
  exact rich.different lastRoot coordinate.symm

/-- Exact evaluation on either installed SCM, for arbitrary interventions
and supplied original units.  No small-membership condition is supplied. -/
theorem actual_eval_eq_replay (nested : Bool)
    (intervention : (node : Fin signature.count) -> Option (signature.Value node))
    (unit : (witness.carrierDefectParityModelFor rich nested).latent.Assignment) :
    ((witness.carrierDefectParityModelFor rich nested).withHedgeReadouts rich plan).evalUnder
        intervention
        ((witness.carrierDefectParityModelFor rich nested).hedgeReadoutAssignment
          rich freshInputs plan unit) =
      witness.carrierPlanReplay rich nested (witness.carrierRetainedState rich nested unit)
        plan freshInputs intervention :=
  witness.carrierDefectParityModelFor_withHedgeReadouts_evalUnder_eq_replay
    rich nested plan freshInputs intervention unit

/-- The unequal outputs are evaluations of the real augmented mechanisms.
The two original units have the same retained state, but their responding
descendants do not admit one shared pointwise update. -/
theorem actual_factual_eval_eq_replay (nested : Bool) :
    ((witness.carrierDefectParityModelFor rich nested).withHedgeReadouts rich plan).eval
        ((witness.carrierDefectParityModelFor rich nested).hedgeReadoutAssignment
          rich freshInputs plan (oldUnit nested)) = replay nested := by
  have actual := actual_eval_eq_replay nested
    (FiniteLatentSCM.noIntervention signature) (oldUnit nested)
  rw [retained_state_realized] at actual
  exact actual

/-- Full observational events on either side have exactly the stated
replay pushforward at these fixed inputs.  This regression intentionally
does not assert equality of the two different pushforwards. -/
theorem actual_event_eq_replay (nested : Bool) (event : Event signature.Assignment) :
    QProb.Equiv
      ((witness.carrierDefectParityModelFor rich nested).prior.probVal (fun unit => event
        (((witness.carrierDefectParityModelFor rich nested).withHedgeReadouts rich plan).eval
          ((witness.carrierDefectParityModelFor rich nested).hedgeReadoutAssignment
            rich freshInputs plan unit))))
      ((witness.carrierRetainedStateDist rich).probVal (fun retained => event
        (witness.carrierPlanReplay rich nested retained plan freshInputs
          (FiniteLatentSCM.noIntervention signature)))) :=
  witness.carrierDefectParityModelFor_withHedgeReadouts_encodedEvent_probVal_equiv_replay
    rich nested plan freshInputs (FiniteLatentSCM.noIntervention signature) event

/-- Both actual installed models remain in the intended positive graph
class.  Their different pointwise responses are not a compatibility or
support failure, and membership alone does not imply observational equality. -/
theorem updated_mem (nested : Bool) :
    (GraphModelClass.positive graph).Mem
      ((witness.carrierDefectParityModelFor rich nested).withHedgeReadouts rich plan) := by
  have compatible : Compatible (witness.carrierDefectParityModelFor rich nested) graph := by
    cases nested
    · exact witness.largeCarrierDefectParityModel_compatible rich
    · exact witness.smallCarrierDefectParityModel_compatible rich
  have positive : ObservationallyPositive (witness.carrierDefectParityModelFor rich nested) := by
    cases nested
    · exact witness.largeCarrierDefectParityModel_positive rich
    · exact witness.smallCarrierDefectParityModel_positive rich
  refine ⟨FiniteLatentSCM.withHedgeReadouts_compatible _ compatible rich plan,
    FiniteLatentSCM.withHedgeReadouts_positive _ positive rich plan ?_⟩
  intro step listed bit
  have same : step = outerStep := List.mem_singleton.mp listed
  subst step
  exact noise_positive bit

/-! ## Repeated pivots retain genuinely independent occurrence inputs -/

def repeatedPlan : List (HedgeReadoutStep signature) := [outerStep, outerStep]

/-- Install no flip first and a flip second.  The tail-first tuple convention
stores the head bit in `.2` and the second instruction's bit in `.1.2`. -/
def independentInputs : HedgeReadoutInputs.Inputs repeatedPlan := (((), true), false)

theorem independent_input_mass :
    FiniteProbRecord.eventMass (HedgeReadoutInputs.distribution repeatedPlan).atoms
        (fun inputs => !inputs.2 && inputs.1.2) = 2 ∧
      (HedgeReadoutInputs.distribution repeatedPlan).den = 9 := by decide +kernel

def independentReplay (nested : Bool) : signature.Assignment :=
  witness.carrierPlanReplayWithInputs rich nested state repeatedPlan independentInputs
    (FiniteLatentSCM.noIntervention signature)

/-- The two distinct occurrence bits flip the pivot once.  Reusing the
node-indexed `true` bit at both instructions flips it twice instead.  This
guards against using the earlier repeated-bit representation as an encoding
of every actual independent unit. -/
theorem occurrence_encoding_not_node_encoding :
    independentReplay false outerReentry = rich.second outerReentry ∧
      witness.carrierPlanReplay rich false state repeatedPlan freshInputs
        (FiniteLatentSCM.noIntervention signature) outerReentry = rich.first outerReentry := by
  decide +kernel

theorem actual_independent_eval_eq_replay (nested : Bool) :
    ((witness.carrierDefectParityModelFor rich nested).withHedgeReadouts rich repeatedPlan).eval
        ((witness.carrierDefectParityModelFor rich nested).hedgeReadoutAssignmentWithInputs
          rich repeatedPlan independentInputs (oldUnit nested)) = independentReplay nested := by
  have actual := witness.carrierDefectParityModelFor_withHedgeReadouts_evalUnderWithInputs_eq_replay
    rich nested repeatedPlan independentInputs (FiniteLatentSCM.noIntervention signature) (oldUnit nested)
  rw [retained_state_realized] at actual
  exact actual

/-- This compares the whole actual final prior with the full mixture, not
the old prior at one fixed fresh-input slice.  Repeated pivots have separate
factors and no hypothesis of slice-by-slice equality is needed. -/
theorem actual_repeated_event_eq_replayDist (nested : Bool) (event : Event signature.Assignment) :
    QProb.Equiv
      (((witness.carrierDefectParityModelFor rich nested).withHedgeReadouts rich repeatedPlan).prior.probVal
        (fun unit => event
          (((witness.carrierDefectParityModelFor rich nested).withHedgeReadouts rich repeatedPlan).eval unit)))
      ((witness.carrierReplayDist rich nested repeatedPlan (FiniteLatentSCM.noIntervention signature)).probVal event) :=
  witness.carrierDefectParityModelFor_withHedgeReadouts_event_probVal_equiv_replayDist
    rich nested repeatedPlan (FiniteLatentSCM.noIntervention signature) event

/-- Equality of the fully averaged replay laws is precisely the remaining
observational comparison, also for this repeated outer-only plan.  The iff
does not assert either side and is not a universal hedge countermodel. -/
theorem repeated_observational_comparison :
    ObservationallyEquivalent
      ((witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich repeatedPlan)
      ((witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich repeatedPlan) ↔
    forall event : Event signature.Assignment, QProb.Equiv
      ((witness.carrierReplayDist rich false repeatedPlan (FiniteLatentSCM.noIntervention signature)).probVal event)
      ((witness.carrierReplayDist rich true repeatedPlan (FiniteLatentSCM.noIntervention signature)).probVal event) :=
  witness.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_iff_replayDist rich repeatedPlan

end HedgeCarrierOuterReplay
end Examples
end Causality
end Thesis
