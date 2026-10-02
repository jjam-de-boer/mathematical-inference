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

Unequal pointwise replays alone would not separate the laws.  The probability
argument below therefore uses the actual defect marginal and integrates the
independent fresh factor.  The root event has probability `4/9` on the large
side and `1/3` on the nested side.  Consequently this particular noisy update
does not preserve full observational equality and cannot admit a probability-
preserving joint input/state recoding, even one mixing fresh inputs with state.

That negative conclusion concerns this stated plan, not every possible
outer-only routing construction or another countermodel family.  It rules
out silently extending the old common replay, or claiming that averaging
necessarily repairs it.  The public evaluation theorems also check arbitrary
interventions against the real installed SCMs rather than an isolated signal.

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

/-- The same mechanism update with an arbitrary stated private-noise law.
Changing this factor changes probabilities, but not the encoded response at
a given supplied bit.  The general obstruction below quantifies over it. -/
def planWithNoise (freshNoise : FiniteProbRecord Bool) : List (HedgeReadoutStep signature) :=
  [⟨outerReentry, freshNoise, true, fun _ => false⟩]

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

/-! ## The supported noise mixture does not repair this particular update -/

private def replayAt (nested : Bool) (retained : HedgeCarrierObservedState signature)
    (bit : Bool) : signature.Assignment :=
  witness.carrierPlanReplayWithInputs rich nested retained plan ((), bit)
    (FiniteLatentSCM.noIntervention signature)

private def oldBit (retained : HedgeCarrierObservedState signature) (node : Fin signature.count) : Bool :=
  hedgeIsSecond rich node (retained.1 node)

private theorem incoming_firstAction (nested : Bool) (parents : signature.ParentValues firstAction) :
    hedgeForestParentBitsFrom rich (witness.carrierParentMap nested firstAction) firstAction parents = false := by
  cases nested <;> rfl

private theorem incoming_firstRoot (nested : Bool) (parents : signature.ParentValues firstRoot) :
    hedgeForestParentBitsFrom rich (witness.carrierParentMap nested firstRoot) firstRoot parents = false := by
  cases nested <;> rfl

private theorem incoming_outerReentry (nested : Bool) (parents : signature.ParentValues outerReentry) :
    hedgeForestParentBitsFrom rich (witness.carrierParentMap nested outerReentry) outerReentry parents =
      hedgeIsSecond rich firstAction (parents firstAction (by decide +kernel)) := by
  cases nested <;> exact Bool.false_xor _

private theorem incoming_secondAction (nested : Bool) (parents : signature.ParentValues secondAction) :
    hedgeForestParentBitsFrom rich (witness.carrierParentMap nested secondAction) secondAction parents =
      hedgeIsSecond rich outerReentry (parents outerReentry (by decide +kernel)) := by
  cases nested <;> exact Bool.false_xor _

private theorem incoming_lastRoot (nested : Bool) (parents : signature.ParentValues lastRoot) :
    hedgeForestParentBitsFrom rich (witness.carrierParentMap nested lastRoot) lastRoot parents =
      if nested then false else hedgeIsSecond rich secondAction (parents secondAction (by decide +kernel)) := by
  cases nested
  · exact Bool.false_xor _
  · rfl

/-- Keep the factual and responding parent terms explicit before cancelling
them.  Background labels disappear only through the proved carrier inverse
law, so this identity is valid on arbitrary retained states. -/
private theorem replayAt_bit (nested : Bool) (retained : HedgeCarrierObservedState signature)
    (bit : Bool) (node : Fin signature.count) (inside : witness.large node = true) :
    hedgeIsSecond rich node (replayAt nested retained bit node) =
      Bool.xor
        (Bool.xor
          (Bool.xor (oldBit retained node)
            (hedgeForestParentBitsFrom rich (witness.carrierParentMap nested node) node
              (fun parent _edge => retained.1 parent)))
          (hedgeForestParentBitsFrom rich (witness.carrierParentMap nested node) node
            (fun parent _edge => replayAt nested retained bit parent)))
        (if node = outerReentry then bit else false) := by
  change hedgeIsSecond rich node
      (witness.carrierPlanReplayNodeWithInputs rich nested retained plan ((), bit)
        (FiniteLatentSCM.noIntervention signature) node) = _
  rw [HedgeWitness.carrierPlanReplayNodeWithInputs]
  simp only [FiniteLatentSCM.noIntervention]
  let parents : signature.ParentValues node := fun parent _edge => replayAt nested retained bit parent
  change hedgeIsSecond rich node
      (HedgeReadoutInputs.response rich node parents plan ((), bit)
        (witness.carrierRetainedResponse rich nested retained node parents)) = _
  have baseBit : hedgeIsSecond rich node (witness.carrierRetainedResponse rich nested retained node parents) =
      Bool.xor
        (Bool.xor (oldBit retained node)
          (hedgeForestParentBitsFrom rich (witness.carrierParentMap nested node) node
            (fun parent _edge => retained.1 parent)))
        (hedgeForestParentBitsFrom rich (witness.carrierParentMap nested node) node parents) := by
    simp only [HedgeWitness.carrierRetainedResponse, inside, if_true, hedgeIsSecond_parityCarrierValue]
    rfl
  by_cases same : node = outerReentry
  · subst node
    simp only [plan, outerStep, HedgeReadoutInputs.response, HedgeReadoutStep.responseAt, dite_true,
      hedgeNoisyReadout, if_true, Bool.xor_false, hedgeIsSecond_parityCarrierValue, baseBit, parents]
  · simp only [plan, outerStep, HedgeReadoutInputs.response, HedgeReadoutStep.responseAt, dif_neg same,
    if_neg same, baseBit, Bool.xor_false]
    rfl

private theorem replayAt_firstAction (nested : Bool) (retained : HedgeCarrierObservedState signature)
    (bit : Bool) : hedgeIsSecond rich firstAction (replayAt nested retained bit firstAction) = oldBit retained firstAction := by
  have equation := replayAt_bit nested retained bit firstAction (by decide +kernel)
  rw [incoming_firstAction, incoming_firstAction] at equation
  simpa only [show firstAction ≠ outerReentry from by decide +kernel, if_false, Bool.xor_false] using equation

private theorem replayAt_firstRoot (nested : Bool) (retained : HedgeCarrierObservedState signature)
    (bit : Bool) : hedgeIsSecond rich firstRoot (replayAt nested retained bit firstRoot) = oldBit retained firstRoot := by
  have equation := replayAt_bit nested retained bit firstRoot (by decide +kernel)
  rw [incoming_firstRoot, incoming_firstRoot] at equation
  simpa only [show firstRoot ≠ outerReentry from by decide +kernel, if_false, Bool.xor_false] using equation

private theorem replayAt_outerReentry (nested : Bool) (retained : HedgeCarrierObservedState signature)
    (bit : Bool) : hedgeIsSecond rich outerReentry (replayAt nested retained bit outerReentry) =
      Bool.xor (oldBit retained outerReentry) bit := by
  have equation := replayAt_bit nested retained bit outerReentry (by decide +kernel)
  rw [incoming_outerReentry, incoming_outerReentry, replayAt_firstAction] at equation
  have cancel (value parent : Bool) : Bool.xor (Bool.xor value parent) parent = value := by
    cases value <;> cases parent <;> rfl
  simpa only [if_true, oldBit, cancel] using equation

private theorem replayAt_secondAction (nested : Bool) (retained : HedgeCarrierObservedState signature)
    (bit : Bool) : hedgeIsSecond rich secondAction (replayAt nested retained bit secondAction) =
      Bool.xor (oldBit retained secondAction) bit := by
  have equation := replayAt_bit nested retained bit secondAction (by decide +kernel)
  rw [incoming_secondAction, incoming_secondAction, replayAt_outerReentry] at equation
  have cancel (value parent fresh : Bool) :
      Bool.xor (Bool.xor value parent) (Bool.xor parent fresh) = Bool.xor value fresh := by
    cases value <;> cases parent <;> cases fresh <;> rfl
  simpa only [show secondAction ≠ outerReentry from by decide +kernel, if_false, Bool.xor_false, oldBit, cancel] using equation

private theorem replayAt_lastRoot (nested : Bool) (retained : HedgeCarrierObservedState signature)
    (bit : Bool) : hedgeIsSecond rich lastRoot (replayAt nested retained bit lastRoot) =
      Bool.xor (oldBit retained lastRoot) (if nested then false else bit) := by
  have equation := replayAt_bit nested retained bit lastRoot (by decide +kernel)
  rw [incoming_lastRoot, incoming_lastRoot] at equation
  cases nested
  · simp only [Bool.false_eq_true, if_false] at equation ⊢
    rw [replayAt_secondAction] at equation
    have cancel (value parent fresh : Bool) :
        Bool.xor (Bool.xor value parent) (Bool.xor parent fresh) = Bool.xor value fresh := by
      cases value <;> cases parent <;> cases fresh <;> rfl
    simpa only [show lastRoot ≠ outerReentry from by decide +kernel, if_false, Bool.xor_false, oldBit, cancel] using equation
  · simpa only [if_true, show lastRoot ≠ outerReentry from by decide +kernel, if_false, Bool.xor_false] using equation

/-- An observable root event, independent of hidden units or retained
backgrounds.  It will distinguish the two actual averaged laws below. -/
def rootEvent : Event signature.Assignment := fun sample =>
  Bool.xor (hedgeIsSecond rich firstRoot (sample firstRoot))
    (hedgeIsSecond rich lastRoot (sample lastRoot))

private theorem rootEvent_eq_rootParity (sample : signature.Assignment) :
    rootEvent sample = hedgeRootParityEvent rich witness.roots sample := by
  have roots : NodeSet.members witness.roots = [firstRoot, lastRoot] := by decide +kernel
  unfold hedgeRootParityEvent hedgeNodeXor
  rw [roots]
  exact (congrArg (fun total => Bool.xor total (hedgeIsSecond rich lastRoot (sample lastRoot)))
    (Bool.false_xor _)).symm

private theorem original_rootEvent_eq_defect
    (unit : (witness.largeCarrierDefectParityModel rich).latent.Assignment) :
    rootEvent ((witness.largeCarrierDefectParityModel rich).eval unit) = hedgeDefectBitOf graph unit := by
  rw [rootEvent_eq_rootParity]
  change hedgeNodeXor witness.roots (fun node => hedgeIsSecond rich node
    ((witness.largeCarrierDefectParityModel rich).eval unit node)) = _
  rw [← witness.large_forest.nodeXor_requiredIncidence rich]
  exact (witness.largeCarrierDefectBitOf_eval rich unit).symm

private theorem replayAt_rootEvent (nested : Bool) (retained : HedgeCarrierObservedState signature)
    (bit : Bool) : rootEvent (replayAt nested retained bit) =
      Bool.xor (rootEvent retained.1) (if nested then false else bit) := by
  unfold rootEvent
  rw [replayAt_firstRoot, replayAt_lastRoot]
  exact (Bool.xor_assoc _ _ _).symm

/-- Read the actual prefixed defect marginal from its independent product
prior.  Its record is the same two-to-one biased coin as `noise`; the whole
large latent enumeration is never unfolded to obtain this marginal. -/
private theorem defect_marginal (event : Event Bool) :
    QProb.Equiv
      ((witness.largeCarrierDefectParityModel rich).prior.probVal
        (fun unit => event (hedgeDefectBitOf graph unit)))
      (noise.probVal event) := by
  have marginal := FiniteProduct.record_coordinate_probVal_dependent
    (hedgeDefectLatentCount graph) (hedgeDefectLatentValue graph) (hedgeDefectLatentFactor graph)
    (hedgeDefectRoot graph) (fun value => event (cast (hedgeDefectLatentValue_zero graph) value))
  have pushed := (hedgeDefectLatentFactor graph (hedgeDefectRoot graph)).map_probVal
    (cast (hedgeDefectLatentValue_zero graph)) event
  have record : (hedgeDefectLatentFactor graph (hedgeDefectRoot graph)).map
      (cast (hedgeDefectLatentValue_zero graph)) = noise := rfl
  rw [record] at pushed
  exact QProb.equiv_trans marginal (QProb.equiv_symm pushed)

private theorem retained_rootEvent_marginal (event : Event Bool) :
    QProb.Equiv
      ((witness.carrierRetainedStateDist rich).probVal (fun retained => event (rootEvent retained.1)))
      (noise.probVal event) := by
  have pushed := (witness.largeCarrierDefectParityModel rich).prior.map_probVal
    (hedgeCarrierObservedState graph (witness.largeCarrierDefectParityModel rich).eval)
    (fun retained => event (rootEvent retained.1))
  have decoded := (witness.largeCarrierDefectParityModel rich).prior.probVal_congr _ _
    (fun unit => congrArg event (original_rootEvent_eq_defect unit))
  exact QProb.equiv_trans pushed (QProb.equiv_trans decoded (defect_marginal event))

private theorem replayNodeWithNoise_eq_replay (freshNoise : FiniteProbRecord Bool) (nested : Bool)
    (retained : HedgeCarrierObservedState signature) (inputs : HedgeReadoutInputs.Inputs plan)
    (node : Fin signature.count) :
    witness.carrierPlanReplayNodeWithInputs rich nested retained (planWithNoise freshNoise) inputs
        (FiniteLatentSCM.noIntervention signature) node =
      witness.carrierPlanReplayNodeWithInputs rich nested retained plan inputs
        (FiniteLatentSCM.noIntervention signature) node := by
  conv => lhs; rw [HedgeWitness.carrierPlanReplayNodeWithInputs]
  conv => rhs; rw [HedgeWitness.carrierPlanReplayNodeWithInputs]
  simp only [FiniteLatentSCM.noIntervention]
  have parentsEqual :
      (fun parent (_edge : signature.directed parent node = true) =>
        witness.carrierPlanReplayNodeWithInputs rich nested retained (planWithNoise freshNoise) inputs
          (FiniteLatentSCM.noIntervention signature) parent) =
      (fun parent (_edge : signature.directed parent node = true) =>
        witness.carrierPlanReplayNodeWithInputs rich nested retained plan inputs
          (FiniteLatentSCM.noIntervention signature) parent) := by
    funext parent edge
    exact replayNodeWithNoise_eq_replay freshNoise nested retained inputs parent
  rw [parentsEqual]
  rfl
termination_by node.val
decreasing_by exact signature.directed_earlier edge

private theorem replayWithNoise_eq_replay (freshNoise : FiniteProbRecord Bool) (nested : Bool)
    (retained : HedgeCarrierObservedState signature) (inputs : HedgeReadoutInputs.Inputs plan) :
    witness.carrierPlanReplayWithInputs rich nested retained (planWithNoise freshNoise) inputs
        (FiniteLatentSCM.noIntervention signature) =
      witness.carrierPlanReplayWithInputs rich nested retained plan inputs
        (FiniteLatentSCM.noIntervention signature) :=
  funext (replayNodeWithNoise_eq_replay freshNoise nested retained inputs)

private theorem replayDistWithNoise_rootEvent_marginal (freshNoise : FiniteProbRecord Bool) (nested : Bool) :
    QProb.Equiv
      ((witness.carrierReplayDist rich nested (planWithNoise freshNoise)
        (FiniteLatentSCM.noIntervention signature)).probVal rootEvent)
      ((freshNoise.product noise).probVal (fun pair => Bool.xor pair.2 (if nested then false else pair.1))) := by
  have pushed := (witness.carrierReplayInputStateDist rich (planWithNoise freshNoise)).map_probVal
    (fun pair => witness.carrierPlanReplayWithInputs rich nested pair.2 (planWithNoise freshNoise) pair.1
      (FiniteLatentSCM.noIntervention signature)) rootEvent
  have decoded := (witness.carrierReplayInputStateDist rich (planWithNoise freshNoise)).probVal_congr
    (fun pair => rootEvent (witness.carrierPlanReplayWithInputs rich nested pair.2 (planWithNoise freshNoise) pair.1
      (FiniteLatentSCM.noIntervention signature)))
    (fun pair => Bool.xor (rootEvent pair.2.1) (if nested then false else pair.1.2)) (by
      intro pair
      rcases pair with ⟨⟨empty, bit⟩, retained⟩
      cases empty
      exact (congrArg rootEvent (replayWithNoise_eq_replay freshNoise nested retained ((), bit))).trans
        (replayAt_rootEvent nested retained bit))
  have marginal := (HedgeReadoutInputs.distribution (planWithNoise freshNoise)).product_probVal_equiv_of_slices
    (witness.carrierRetainedStateDist rich) noise
    (fun pair => Bool.xor (rootEvent pair.2.1) (if nested then false else pair.1.2))
    (fun pair => Bool.xor pair.2 (if nested then false else pair.1.2))
    (fun inputs => retained_rootEvent_marginal (fun signal => Bool.xor signal (if nested then false else inputs.2)))
  have encoded : HedgeReadoutInputs.distribution (planWithNoise freshNoise) =
      freshNoise.map (fun bit => ((), bit)) := by
    simp only [planWithNoise, HedgeReadoutInputs.distribution, FiniteProbRecord.product,
      FiniteProbRecord.map, FiniteProbRecord.weightedCartesian, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, Nat.one_mul]
    rfl
  have inputs := freshNoise.product_map_left_probVal noise (fun bit => ((), bit))
    (fun pair => Bool.xor pair.2 (if nested then false else pair.1.2))
  rw [← encoded] at inputs
  exact QProb.equiv_trans pushed (QProb.equiv_trans decoded (QProb.equiv_trans marginal inputs))

/-- For arbitrary fresh weights, the large root event has numerator
`den + flipMass` over `3 * den`, while the nested root event stays at `1/3`.
The expression retains the actual denominator and permits repeated noise
labels, zero weights, and unsupported values.  It is not an approximation. -/
theorem updatedWithNoise_rootEvent_probability (freshNoise : FiniteProbRecord Bool) (nested : Bool) :
    QProb.Equiv
      (((witness.carrierDefectParityModelFor rich nested).withHedgeReadouts rich
        (planWithNoise freshNoise)).observationalValue rootEvent)
      (if nested then (⟨1, 3, by decide⟩ : QProb) else
        ⟨freshNoise.den + FiniteProbRecord.eventMass freshNoise.atoms id,
          3 * freshNoise.den, Nat.mul_pos (by decide) freshNoise.den_pos⟩) := by
  have actual := QProb.equiv_trans
    (((witness.carrierDefectParityModelFor rich nested).withHedgeReadouts rich
      (planWithNoise freshNoise)).observationalValue_eq rootEvent)
    (witness.carrierDefectParityModelFor_withHedgeReadouts_event_probVal_equiv_replayDist
      rich nested (planWithNoise freshNoise) (FiniteLatentSCM.noIntervention signature) rootEvent)
  have coins : QProb.Equiv
      ((freshNoise.product noise).probVal (fun pair => Bool.xor pair.2 (if nested then false else pair.1)))
      (if nested then (⟨1, 3, by decide⟩ : QProb) else
        ⟨freshNoise.den + FiniteProbRecord.eventMass freshNoise.atoms id,
          3 * freshNoise.den, Nat.mul_pos (by decide) freshNoise.den_pos⟩) := by
    cases nested
    · simp only [Bool.false_eq_true, if_false]
      have partition := FiniteProbRecord.eventMass_add_complement freshNoise.atoms id
      rw [freshNoise.total_mass] at partition
      change FiniteProbRecord.eventMass (FiniteProbRecord.weightedCartesian freshNoise.atoms noise.atoms)
          (fun pair => Bool.xor (id pair.2) pair.1) * (3 * freshNoise.den) =
        (freshNoise.den + FiniteProbRecord.eventMass freshNoise.atoms id) * (freshNoise.den * 3)
      rw [FiniteProbRecord.eventMass_weightedCartesian_xor_noise_first]
      simp only [id_eq] at partition ⊢
      have inactive : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) = 2 := by decide +kernel
      have active : FiniteProbRecord.eventMass noise.atoms id = 1 := by decide +kernel
      rw [inactive, active]
      have numerator :
          FiniteProbRecord.eventMass freshNoise.atoms (fun bit => !bit) * 1 +
            FiniteProbRecord.eventMass freshNoise.atoms id * 2 =
          freshNoise.den + FiniteProbRecord.eventMass freshNoise.atoms id := by
        omega
      rw [numerator]
      ac_rfl
    · simp only [if_true, Bool.xor_false]
      exact QProb.equiv_trans (freshNoise.product_probVal_right noise id) (by decide +kernel)
  exact QProb.equiv_trans actual
    (QProb.equiv_trans (replayDistWithNoise_rootEvent_marginal freshNoise nested) coins)

/-- No change of the fresh-noise weights alone repairs this update while
retaining a positive-probability flip.  This includes fair noise and every
supported biased record.  It concerns the original two-to-one defect priors
and the stated toggle mechanism; it does not prohibit changing those priors,
the mechanisms, or the countermodel family itself. -/
theorem updatedWithNoise_not_observationally_equivalent
    (freshNoise : FiniteProbRecord Bool)
    (flipPositive : freshNoise.EventPositive (FiniteProbRecord.singletonEvent true)) :
    Not (ObservationallyEquivalent
      ((witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich (planWithNoise freshNoise))
      ((witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich (planWithNoise freshNoise))) := by
  have event : FiniteProbRecord.singletonEvent true = (id : Bool -> Bool) := by
    funext bit
    cases bit <;> rfl
  have positive : 0 < FiniteProbRecord.eventMass freshNoise.atoms id := by
    rw [← event]
    exact flipPositive
  intro equivalent
  have impossible := QProb.equiv_trans (QProb.equiv_symm (updatedWithNoise_rootEvent_probability freshNoise false))
    (QProb.equiv_trans (equivalent rootEvent) (updatedWithNoise_rootEvent_probability freshNoise true))
  change (freshNoise.den + FiniteProbRecord.eventMass freshNoise.atoms id) * 3 =
    1 * (3 * freshNoise.den) at impossible
  omega

/-- Specialize the arbitrary-noise formula to the supported two-to-one
coin.  The large latent prior was integrated through its proved coordinate
marginal; neither the full prior table nor a binary replacement of the
observed values is used to justify these exact probabilities. -/
theorem updated_rootEvent_probability (nested : Bool) :
    QProb.Equiv
      (((witness.carrierDefectParityModelFor rich nested).withHedgeReadouts rich plan).observationalValue rootEvent)
      (if nested then (⟨1, 3, by decide⟩ : QProb) else ⟨4, 9, by decide⟩) :=
  updatedWithNoise_rootEvent_probability noise nested

/-- This free, non-action outer update really breaks observational equality
despite supported biased noise and positive graph-compatible installed
models.  Averaging unequal pointwise replays is not automatically a repair. -/
theorem updated_not_observationally_equivalent :
    Not (ObservationallyEquivalent
      ((witness.largeCarrierDefectParityModel rich).withHedgeReadouts rich plan)
      ((witness.smallCarrierDefectParityModel rich).withHedgeReadouts rich plan)) :=
  updatedWithNoise_not_observationally_equivalent noise (noise_positive true)

/-- There is no recoding of the stated common joint law that preserves its
probabilities and matches the two replays on positive atoms.  This rules out
the entire recoding proof method for this particular plan, not only identity
recoding or transformations that keep each fresh-input slice fixed.

It does not refute the universal hedge theorem.  A different plan, different
noise mechanisms or priors, or a genuinely broader countermodel construction
is still allowed and is precisely what remains to be developed. -/
theorem no_jointInputStateRecoding
    (recode : (HedgeReadoutInputs.Inputs plan × HedgeCarrierObservedState signature) ->
      (HedgeReadoutInputs.Inputs plan × HedgeCarrierObservedState signature))
    (preserves : forall event, QProb.Equiv
      ((witness.carrierReplayInputStateDist rich plan).probVal (fun pair => event (recode pair)))
      ((witness.carrierReplayInputStateDist rich plan).probVal event)) :
    Not (forall atom, atom ∈ (witness.carrierReplayInputStateDist rich plan).atoms -> 0 < atom.2 ->
      witness.carrierPlanReplayWithInputs rich false atom.1.2 plan atom.1.1
          (FiniteLatentSCM.noIntervention signature) =
        witness.carrierPlanReplayWithInputs rich true (recode atom.1).2 plan (recode atom.1).1
          (FiniteLatentSCM.noIntervention signature)) := by
  intro matching
  exact updated_not_observationally_equivalent
    (witness.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_of_jointInputStateRecoding
      rich plan recode preserves matching)

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
