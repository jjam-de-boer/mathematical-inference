import Thesis.CausalTransport.HedgeCarrierReplay
import Thesis.CausalTransport.HedgeReadoutEvaluation
import Thesis.CausalTransport.HedgeReadoutNoise
import Thesis.CausalTransport.HedgeReadoutInputs

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Exact two-sided carrier replay without a geometric restriction

The common-replay theorem in `HedgeCarrierReplayPlan` fixes outer-only
forest rows.  That hypothesis cannot cover every hedge, as the seven-node
carrier-route obstruction shows.  It must not be deleted by identifying the
large and nested parent maps when their excluded parents actually change.

This module instead retains the two parent maps separately.  Each side has
an exact topological replay on the same kind of retained state: the original
full observed assignment, all private backgrounds, and the actual defect.
The replay follows the final mechanism responses at their *new* parents.
It is proved equal to actual SCM evaluation after any finite readout plan,
under arbitrary interventions, including outer-only updates and responding
descendants.  No small-membership or route-avoidance premise is imposed.

The two replays need not agree.  Their observational comparison reduces to
two explicit pushforwards of one common finite retained-state law, rather
than to an assumed common pointwise response.  A checked state-law symmetry
can therefore be used in place of pointwise equality.  Such a symmetry or
another probability comparison still has to be constructed; this module
does not supply an unrestricted hedge countermodel by assuming it.

The main replay indexes fresh inputs by instruction occurrence, using
`HedgeReadoutInputs`.  Every repeated pivot therefore retains a separate
actual factor.  The fully integrated replay law is an independent product
of this input record and the common original retained-state record.  Its
comparison is necessary and sufficient for observational equality, and a
state-law recoding may mix fresh inputs with retained state.  It need not
match the two laws separately at each fixed input.

Node-indexed wrappers retain the older API for pivot-distinct plans.  Their
mechanism statements remain exact for repeated pivots with a shared supplied
bit, but only the older fixed-node-input integration methods require distinct
pivots.  That restriction is not present in the main integrated replay law.
-/

section Responses

variable {G : ObservedGraph S} {q : JointKernelQuery S}

/-- Select an actual base carrier.  `false` is the large carrier and `true`
the nested carrier; both use the independently constructed defect prior. -/
def HedgeWitness.carrierDefectParityModelFor (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nested : Bool) : ExactModel S :=
  if nested then w.smallCarrierDefectParityModel rich else w.largeCarrierDefectParityModel rich

/-- The nested model restricts incoming kept parents only at small rows.
Outer-only rows use the full kept map on both sides.  Keeping this child-
indexed distinction is essential once outer parents are allowed to respond. -/
def HedgeWitness.carrierParentMap (w : HedgeWitness G q) (nested : Bool)
    (child : Fin S.count) : ForestChild S :=
  if nested && w.small child then restrictChild w.small w.child else w.child

/-- Recover the real original retained state from an actual base latent
unit.  Boolean pattern matching handles the dependent model type directly;
no latent unit or background assignment is chosen from a proposition. -/
def HedgeWitness.carrierRetainedState (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) : (nested : Bool) ->
      (w.carrierDefectParityModelFor rich nested).latent.Assignment -> HedgeCarrierObservedState S
  | false, unit => hedgeCarrierObservedState G (w.largeCarrierDefectParityModel rich).eval unit
  | true, unit => hedgeCarrierObservedState G (w.smallCarrierDefectParityModel rich).eval unit

/-- Reconstruct a base mechanism at arbitrary current parent inputs from
its factual state.  The exogenous incidence and defect are recovered through
the factual residual; retained backgrounds recover all nonbinary labels. -/
def HedgeWitness.carrierRetainedResponse (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nested : Bool) (state : HedgeCarrierObservedState S)
    (child : Fin S.count) (parents : S.ParentValues child) : S.Value child :=
  if w.large child then hedgeParityCarrierValue rich child
    (Bool.xor
      (Bool.xor (hedgeIsSecond rich child (state.1 child))
        (hedgeForestParentBitsFrom rich (w.carrierParentMap nested child) child
          (fun parent _edge => state.1 parent)))
      (hedgeForestParentBitsFrom rich (w.carrierParentMap nested child) child parents))
    (hedgePrivateDecode S child (state.2.1 child))
  else state.1 child

/-- This response is proved against the actual typed SCM mechanism on both
sides, not postulated as a common response or a probability-equivalence
premise.  Parent inputs can be interventional, not only factual. -/
theorem HedgeWitness.carrierDefectParityModelFor_mechanism_eq_retainedResponse
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (unit : (w.carrierDefectParityModelFor rich nested).latent.Assignment)
    (child : Fin S.count) (parents : S.ParentValues child) :
    (w.carrierDefectParityModelFor rich nested).mechanism child parents (fun root _incident => unit root) =
      w.carrierRetainedResponse rich nested (w.carrierRetainedState rich nested unit) child parents := by
  cases nested with
  | false =>
      simpa only [HedgeWitness.carrierDefectParityModelFor, HedgeWitness.carrierRetainedResponse,
        HedgeWitness.carrierRetainedState, hedgeCarrierObservedState, HedgeWitness.carrierParentMap,
        Bool.false_and, Bool.false_eq_true, if_false] using
        w.largeCarrierDefectParityModel_mechanism_parent_response rich unit child parents
  | true =>
      simpa only [HedgeWitness.carrierDefectParityModelFor, HedgeWitness.carrierRetainedResponse,
        HedgeWitness.carrierRetainedState, hedgeCarrierObservedState, HedgeWitness.carrierParentMap,
        Bool.true_and, if_true] using
        w.smallCarrierDefectParityModel_mechanism_parent_response rich unit child parents

/-! ## Topological replay of all final mechanism responses -/

/-- Evaluate a finite plan on retained state, using the appropriate side's
base response.  Installed readouts receive the final current parents, and
repeated updates at one row compose in their actual installation order.
An intervention bypasses that row's entire installed mechanism. -/
def HedgeWitness.carrierPlanReplayNodeWithInputs (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nested : Bool) (state : HedgeCarrierObservedState S)
    (steps : List (HedgeReadoutStep S)) (inputs : HedgeReadoutInputs.Inputs steps)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (child : Fin S.count) : S.Value child :=
  match intervention child with
  | some value => value
  | none =>
      let parents := fun parent (_edge : S.directed parent child = true) =>
        w.carrierPlanReplayNodeWithInputs rich nested state steps inputs intervention parent
      HedgeReadoutInputs.response rich child parents steps inputs
        (w.carrierRetainedResponse rich nested state child parents)
termination_by child.val
decreasing_by exact S.directed_earlier _edge

/-- The complete full-value assignment, not just a root parity or the
prefix ending at an installed pivot. -/
def HedgeWitness.carrierPlanReplayWithInputs (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nested : Bool) (state : HedgeCarrierObservedState S)
    (steps : List (HedgeReadoutStep S)) (inputs : HedgeReadoutInputs.Inputs steps)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) : S.Assignment :=
  fun child => w.carrierPlanReplayNodeWithInputs rich nested state steps inputs intervention child

/-- Convenience wrapper for a node-indexed bit family.  Repeated pivots
share this supplied bit only in the wrapper; the main input-indexed replay
does not identify their independent coordinates. -/
def HedgeWitness.carrierPlanReplay (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nested : Bool) (state : HedgeCarrierObservedState S)
    (steps : List (HedgeReadoutStep S)) (bits : Fin S.count -> Bool)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) : S.Assignment :=
  w.carrierPlanReplayWithInputs rich nested state steps (HedgeReadoutInputs.ofNodeBits bits steps) intervention

private theorem replayNode_actual (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (steps : List (HedgeReadoutStep S)) (inputs : HedgeReadoutInputs.Inputs steps)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (unit : (w.carrierDefectParityModelFor rich nested).latent.Assignment) (child : Fin S.count) :
    ((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).evalNodeUnder intervention
      ((w.carrierDefectParityModelFor rich nested).hedgeReadoutAssignmentWithInputs rich steps inputs unit) child =
    w.carrierPlanReplayNodeWithInputs rich nested (w.carrierRetainedState rich nested unit)
      steps inputs intervention child := by
  rw [FiniteLatentSCM.evalNodeUnder, HedgeWitness.carrierPlanReplayNodeWithInputs]
  unfold FiniteLatentSCM.equationUnder
  cases fixed : intervention child with
  | some value => rfl
  | none =>
      rw [FiniteLatentSCM.withHedgeReadouts_mechanism_eq_responseWithInputs,
        w.carrierDefectParityModelFor_mechanism_eq_retainedResponse]
      have parentsEqual :
          (fun parent (_edge : S.directed parent child = true) =>
            ((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).evalNodeUnder intervention
              ((w.carrierDefectParityModelFor rich nested).hedgeReadoutAssignmentWithInputs rich steps inputs unit) parent) =
          (fun parent (_edge : S.directed parent child = true) =>
            w.carrierPlanReplayNodeWithInputs rich nested (w.carrierRetainedState rich nested unit)
              steps inputs intervention parent) := by
        funext parent edge
        exact replayNode_actual w rich nested steps inputs intervention unit parent
      rw [parentsEqual]
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- Actual full SCM evaluation equals the selected side's replay for any
finite plan, any independent occurrence inputs, and any intervention.
Repeated pivots and outer-only updates are included; no equality of the two
sides is inferred here. -/
theorem HedgeWitness.carrierDefectParityModelFor_withHedgeReadouts_evalUnderWithInputs_eq_replay
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (steps : List (HedgeReadoutStep S)) (inputs : HedgeReadoutInputs.Inputs steps)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (unit : (w.carrierDefectParityModelFor rich nested).latent.Assignment) :
    ((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).evalUnder intervention
      ((w.carrierDefectParityModelFor rich nested).hedgeReadoutAssignmentWithInputs rich steps inputs unit) =
    w.carrierPlanReplayWithInputs rich nested (w.carrierRetainedState rich nested unit)
      steps inputs intervention :=
  funext (replayNode_actual w rich nested steps inputs intervention unit)

/-- The node-indexed API follows by explicit occurrence encoding.  It is
an exact mechanism identity, not an assertion of independent repeated bits. -/
theorem HedgeWitness.carrierDefectParityModelFor_withHedgeReadouts_evalUnder_eq_replay
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (steps : List (HedgeReadoutStep S)) (bits : Fin S.count -> Bool)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (unit : (w.carrierDefectParityModelFor rich nested).latent.Assignment) :
    ((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).evalUnder intervention
      ((w.carrierDefectParityModelFor rich nested).hedgeReadoutAssignment rich bits steps unit) =
    w.carrierPlanReplay rich nested (w.carrierRetainedState rich nested unit) steps bits intervention := by
  have exactReplay := w.carrierDefectParityModelFor_withHedgeReadouts_evalUnderWithInputs_eq_replay
    rich nested steps (HedgeReadoutInputs.ofNodeBits bits steps) intervention unit
  rw [FiniteLatentSCM.hedgeReadoutAssignmentWithInputs_ofNodeBits] at exactReplay
  exact exactReplay

end Responses

section Probability

variable {G : ObservedGraph S} {q : JointKernelQuery S}

/-- One actual finite record for the common original retained-state law.
The nested carrier's corresponding record is probability-equivalent by the
proved joint observed/background/defect theorem. -/
def HedgeWitness.carrierRetainedStateDist (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    FiniteProbRecord (HedgeCarrierObservedState S) :=
  (w.largeCarrierDefectParityModel rich).prior.map
    (hedgeCarrierObservedState G (w.largeCarrierDefectParityModel rich).eval)

/-- The selected side's real original prior has the common retained-state
law.  This does not compare the updated observations or identify the two
replay functions. -/
theorem HedgeWitness.carrierDefectParityModelFor_retainedState_probVal_equiv
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (event : Event (HedgeCarrierObservedState S)) :
    QProb.Equiv
      ((w.carrierDefectParityModelFor rich nested).prior.probVal
        (fun unit => event (w.carrierRetainedState rich nested unit)))
      ((w.carrierRetainedStateDist rich).probVal event) := by
  have pushed := (w.largeCarrierDefectParityModel rich).prior.map_probVal
    (hedgeCarrierObservedState G (w.largeCarrierDefectParityModel rich).eval) event
  cases nested with
  | false => exact QProb.equiv_symm pushed
  | true =>
      exact QProb.equiv_trans
        (QProb.equiv_symm (w.carrierDefectParityModels_observationalState_probVal_equiv rich event))
        (QProb.equiv_symm pushed)

/-! ## The full input-averaged replay law -/

/-- A single explicit law for all fresh occurrence inputs and the original
retained state.  It is the same record for the two sides; fresh factors are
independent of the state, but observed values and retained backgrounds are
not incorrectly assumed independent of one another. -/
def HedgeWitness.carrierReplayInputStateDist (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (steps : List (HedgeReadoutStep S)) :
    FiniteProbRecord (HedgeReadoutInputs.Inputs steps × HedgeCarrierObservedState S) :=
  (HedgeReadoutInputs.distribution steps).product (w.carrierRetainedStateDist rich)

/-- Push the common joint input/state law through the selected side's full
replay.  The two output records may differ; no probability comparison is
hidden in this definition.  Any intervention and repeated-pivot plan is
allowed, with a separate fresh factor at each instruction occurrence. -/
def HedgeWitness.carrierReplayDist (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nested : Bool) (steps : List (HedgeReadoutStep S))
    (intervention : (node : Fin S.count) -> Option (S.Value node)) : FiniteProbRecord S.Assignment :=
  (w.carrierReplayInputStateDist rich steps).map (fun pair =>
    w.carrierPlanReplayWithInputs rich nested pair.2 steps pair.1 intervention)

/-- The real final SCM event law equals the completely input-averaged
replay record.  The proof integrates every actual independent factor, then
uses the proved common retained-state law.  It requires neither distinct
pivots nor equality of the two side-specific replays at a fixed input. -/
theorem HedgeWitness.carrierDefectParityModelFor_withHedgeReadouts_event_probVal_equiv_replayDist
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (steps : List (HedgeReadoutStep S))
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (event : Event S.Assignment) :
    QProb.Equiv
      (((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).prior.probVal
        (fun unit => event
          (((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).evalUnder
            intervention unit)))
      ((w.carrierReplayDist rich nested steps intervention).probVal event) := by
  have integrated := (w.carrierDefectParityModelFor rich nested).withHedgeReadouts_prior_probVal_equiv_inputs
    rich steps (fun unit => event
      (((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).evalUnder intervention unit))
  have compared := (HedgeReadoutInputs.distribution steps).product_probVal_equiv_of_slices
    (w.carrierDefectParityModelFor rich nested).prior (w.carrierRetainedStateDist rich)
    (fun pair => event
      (((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).evalUnder intervention
        ((w.carrierDefectParityModelFor rich nested).hedgeReadoutAssignmentWithInputs rich steps pair.1 pair.2)))
    (fun pair => event (w.carrierPlanReplayWithInputs rich nested pair.2 steps pair.1 intervention))
    (by
      intro inputs
      have actual := (w.carrierDefectParityModelFor rich nested).prior.probVal_congr _ _ (fun unit =>
        congrArg event (w.carrierDefectParityModelFor_withHedgeReadouts_evalUnderWithInputs_eq_replay
          rich nested steps inputs intervention unit))
      exact QProb.equiv_trans actual
        (w.carrierDefectParityModelFor_retainedState_probVal_equiv rich nested
          (fun state => event (w.carrierPlanReplayWithInputs rich nested state steps inputs intervention))))
  have pushed := (w.carrierReplayInputStateDist rich steps).map_probVal
    (fun pair => w.carrierPlanReplayWithInputs rich nested pair.2 steps pair.1 intervention) event
  exact QProb.equiv_trans integrated (QProb.equiv_trans compared (QProb.equiv_symm pushed))

private theorem observationalValue_replayDist (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nested : Bool) (steps : List (HedgeReadoutStep S))
    (event : Event S.Assignment) :
    QProb.Equiv
      (((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).observationalValue event)
      ((w.carrierReplayDist rich nested steps (FiniteLatentSCM.noIntervention S)).probVal event) :=
  QProb.equiv_trans
    (((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).observationalValue_eq event)
    (w.carrierDefectParityModelFor_withHedgeReadouts_event_probVal_equiv_replayDist
      rich nested steps (FiniteLatentSCM.noIntervention S) event)

/-- Necessary and sufficient observational comparison of the two actual
installed models.  The right side compares the fully averaged pushforwards
of one explicit input/state record.  It permits equality obtained by mixing
different fresh-input slices, not only equality at each fixed slice.

This is an exact reduction of the remaining comparison, not a general
countermodel theorem.  Nothing here asserts that the two replay records
agree for an arbitrary outer-only plan. -/
theorem HedgeWitness.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_iff_replayDist
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S)) :
    ObservationallyEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich steps)
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich steps) ↔
    forall event : Event S.Assignment, QProb.Equiv
      ((w.carrierReplayDist rich false steps (FiniteLatentSCM.noIntervention S)).probVal event)
      ((w.carrierReplayDist rich true steps (FiniteLatentSCM.noIntervention S)).probVal event) := by
  constructor
  · intro equivalent event
    exact QProb.equiv_trans (QProb.equiv_symm (observationalValue_replayDist w rich false steps event))
      (QProb.equiv_trans (equivalent event) (observationalValue_replayDist w rich true steps event))
  · intro equivalent event
    exact QProb.equiv_trans (observationalValue_replayDist w rich false steps event)
      (QProb.equiv_trans (equivalent event) (QProb.equiv_symm (observationalValue_replayDist w rich true steps event)))

private theorem eventMass_congr_on_positive_atoms (atoms : List (Ω × Nat)) (left right : Event Ω)
    (matching : forall atom, atom ∈ atoms -> 0 < atom.2 -> left atom.1 = right atom.1) :
    FiniteProbRecord.eventMass atoms left = FiniteProbRecord.eventMass atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      have tail := inductionHypothesis (fun next listed positive =>
        matching next (List.mem_cons_of_mem _ listed) positive)
      cases weight : atom.2 with
      | zero =>
          cases leftBit : left atom.1 <;> cases rightBit : right atom.1 <;>
            simp only [FiniteProbRecord.eventMass, leftBit, rightBit, weight, Bool.false_eq_true, if_true, if_false,
              Nat.zero_add, tail]
      | succ count =>
          have same := matching atom List.mem_cons_self (by rw [weight]; exact Nat.zero_lt_succ count)
          simp only [FiniteProbRecord.eventMass, same, tail]

/-- A constructive symmetry may mix fresh inputs with retained state.
Its invariance is stated on the single actual finite joint law.  The replay
matching need hold only on positive-weight atoms, not on impossible states
or zero-weight noise values.  No inverse, coupling, or support unit is chosen.

This is a sufficient construction method for the unrestricted comparison
boundary above.  A usable symmetry still has to be supplied and proved; its
existence for arbitrary outer-only routing is not assumed. -/
theorem HedgeWitness.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_of_jointInputStateRecoding
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (recode : (HedgeReadoutInputs.Inputs steps × HedgeCarrierObservedState S) ->
      (HedgeReadoutInputs.Inputs steps × HedgeCarrierObservedState S))
    (preserves : forall event, QProb.Equiv
      ((w.carrierReplayInputStateDist rich steps).probVal (fun pair => event (recode pair)))
      ((w.carrierReplayInputStateDist rich steps).probVal event))
    (matching : forall atom, atom ∈ (w.carrierReplayInputStateDist rich steps).atoms ->
      0 < atom.2 ->
      w.carrierPlanReplayWithInputs rich false atom.1.2 steps atom.1.1 (FiniteLatentSCM.noIntervention S) =
        w.carrierPlanReplayWithInputs rich true (recode atom.1).2 steps (recode atom.1).1
          (FiniteLatentSCM.noIntervention S)) :
    ObservationallyEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich steps)
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich steps) := by
  apply (w.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_iff_replayDist rich steps).mpr
  intro event
  have leftPushed := (w.carrierReplayInputStateDist rich steps).map_probVal
    (fun pair => w.carrierPlanReplayWithInputs rich false pair.2 steps pair.1 (FiniteLatentSCM.noIntervention S)) event
  have rightPushed := (w.carrierReplayInputStateDist rich steps).map_probVal
    (fun pair => w.carrierPlanReplayWithInputs rich true pair.2 steps pair.1 (FiniteLatentSCM.noIntervention S)) event
  have matched : QProb.Equiv
      ((w.carrierReplayInputStateDist rich steps).probVal (fun pair => event
        (w.carrierPlanReplayWithInputs rich false pair.2 steps pair.1 (FiniteLatentSCM.noIntervention S))))
      ((w.carrierReplayInputStateDist rich steps).probVal (fun pair => event
        (w.carrierPlanReplayWithInputs rich true (recode pair).2 steps (recode pair).1
          (FiniteLatentSCM.noIntervention S)))) := by
    change FiniteProbRecord.eventMass _ _ * _ = FiniteProbRecord.eventMass _ _ * _
    exact congrArg (fun mass => mass * (w.carrierReplayInputStateDist rich steps).den)
      (eventMass_congr_on_positive_atoms _ _ _ (fun atom listed positive =>
        congrArg event (matching atom listed positive)))
  exact QProb.equiv_trans leftPushed
    (QProb.equiv_trans matched (QProb.equiv_trans
      (preserves (fun pair => event (w.carrierPlanReplayWithInputs rich true pair.2 steps pair.1
        (FiniteLatentSCM.noIntervention S)))) (QProb.equiv_symm rightPushed)))

/-! ## Fixed node-input sufficient comparisons for the older API -/

/-- At fixed represented fresh inputs, the actual event law on either side
is its explicit replay pushforward of the common retained-state record.
The event may depend on every observed value and the intervention is arbitrary. -/
theorem HedgeWitness.carrierDefectParityModelFor_withHedgeReadouts_encodedEvent_probVal_equiv_replay
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) (nested : Bool)
    (steps : List (HedgeReadoutStep S)) (bits : Fin S.count -> Bool)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (event : Event S.Assignment) :
    QProb.Equiv
      ((w.carrierDefectParityModelFor rich nested).prior.probVal (fun unit => event
        (((w.carrierDefectParityModelFor rich nested).withHedgeReadouts rich steps).evalUnder intervention
          ((w.carrierDefectParityModelFor rich nested).hedgeReadoutAssignment rich bits steps unit))))
      ((w.carrierRetainedStateDist rich).probVal
        (fun state => event (w.carrierPlanReplay rich nested state steps bits intervention))) := by
  have pointwise (unit : (w.carrierDefectParityModelFor rich nested).latent.Assignment) :=
    congrArg event (w.carrierDefectParityModelFor_withHedgeReadouts_evalUnder_eq_replay
      rich nested steps bits intervention unit)
  exact QProb.equiv_trans
    ((w.carrierDefectParityModelFor rich nested).prior.probVal_congr _ _ pointwise)
    (w.carrierDefectParityModelFor_retainedState_probVal_equiv rich nested
      (fun state => event (w.carrierPlanReplay rich nested state steps bits intervention)))

/-- Compare two explicit replay pushforwards and integrate every actual
private factor.  The remaining premise is a finite probability comparison
on a single stated state record, not a falsely shared pointwise response.
Distinct pivots are needed only by the fresh-input representation at this
integration boundary; plan ordering and geometric exclusions are not needed. -/
theorem HedgeWitness.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_of_twoSidedReplay
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (distinct : steps.Pairwise (fun first second => first.pivot ≠ second.pivot))
    (comparison : forall (bits : Fin S.count -> Bool) (event : Event S.Assignment),
      QProb.Equiv
        ((w.carrierRetainedStateDist rich).probVal (fun state =>
          event (w.carrierPlanReplay rich false state steps bits (FiniteLatentSCM.noIntervention S))))
        ((w.carrierRetainedStateDist rich).probVal (fun state =>
          event (w.carrierPlanReplay rich true state steps bits (FiniteLatentSCM.noIntervention S))))) :
    ObservationallyEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich steps)
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich steps) := by
  intro event
  have integrated := FiniteLatentSCM.withHedgeReadouts_prior_equiv_of_encodedSlices
    (w.largeCarrierDefectParityModel rich) (w.smallCarrierDefectParityModel rich) rich steps distinct
    (fun unit => event (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich steps).eval unit))
    (fun unit => event (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich steps).eval unit))
    (by
      intro bits
      exact QProb.equiv_trans
        (w.carrierDefectParityModelFor_withHedgeReadouts_encodedEvent_probVal_equiv_replay
          rich false steps bits (FiniteLatentSCM.noIntervention S) event)
        (QProb.equiv_trans (comparison bits event)
          (QProb.equiv_symm
            (w.carrierDefectParityModelFor_withHedgeReadouts_encodedEvent_probVal_equiv_replay
              rich true steps bits (FiniteLatentSCM.noIntervention S) event))))
  exact QProb.equiv_trans
    (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich steps).observationalValue_eq event)
    (QProb.equiv_trans integrated
      (QProb.equiv_symm (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich steps).observationalValue_eq event)))

/-- A supplied probability-preserving state recoding may relate unequal
replays.  Both the recoding and its invariance proof are explicit data; no
coupling or inverse is selected by choice.  This is a sufficient proof method,
not a claim that every outer-only plan admits such a symmetry. -/
theorem HedgeWitness.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_of_stateRecoding
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (distinct : steps.Pairwise (fun first second => first.pivot ≠ second.pivot))
    (recode : (Fin S.count -> Bool) -> HedgeCarrierObservedState S -> HedgeCarrierObservedState S)
    (preserves : forall bits (event : Event (HedgeCarrierObservedState S)), QProb.Equiv
      ((w.carrierRetainedStateDist rich).probVal (fun state => event (recode bits state)))
      ((w.carrierRetainedStateDist rich).probVal event))
    (matching : forall bits state,
      w.carrierPlanReplay rich false state steps bits (FiniteLatentSCM.noIntervention S) =
      w.carrierPlanReplay rich true (recode bits state) steps bits (FiniteLatentSCM.noIntervention S)) :
    ObservationallyEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich steps)
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich steps) := by
  apply w.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_of_twoSidedReplay rich steps distinct
  intro bits event
  exact QProb.equiv_trans
    ((w.carrierRetainedStateDist rich).probVal_congr _ _ (fun state => congrArg event (matching bits state)))
    (preserves bits (fun state => event (w.carrierPlanReplay rich true state steps bits (FiniteLatentSCM.noIntervention S))))

end Probability

end Causality
end Thesis
