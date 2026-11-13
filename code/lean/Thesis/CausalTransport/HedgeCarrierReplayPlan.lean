import Thesis.CausalTransport.HedgeCarrierReplay
import Thesis.CausalTransport.HedgeReadoutSequence

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Common retained-state replay through finite carrier readout plans

The single internal replay theorem cannot be iterated by pretending that an
updated SCM is still an unmodified carrier.  Installed readouts change its
mechanisms, and their fresh bits must remain in its genuine product prior.
This module instead transports a mechanism-level presentation throughout
the actual plan.  Its common state retains the original observation and
private backgrounds, then appends each new independent Boolean.  Its common
response composes the installed readouts at their respective mechanisms.

The invariant fixes only outer-only forest vertices (`large` but not
`small`).  Kept parents of such a vertex are themselves outer-only, so their
original equations stay factual.  At a small vertex the large/restricted
parent parity changes therefore agree.  Outside-forest vertices may change:
they are not read by the original kept map, although installed readouts may
read them through ambient declared edges.  This permits internal re-entry
and responding descendants in the observational argument.

No increasing-order, distinct-pivot, kept-sink, non-influence, or positive
noise hypothesis is needed here.  Repeated instructions compose at the same
mechanism rather than overwriting an observed table.  Updating an outer-only
vertex is still excluded, and interventional parity separation is a separate
obligation: observational replay alone is not a completeness inhabitant.
-/

namespace HedgeCarrierReplayPlan

variable {G : ObservedGraph S} {q : JointKernelQuery S}

/-- The original large-carrier response to arbitrary parent values.  Its
exogenous residual is determined by the old observation and retained private
background; pair-root coordinates need not survive in the common state. -/
private def originalResponse (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (sample : S.Assignment) (backgrounds : HedgePrivateCoordinates S)
    (child : Fin S.count) (parents : S.ParentValues child) : S.Value child :=
  if w.large child then hedgeParityCarrierValue rich child
    (Bool.xor
      (Bool.xor (hedgeIsSecond rich child (sample child))
        (hedgeForestParentBitsFrom rich w.child child (fun parent _edge => sample parent)))
      (hedgeForestParentBitsFrom rich w.child child parents))
    (hedgePrivateDecode S child (backgrounds child))
  else sample child

/-- A common response system on explicitly retained state.  Only outer-only
forest rows must retain their original mechanism response.  Arbitrary
functions on typed parents and old full values are allowed at all other rows. -/
private structure ReplayData (w : HedgeWitness G q) (State : Type) where
  sample : State -> S.Assignment
  backgrounds : State -> HedgePrivateCoordinates S
  response : State -> (child : Fin S.count) -> S.ParentValues child -> S.Value child -> S.Value child
  outer_identity : forall state child, w.large child = true -> w.small child = false ->
    forall parents old, response state child parents old = old

/-- Topological solution of the common response system.  Every installed
readout receives the *new* parents.  Its old-value argument is the original
carrier response at those parents, transformed by earlier installed readouts
at that same mechanism, not its previously observed factual value. -/
private def ReplayData.evalNode (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    {State : Type} (data : ReplayData w State) (state : State) (child : Fin S.count) : S.Value child :=
  data.response state child (fun parent _edge => data.evalNode w rich state parent)
    (originalResponse w rich (data.sample state) (data.backgrounds state) child
      (fun parent _edge => data.evalNode w rich state parent))
termination_by child.val
decreasing_by exact S.directed_earlier _edge

/-- Outer-only kept rows cannot acquire a changed kept parent: small-parent
closure would put their child in the small forest, while outside-large
parents have no kept edge at all.  Cancelling the unchanged parent parity
then reconstructs the old full value, including nonbinary labels. -/
private theorem ReplayData.evalNode_outer (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    {State : Type} (data : ReplayData w State) (state : State)
    (fits : hedgeCarrierPrivateCoordinatesFit rich w.large (data.sample state) (data.backgrounds state) = true)
    (child : Fin S.count) (inside : w.large child = true) (outside : w.small child = false) :
    data.evalNode w rich state child = data.sample state child := by
  rw [ReplayData.evalNode, data.outer_identity state child inside outside]
  unfold originalResponse
  rw [inside]
  simp only [if_true]
  have parents : hedgeForestParentBitsFrom rich w.child child
      (fun parent _edge => data.evalNode w rich state parent) =
      hedgeForestParentBitsFrom rich w.child child (fun parent _edge => data.sample state parent) := by
    apply hedgeForestParentBitsFrom_congr_of_kept
    intro parent edge keptAt
    have parentLarge := (w.large_forest.child_edge parent child keptAt).1
    have parentOutside : w.small parent = false := by
      cases selected : w.small parent with
      | false => rfl
      | true =>
          have restricted : restrictChild w.small w.child parent = some child := by
            simpa only [restrictChild, selected, if_true] using keptAt
          have childInside := (w.small_forest.child_edge parent child restricted).2.1
          rw [outside] at childInside
          cases childInside
    exact congrArg (hedgeIsSecond rich parent)
      (data.evalNode_outer w rich state fits parent parentLarge parentOutside)
  rw [parents]
  have cancel (bit parentBit : Bool) : Bool.xor (Bool.xor bit parentBit) parentBit = bit := by
    cases bit <;> cases parentBit <;> rfl
  rw [cancel]
  exact hedgeCarrierPrivateCoordinatesFit_inside rich w.large _ _ fits child inside
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- A presentation is proved against the SCM's actual mechanisms and latent
units.  Agreement of outer-only parent values is the only admissibility
restriction.  The preceding topological invariant supplies it during real
evaluation; it is not an observational-equivalence premise in disguise. -/
private structure Presentation (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    {State : Type} (data : ReplayData w State) (model : ExactModel S) where
  stateOf : model.latent.Assignment -> State
  fits : forall unit, hedgeCarrierPrivateCoordinatesFit rich w.large
    (data.sample (stateOf unit)) (data.backgrounds (stateOf unit)) = true
  mechanism_eq : forall unit child parents,
    (forall parent edge, w.large parent = true -> w.small parent = false ->
      parents parent edge = data.sample (stateOf unit) parent) ->
    model.mechanism child parents (fun root _incident => unit root) =
      data.response (stateOf unit) child parents
        (originalResponse w rich (data.sample (stateOf unit)) (data.backgrounds (stateOf unit)) child parents)

/-- Real evaluation solves the common response system.  The recursive
parent equalities simultaneously supply every admissibility premise before
the actual mechanism equation is invoked.  No descendant is omitted. -/
private theorem Presentation.evalNode_eq (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    {State : Type} {data : ReplayData w State} {model : ExactModel S}
    (presentation : Presentation w rich data model) (unit : model.latent.Assignment) (child : Fin S.count) :
    model.evalNodeUnder (FiniteLatentSCM.noIntervention S) unit child =
      data.evalNode w rich (presentation.stateOf unit) child := by
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  simp only [FiniteLatentSCM.noIntervention]
  rw [presentation.mechanism_eq unit child _ (by
    intro parent edge inside outside
    exact (presentation.evalNode_eq w rich unit parent).trans
      (data.evalNode_outer w rich _ (presentation.fits unit) parent inside outside))]
  rw [ReplayData.evalNode]
  have parents :
      (fun parent (_edge : S.directed parent child = true) =>
        model.evalNodeUnder (FiniteLatentSCM.noIntervention S) unit parent) =
      (fun parent (_edge : S.directed parent child = true) =>
        data.evalNode w rich (presentation.stateOf unit) parent) := by
    funext parent edge
    exact presentation.evalNode_eq w rich unit parent
  rw [parents]
termination_by child.val
decreasing_by all_goals exact S.directed_earlier edge

/-! ## Transporting the mechanism presentation through actual private noise -/

/-- Recover the original typed latent block by the constructive castSucc
coordinate laws.  Decoding is total on every augmented unit, not just units
selected from support by a choice principle. -/
private def oldAssignment (model : ExactModel S) (pivot : Fin S.count)
    (unit : (PrivateBooleanNoise.extension model.latent pivot).Assignment) : model.latent.Assignment :=
  fun root => cast (PrivateBooleanNoise.value_castSucc model.latent root) (unit root.castSucc)

/-- The last coordinate is the genuinely appended private Boolean. -/
private def freshBit (model : ExactModel S) (pivot : Fin S.count)
    (unit : (PrivateBooleanNoise.extension model.latent pivot).Assignment) : Bool :=
  cast (PrivateBooleanNoise.value_last model.latent) (unit (Fin.last model.latent.count))

private theorem oldAssignment_encoded (model : ExactModel S) (pivot : Fin S.count)
    (bit : Bool) (unit : model.latent.Assignment) :
    oldAssignment model pivot (PrivateBooleanNoise.assignment model.latent bit unit) = unit := by
  funext root
  exact PrivateBooleanNoise.assignment_castSucc model.latent bit unit root

private theorem freshBit_encoded (model : ExactModel S) (pivot : Fin S.count)
    (bit : Bool) (unit : model.latent.Assignment) :
    freshBit model pivot (PrivateBooleanNoise.assignment model.latent bit unit) = bit :=
  PrivateBooleanNoise.assignment_last model.latent bit unit

/-- One fresh bit extends the retained state, while its readout composes
with the previously installed response at the same node.  Thus repeated and
descending instructions require no special-case evaluation semantics. -/
private def ReplayData.withStep (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    {State : Type} (data : ReplayData w State) (step : HedgeReadoutStep S)
    (allowed : w.small step.pivot = true ∨ w.large step.pivot = false) : ReplayData w (Bool × State) where
  sample := fun state => data.sample state.2
  backgrounds := fun state => data.backgrounds state.2
  response := fun state child parents old =>
    if same : child = step.pivot then by
      subst child
      exact hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal parents
        (data.response state.2 step.pivot parents old) state.1
    else data.response state.2 child parents old
  outer_identity := by
    intro state child inside outside parents old
    have different : child ≠ step.pivot := by
      intro same
      subst child
      cases allowed with
      | inl selected => rw [selected] at outside; cases outside
      | inr excluded => rw [excluded] at inside; cases inside
    simp only [dif_neg different]
    exact data.outer_identity state.2 child inside outside parents old

/-- Install one instruction in the real SCM and transport its mechanism
presentation.  At the pivot the old mechanism is transformed; everywhere
else its old incident inputs are recovered unchanged. -/
private def Presentation.withStep (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    {State : Type} {data : ReplayData w State} {model : ExactModel S}
    (presentation : Presentation w rich data model) (step : HedgeReadoutStep S)
    (allowed : w.small step.pivot = true ∨ w.large step.pivot = false) :
    Presentation w rich (data.withStep w rich step allowed) (step.apply rich model) where
  stateOf := fun unit => (freshBit model step.pivot unit,
    presentation.stateOf (oldAssignment model step.pivot unit))
  fits := fun unit => presentation.fits (oldAssignment model step.pivot unit)
  mechanism_eq := by
    intro unit child parents unchanged
    have oldInputs : PrivateBooleanNoise.oldInputs model.latent step.pivot child
        (fun root _incident => unit root) =
        (fun root _incident => oldAssignment model step.pivot unit root) := rfl
    by_cases same : child = step.pivot
    · subst child
      dsimp only [HedgeReadoutStep.apply, FiniteLatentSCM.withHedgeReadout, FiniteLatentSCM.withPrivateReadout]
      rw [FiniteLatentSCM.withPrivateBooleanNoise_mechanism_pivot]
      have oldResponse := (congrArg (model.mechanism step.pivot parents) oldInputs).trans
        (presentation.mechanism_eq _ _ _ unchanged)
      refine (congrArg (fun value => hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal
        parents value (PrivateBooleanNoise.bit model.latent step.pivot (fun root _incident => unit root)))
        oldResponse).trans ?_
      simp only [ReplayData.withStep]
      rfl
    · dsimp only [HedgeReadoutStep.apply, FiniteLatentSCM.withHedgeReadout, FiniteLatentSCM.withPrivateReadout]
      rw [FiniteLatentSCM.withPrivateBooleanNoise_mechanism_of_ne _ _ _ _ _ same]
      refine ((congrArg (model.mechanism child parents) oldInputs).trans
        (presentation.mechanism_eq _ _ _ unchanged)).trans ?_
      simp only [ReplayData.withStep, dif_neg same]

private theorem Presentation.withStep_state_encoded (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) {State : Type} {data : ReplayData w State}
    {model : ExactModel S} (presentation : Presentation w rich data model)
    (step : HedgeReadoutStep S) (allowed : w.small step.pivot = true ∨ w.large step.pivot = false)
    (bit : Bool) (unit : model.latent.Assignment) :
    (presentation.withStep w rich step allowed).stateOf
        (PrivateBooleanNoise.assignment model.latent bit unit) = (bit, presentation.stateOf unit) := by
  change (freshBit model step.pivot _, presentation.stateOf (oldAssignment model step.pivot _)) = _
  rw [freshBit_encoded, oldAssignment_encoded]

/-! ## The common retained-state law, not a presumed intermediate table -/

/-- Extend the common state law by the same independent factor on both
sides.  The encoded assignments are the literal pushforwards defining the
updated priors; the product comparison is applied to every Boolean slice.
Different original latent spaces and dependencies inside the old state do
not require an identification or an independence assumption. -/
private theorem stateLaw_withStep (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    {State : Type} {data : ReplayData w State} {left right : ExactModel S}
    (leftPresentation : Presentation w rich data left) (rightPresentation : Presentation w rich data right)
    (law : forall event : Event State,
      QProb.Equiv (left.prior.probVal (fun unit => event (leftPresentation.stateOf unit)))
        (right.prior.probVal (fun unit => event (rightPresentation.stateOf unit))))
    (step : HedgeReadoutStep S) (allowed : w.small step.pivot = true ∨ w.large step.pivot = false)
    (event : Event (Bool × State)) :
    QProb.Equiv
      ((step.apply rich left).prior.probVal
        (fun unit => event ((leftPresentation.withStep w rich step allowed).stateOf unit)))
      ((step.apply rich right).prior.probVal
        (fun unit => event ((rightPresentation.withStep w rich step allowed).stateOf unit))) := by
  let leftEvent : Event (Bool × left.latent.Assignment) := fun pair => event (pair.1, leftPresentation.stateOf pair.2)
  let rightEvent : Event (Bool × right.latent.Assignment) := fun pair => event (pair.1, rightPresentation.stateOf pair.2)
  have leftPushed := (step.noise.product left.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment left.latent pair.1 pair.2)
    (fun unit => event ((leftPresentation.withStep w rich step allowed).stateOf unit))
  have rightPushed := (step.noise.product right.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment right.latent pair.1 pair.2)
    (fun unit => event ((rightPresentation.withStep w rich step allowed).stateOf unit))
  have leftEncoded := (step.noise.product left.prior).probVal_congr _ leftEvent
    (fun pair => congrArg event (leftPresentation.withStep_state_encoded w rich step allowed pair.1 pair.2))
  have rightEncoded := (step.noise.product right.prior).probVal_congr _ rightEvent
    (fun pair => congrArg event (rightPresentation.withStep_state_encoded w rich step allowed pair.1 pair.2))
  have slices := step.noise.product_probVal_equiv_of_slices left.prior right.prior leftEvent rightEvent
    (fun bit => law (fun state => event (bit, state)))
  exact QProb.equiv_trans leftPushed
    (QProb.equiv_trans leftEncoded
      (QProb.equiv_trans slices
        (QProb.equiv_trans (QProb.equiv_symm rightEncoded) (QProb.equiv_symm rightPushed))))

/-- Full observed events are common functions of the retained state because
both actual evaluations solve the same response system. -/
private theorem observational_of_stateLaw (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    {State : Type} {data : ReplayData w State} {left right : ExactModel S}
    (leftPresentation : Presentation w rich data left) (rightPresentation : Presentation w rich data right)
    (law : forall event : Event State,
      QProb.Equiv (left.prior.probVal (fun unit => event (leftPresentation.stateOf unit)))
        (right.prior.probVal (fun unit => event (rightPresentation.stateOf unit)))) :
    ObservationallyEquivalent left right := by
  intro event
  let replayEvent : Event State := fun state => event (fun child => data.evalNode w rich state child)
  have leftEvaluation (unit : left.latent.Assignment) :
      event (left.eval unit) = replayEvent (leftPresentation.stateOf unit) :=
    congrArg event (funext (leftPresentation.evalNode_eq w rich unit))
  have rightEvaluation (unit : right.latent.Assignment) :
      event (right.eval unit) = replayEvent (rightPresentation.stateOf unit) :=
    congrArg event (funext (rightPresentation.evalNode_eq w rich unit))
  exact QProb.equiv_trans (left.observationalValue_eq event)
    (QProb.equiv_trans (left.prior.probVal_congr _ _ leftEvaluation)
      (QProb.equiv_trans (law replayEvent)
        (QProb.equiv_trans (QProb.equiv_symm (right.prior.probVal_congr _ _ rightEvaluation))
          (QProb.equiv_symm (right.observationalValue_eq event)))))

/-- Induction keeps the *presentation and state law*, not just equality of
the intermediate observations.  The state type grows with each fresh bit;
the tail can still inspect all backgrounds and earlier noise responses. -/
private theorem observational_plan (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    {State : Type} {data : ReplayData w State} {left right : ExactModel S}
    (leftPresentation : Presentation w rich data left) (rightPresentation : Presentation w rich data right)
    (law : forall event : Event State,
      QProb.Equiv (left.prior.probVal (fun unit => event (leftPresentation.stateOf unit)))
        (right.prior.probVal (fun unit => event (rightPresentation.stateOf unit))))
    (steps : List (HedgeReadoutStep S))
    (allowed : forall step, step ∈ steps -> w.small step.pivot = true ∨ w.large step.pivot = false) :
    ObservationallyEquivalent (left.withHedgeReadouts rich steps) (right.withHedgeReadouts rich steps) := by
  induction steps generalizing State left right with
  | nil => exact observational_of_stateLaw w rich leftPresentation rightPresentation law
  | cons step rest inductionHypothesis =>
      have headAllowed := allowed step List.mem_cons_self
      exact inductionHypothesis
        (leftPresentation.withStep w rich step headAllowed)
        (rightPresentation.withStep w rich step headAllowed)
        (stateLaw_withStep w rich leftPresentation rightPresentation law step headAllowed)
        (fun next listed => allowed next (List.mem_cons_of_mem _ listed))

/-! ## Initial presentations of the original carrier pair -/

private def initialData (w : HedgeWitness G q) : ReplayData w (HedgeCarrierObservedState S) where
  sample := Prod.fst
  backgrounds := fun state => state.2.1
  response := fun _state _child _parents old => old
  outer_identity := fun _state _child _inside _outside _parents _old => rfl

private def largePresentation (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Presentation w rich (initialData w) (w.largeCarrierDefectParityModel rich) where
  stateOf := hedgeCarrierObservedState G (w.largeCarrierDefectParityModel rich).eval
  fits := w.largeCarrierPrivateCoordinatesFit_eval rich
  mechanism_eq := fun unit child parents _unchanged =>
    w.largeCarrierDefectParityModel_mechanism_parent_response rich unit child parents

private def smallPresentation (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Presentation w rich (initialData w) (w.smallCarrierDefectParityModel rich) where
  stateOf := hedgeCarrierObservedState G (w.smallCarrierDefectParityModel rich).eval
  fits := w.smallCarrierPrivateCoordinatesFit_eval rich
  mechanism_eq := by
    intro unit child parents unchanged
    rw [w.smallCarrierDefectParityModel_mechanism_parent_response rich unit child parents]
    change (if w.large child then _ else _) = originalResponse w rich _ _ child parents
    dsimp only [initialData, hedgeCarrierObservedState] at unchanged ⊢
    unfold originalResponse
    cases inside : w.large child with
    | false => simp only [Bool.false_eq_true, if_false]
    | true =>
        simp only [if_true]
        cases selected : w.small child with
        | false => simp only [Bool.false_eq_true, if_false]
        | true =>
            simp only [if_true]
            congr 1
            rw [Bool.xor_assoc, Bool.xor_assoc]
            congr 1
            apply (hedgeForestParentBitsFrom_delta_restrict_eq_of_kept rich w.small w.child child _ _ ?_).symm
            intro parent edge keptAt outside
            exact (unchanged parent edge (w.large_forest.child_edge parent child keptAt).1 outside).symm

end HedgeCarrierReplayPlan

/-- Every finite common hedge readout plan whose pivots are in the small
forest or outside the large forest preserves the *full* observational law of
the positive carrier pair.  Internal pivots may have responding kept children;
outside pivots may feed installed readouts through arbitrary declared edges.

The plan need not be increasing and may repeat a pivot.  The proof preserves
a common mechanism presentation and joint retained-state law through each
actual independent prior extension, rather than assuming equality of the
intermediate observed tables.  Noise support and bias are irrelevant to this
equality result; positivity and interventional separation remain separate
countermodel requirements.  Outer-only pivots are deliberately not covered. -/
theorem HedgeWitness.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_of_small_or_outside
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (allowed : forall step, step ∈ steps -> w.small step.pivot = true ∨ w.large step.pivot = false) :
    ObservationallyEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich steps)
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich steps) :=
  HedgeCarrierReplayPlan.observational_plan w rich
    (HedgeCarrierReplayPlan.largePresentation w rich) (HedgeCarrierReplayPlan.smallPresentation w rich)
    (w.carrierDefectParityModels_observationalState_probVal_equiv rich) steps allowed

end Causality
end Thesis
