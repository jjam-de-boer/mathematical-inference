import Thesis.CausalTransport.HedgeChannelBackgroundFactorization
import Thesis.CausalTransport.HedgeChannelEnvironmentCounterexample
import Thesis.Probability.FiniteRatioPerturbation

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability
open HedgeChannelInstallation

/-!
# Background-weighted conditional gaps after full environment integration

The general action-cut product identity holds at every frozen independent
environment.  Here it is summed over the *actual complete* environment and
observed event supports.  The two resulting integer sums describe the left
background mass and the full-small interaction mass.  Their common scalar
is the literal ordinary main-prior denominator, including all inactive slots.

These sums are connected to the existing natural event numerators of the
widened, positive, observationally equal model pair.  Consequently a
conditional cell separates exactly when the joint interaction times the old
conditioning background differs from the old joint background times the
conditioning interaction.  Both conditioning masses may change.

The supplied signals still read only typed directed parents and incident
environment bits.  Calling their full-support sums "background" and
"interaction" does not give a local mechanism a global environment read.
The common scalar is cancelled only in an integer equality and only after
its strictly positive actual denominator is proved nonzero.

The final constructor lifts a proved background-weighted gap to a positive
countermodel pair on every original label.  It does not itself construct
signals for an arbitrary terminal active path: that remaining graph-to-
nonzero-interaction theorem is the next load-bearing conditional obligation.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-- Complete old background event mass, after every independent environment
and every selected observed sample is included once.  Small rows retain
their actual capacity indicators; forced conflicts have not been removed. -/
def backgroundEventSum (w : HedgeWitness G q) (backgroundSignal : ParentSignal G)
    (target : Fin S.count -> Option Bool) (event : Event S.binary.Assignment) : Int :=
  ((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
    ((S.binary.assignmentEnumeration.filter event).map (fun sample =>
      smallCapacityProductUnder w target sample *
        outsideBackgroundProductUnder w (frozenParentSignal backgroundSignal environment) target sample)).sum)).sum

/-- Complete signed interaction on the same environment and event support.
This is the actual full-small contribution, not one chosen background mask,
an assumed positive perturbation or a replacement conditional denominator. -/
def interactionEventSum (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal G)
    (target : Fin S.count -> Option Bool) (event : Event S.binary.Assignment) : Int :=
  ((PairRootChannels.Environment.enumeration G.binary).map (fun environment =>
    ((S.binary.assignmentEnumeration.filter event).map (fun sample =>
      smallAmplitudeProductUnder w target sample *
        FiniteProbRecord.characterSign
          (signalPhase w.small (frozenParentSignal smallSignal environment) sample) *
        outsideBackgroundProductUnder w (frozenParentSignal backgroundSignal environment) target sample)).sum)).sum

private theorem natSum_cast {α : Type u} (values : List α) (term : α -> Nat) :
    ((values.map term).sum : Int) = (values.map (fun value => (term value : Int))).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, Int.natCast_add, inductionHypothesis]

/-- The background sum is exactly the widened left model's natural event
numerator after the action cut, up to its positive literal main-prior mass.
All observed event coordinates and all independent environments are retained. -/
theorem leftEventNumerator_eq_backgroundEventSum_of_action
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) (target : Fin S.count -> Option Bool)
    (fixed : Bool) (forced : target w.actionSeed = some fixed) (event : Event S.binary.Assignment) :
    (leftEventNumerator w rich smallSignal backgroundSignal target event : Int) =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        backgroundEventSum w backgroundSignal target event := by
  unfold leftEventNumerator backgroundEventSum HedgeChannelTable.eventNumerator
  simp only [natSum_cast]
  rw [← FiniteSupportedSum.sum_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro environment _listed
  rw [← FiniteSupportedSum.sum_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sample _selected
  simpa only [Int.mul_assoc] using
    left_integratedNumerator_eq_backgroundProduct_of_action w rich
      (frozenParentSignal smallSignal environment) (frozenParentSignal backgroundSignal environment)
      target fixed forced sample

/-- The complete right event change is the integrated full-small interaction
sum, with the same literal prior scalar as the old background event mass.
The equality applies to the joint and conditioning cylinders independently. -/
theorem eventNumerators_difference_eq_interactionEventSum_of_action
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) (target : Fin S.count -> Option Bool)
    (fixed : Bool) (forced : target w.actionSeed = some fixed) (event : Event S.binary.Assignment) :
    (rightEventNumerator w smallSignal backgroundSignal target event : Int) =
      (leftEventNumerator w rich smallSignal backgroundSignal target event : Int) +
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        interactionEventSum w smallSignal backgroundSignal target event := by
  unfold rightEventNumerator leftEventNumerator interactionEventSum HedgeChannelTable.eventNumerator
  simp only [natSum_cast]
  rw [← FiniteSupportedSum.sum_mul_left, ← FiniteSupportedSum.sum_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro environment _listed
  rw [← FiniteSupportedSum.sum_mul_left, ← FiniteSupportedSum.sum_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sample _selected
  simpa only [Int.mul_assoc] using
    integratedNumerators_difference_eq_backgroundProduct_of_action w rich
      (frozenParentSignal smallSignal environment) (frozenParentSignal backgroundSignal environment)
      target fixed forced sample

/-- Necessary and sufficient complete cross-product test in background/
interaction coordinates.  This is not a frozen-environment conditional
test: all integrations precede the cross-products.  Both actual event changes
are retained, and only the positive ordinary main-prior scalar is cancelled. -/
theorem event_cross_eq_iff_background_balanced_of_action
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) (target : Fin S.count -> Option Bool)
    (fixed : Bool) (forced : target w.actionSeed = some fixed)
    (joint condition : Event S.binary.Assignment) :
    leftEventNumerator w rich smallSignal backgroundSignal target joint *
        rightEventNumerator w smallSignal backgroundSignal target condition =
      rightEventNumerator w smallSignal backgroundSignal target joint *
        leftEventNumerator w rich smallSignal backgroundSignal target condition ↔
      interactionEventSum w smallSignal backgroundSignal target joint *
          backgroundEventSum w backgroundSignal target condition =
        backgroundEventSum w backgroundSignal target joint *
          interactionEventSum w smallSignal backgroundSignal target condition := by
  let priorMass : Int := (PairRootChannels.prior G.binary (channelCount w)).den
  have priorNonzero : priorMass ≠ 0 := by
    have positive := (PairRootChannels.prior G.binary (channelCount w)).den_pos
    dsimp only [priorMass]
    omega
  have priorSquareNonzero : priorMass * priorMass ≠ 0 := by
    intro zero
    rcases Int.mul_eq_zero.mp zero with first | second
    · exact priorNonzero first
    · exact priorNonzero second
  rw [FiniteRatioPerturbation.cross_eq_iff_balanced _ _ _ _
    (priorMass * interactionEventSum w smallSignal backgroundSignal target joint)
    (priorMass * interactionEventSum w smallSignal backgroundSignal target condition)
    (eventNumerators_difference_eq_interactionEventSum_of_action w rich smallSignal backgroundSignal target fixed forced joint)
    (eventNumerators_difference_eq_interactionEventSum_of_action w rich smallSignal backgroundSignal target fixed forced condition),
    leftEventNumerator_eq_backgroundEventSum_of_action w rich smallSignal backgroundSignal target fixed forced condition,
    leftEventNumerator_eq_backgroundEventSum_of_action w rich smallSignal backgroundSignal target fixed forced joint]
  have regroup (first second : Int) : (priorMass * first) * (priorMass * second) =
      (priorMass * priorMass) * (first * second) := by ac_rfl
  change (priorMass * _) * (priorMass * _) = (priorMass * _) * (priorMass * _) ↔ _
  rw [regroup, regroup]
  constructor
  · exact Int.eq_of_mul_eq_mul_left priorSquareNonzero
  · intro equal
    exact congrArg ((priorMass * priorMass) * ·) equal

variable {query : ConditionalKernelQuery S}

/-- Build a full original-alphabet conditional countermodel from the actual
nonbalanced background-weighted interaction.  Positivity, whole observed-law
equality and every original query coordinate are inherited from the widened
installation and explicit label refinement, not added as arithmetic premises. -/
noncomputable def conditionalCounterexampleOfBackgroundChange
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal G) (reference : S.binary.Assignment)
    (separated : interactionEventSum w smallSignal backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.numeratorEvent reference) *
        backgroundEventSum w backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.conditionEvent reference) ≠
      backgroundEventSum w backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.numeratorEvent reference) *
        interactionEventSum w smallSignal backgroundSignal
          (query.binary.operationKernel.intervention reference) (query.binary.operationKernel.conditionEvent reference)) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query := by
  apply conditionalCounterexampleOfCross (S := S) (G := G) (query := query) w rich smallSignal backgroundSignal reference
  intro equal
  apply separated
  apply (event_cross_eq_iff_background_balanced_of_action w rich smallSignal backgroundSignal
    (query.binary.operationKernel.intervention reference) (reference w.actionSeed) ?_
    (query.binary.operationKernel.numeratorEvent reference) (query.binary.operationKernel.conditionEvent reference)).mp equal
  change (if query.action w.actionSeed then some (reference w.actionSeed) else none) = some (reference w.actionSeed)
  rw [show query.action w.actionSeed = true from w.actionSeed_in_action]
  rfl

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
