import Thesis.CausalTransport.HedgeReadout

namespace Thesis
namespace Causality

open Probability

/-!
# Finite topologically ordered private hedge readouts

A one-vertex readout is not enough for a routed hedge countermodel.  Each
later update must still have the non-influence property used to identify
its complete observational law with a common observable pushforward.
This module proves that invariant for an arbitrary finite increasing list
of readouts, rather than supplying it separately at each intermediate SCM.

The list is explicit data.  Each step retains its own noise record, optional
old-bit injection, and declared-parent signal.  Its fold constructs actual
SCMs with their successive independent product priors.  Compatibility,
strict positivity, and equality of the entire observed laws are then proved
uniformly for the fold.  Noise records need not be the same at different
vertices, and the observed alphabet is not restricted to Boolean values.

For the positive carrier pair the initial non-influence proofs follow from
the kept-child map: the permitted pivots are forest roots and vertices
outside the forest.  Earlier updates cannot read a later pivot because the
signature is topologically ordered.  This closes the observational and
support invariants of finite routing; it does not yet identify a routed
outcome signal with root parity or cover re-entry into an internal forest
vertex.  Those are distinct interventional obligations.
`HedgeReadoutPullback` is the companion that now carries linear parity events
back through arbitrary such plans, and `HedgeRoutedCounterexample` combines
the two invariants once the pure routing identity has been established.
-/

variable {S : ObservedSignature.{0}}

/-- One observable readout instruction, with its own independent noise.
Only declared parent values are available to the signal function. -/
structure HedgeReadoutStep (S : ObservedSignature.{0}) where
  pivot : Fin S.count
  noise : FiniteProbRecord Bool
  injectOld : Bool
  parentSignal : S.ParentValues pivot -> Bool

/-- Install the instruction in an actual SCM, not in an isolated signal
record.  The latent space grows by one private Boolean coordinate. -/
def HedgeReadoutStep.apply (step : HedgeReadoutStep S) (rich : ObservedSignature.ValueRich S)
    (base : ExactModel S) : ExactModel S :=
  base.withHedgeReadout rich step.pivot step.noise step.injectOld step.parentSignal

/-- Execute instructions from left to right.  The empty plan leaves the
base model unchanged, and every nonempty step uses the previous SCM's real
prior and mechanisms. -/
def FiniteLatentSCM.withHedgeReadouts (base : ExactModel S) (rich : ObservedSignature.ValueRich S) :
    List (HedgeReadoutStep S) -> ExactModel S
  | [] => base
  | step :: rest => (step.apply rich base).withHedgeReadouts rich rest

/-- A common finite readout plan preserves projected-graph compatibility,
independently of its order, support, and choice of parent signals. -/
theorem FiniteLatentSCM.withHedgeReadouts_compatible {G : ObservedGraph S}
    (base : ExactModel S) (compatible : Compatible base G) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S)) : Compatible (base.withHedgeReadouts rich steps) G := by
  induction steps generalizing base with
  | nil => exact compatible
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis (step.apply rich base)
        (base.withHedgeReadout_compatible compatible rich step.pivot step.noise step.injectOld step.parentSignal)

/-- Every already installed earlier readout leaves non-influence of a
future coordinate intact.  No readout signal can obtain a backward parent
edge, even when it uses all parents allowed by the ambient signature. -/
theorem FiniteLatentSCM.withHedgeReadouts_otherMechanismsIgnore
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S)) (later : Fin S.count)
    (ignored : base.OtherMechanismsIgnore later)
    (earlier : forall step, step ∈ steps -> step.pivot.val < later.val) :
    (base.withHedgeReadouts rich steps).OtherMechanismsIgnore later := by
  induction steps generalizing base with
  | nil => exact ignored
  | cons step rest inductionHypothesis =>
      apply inductionHypothesis (step.apply rich base)
      · exact base.withPrivateBooleanNoise_otherMechanismsIgnore_of_earlier step.pivot later step.noise
          _ ignored (earlier step (List.mem_cons_self))
      · intro next listed
        exact earlier next (List.mem_cons_of_mem _ listed)

/-- All later instructions remain ready after installing the first one.
The initial model need only ignore their pivots before any updates; strict
topological order transports those proofs through each new mechanism. -/
private theorem tail_ignored (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (step : HedgeReadoutStep S) (rest : List (HedgeReadoutStep S))
    (ordered : (step :: rest).Pairwise (fun first second => first.pivot.val < second.pivot.val))
    (ignored : forall next, next ∈ step :: rest -> base.OtherMechanismsIgnore next.pivot) :
    forall next, next ∈ rest -> (step.apply rich base).OtherMechanismsIgnore next.pivot := by
  intro next listed
  exact base.withPrivateBooleanNoise_otherMechanismsIgnore_of_earlier step.pivot next.pivot step.noise
    _ (ignored next (List.mem_cons_of_mem _ listed)) ((List.pairwise_cons.mp ordered).1 next listed)

/-- Full observational positivity survives any finite increasing readout
plan.  The restoring bit is the explicit carrier restoring function at
each step; it is never selected from a proposition.  Both noise bits must
have positive mass, but their denominators and biases may vary by step. -/
theorem FiniteLatentSCM.withHedgeReadouts_positive
    (base : ExactModel S) (positive : ObservationallyPositive base) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (ordered : steps.Pairwise (fun first second => first.pivot.val < second.pivot.val))
    (ignored : forall step, step ∈ steps -> base.OtherMechanismsIgnore step.pivot)
    (noisePositive : forall step, step ∈ steps ->
      forall bit, step.noise.EventPositive (FiniteProbRecord.singletonEvent bit)) :
    ObservationallyPositive (base.withHedgeReadouts rich steps) := by
  induction steps generalizing base with
  | nil => exact positive
  | cons step rest inductionHypothesis =>
      apply inductionHypothesis (step.apply rich base)
      · exact base.withHedgeReadout_positive positive rich step.pivot step.noise
          (noisePositive step List.mem_cons_self) step.injectOld step.parentSignal
          (ignored step List.mem_cons_self)
      · exact (List.pairwise_cons.mp ordered).2
      · exact tail_ignored base rich step rest ordered ignored
      · intro next listed
        exact noisePositive next (List.mem_cons_of_mem _ listed)

/-- A finite common increasing plan preserves equality of the complete
observational laws, even when the original latent spaces differ.

Induction invokes the common-observable pushforward theorem on the actual
updated models.  The tail invariant above supplies their non-influence
proofs; observational equality is not an unproved hypothesis attached to
each new intermediate pair. -/
theorem FiniteLatentSCM.withHedgeReadouts_observationally_equivalent
    (left right : ExactModel S) (observational : ObservationallyEquivalent left right)
    (rich : ObservedSignature.ValueRich S) (steps : List (HedgeReadoutStep S))
    (ordered : steps.Pairwise (fun first second => first.pivot.val < second.pivot.val))
    (leftIgnored : forall step, step ∈ steps -> left.OtherMechanismsIgnore step.pivot)
    (rightIgnored : forall step, step ∈ steps -> right.OtherMechanismsIgnore step.pivot) :
    ObservationallyEquivalent (left.withHedgeReadouts rich steps) (right.withHedgeReadouts rich steps) := by
  induction steps generalizing left right with
  | nil => exact observational
  | cons step rest inductionHypothesis =>
      apply inductionHypothesis (step.apply rich left) (step.apply rich right)
      · exact FiniteLatentSCM.withPrivateReadout_observationally_equivalent left right observational
          step.pivot step.noise _ (leftIgnored step List.mem_cons_self) (rightIgnored step List.mem_cons_self)
      · exact (List.pairwise_cons.mp ordered).2
      · exact tail_ignored left rich step rest ordered leftIgnored
      · exact tail_ignored right rich step rest ordered rightIgnored

/-! ## Discharging the initial invariant for positive hedge carriers -/

/-- Every finite increasing plan at sinks of the kept forest map preserves
the full carrier pair's observational equality.  Roots and outside-forest
pivots may be mixed in one plan; no intermediate model invariants are
requested from the caller.  Interventional routing is deliberately separate. -/
theorem HedgeWitness.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (ordered : steps.Pairwise (fun first second => first.pivot.val < second.pivot.val))
    (sinks : forall step, step ∈ steps -> w.child step.pivot = none) :
    ObservationallyEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich steps)
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich steps) :=
  FiniteLatentSCM.withHedgeReadouts_observationally_equivalent _ _
    (w.carrierDefectParityModels_observationally_equivalent rich) rich steps ordered
    (fun step listed => w.largeCarrierDefectParityModel_otherMechanismsIgnore rich step.pivot (sinks step listed))
    (fun step listed => w.smallCarrierDefectParityModel_otherMechanismsIgnore rich step.pivot (sinks step listed))

end Causality
end Thesis
