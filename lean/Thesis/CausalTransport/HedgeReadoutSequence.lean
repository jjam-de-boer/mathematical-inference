import Thesis.CausalTransport.HedgeReadout

namespace Thesis
namespace Causality

open Probability

/-!
# Finite topologically ordered private hedge readouts

A one-vertex readout is not enough for a routed hedge countermodel.  In the
sink-based construction treated here, each later update retains the
non-influence property used to identify its complete observational law with
a common observable pushforward.  This module proves that invariant for an
arbitrary finite increasing list, rather than supplying it separately at
each intermediate SCM.  `HedgeCarrierReplayPlan` now gives a different
mechanism-level invariant for small-or-outside pivots: its full-law theorem
includes responding children, arbitrary order, and repeated updates.

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
non-influence invariants of finite routing; it does not yet identify a routed
outcome signal with root parity or cover re-entry into an internal forest
vertex.  Those are distinct interventional obligations.
`HedgeReadoutPullback` is the companion that now carries linear parity events
back through arbitrary such plans, and `HedgeRoutedCounterexample` combines
the two invariants once the pure routing identity has been established.

An additional preservation theorem covers arbitrary events and joint kernels
whose inspected coordinates are outside every readout pivot.  The intervention
need not leave the pivots free.  Each independent fresh factor integrates out
of such an event, so the same routed carrier pair retains any conditioning
denominator outside its original large forest and the modified route nodes.
`HedgeConditionalReadout` combines this with the canonical routed numerator
countermodel; a merely failed numerator is never treated as conditional
non-identifiability without proving the required denominator agreement.
The companion `HedgeReadoutPreservation` replaces this global non-influence
premise by closure of just the inspected mechanisms.  Its protected-marginal
theorem allows responding unprotected descendants, arbitrary instruction
order, and repeated pivots with distinct actual fresh factors.

Positivity no longer uses the increasing-plan invariant.  The stronger
restoring theorem in `PrivateNoise` fixes each old target assignment even
when other mechanisms read the pivot.  Consequently every finite supported
readout plan preserves full support, including internal forest pivots,
descending order, and repeated updates.  These support facts do not remove
the observational or interventional premises from the countermodel theorem.
The replay companion removes the observational sink/order premises on its
permitted pivots; the interventional event pullback remains separate.
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

/-- Events on nodes outside an increasing readout plan keep their original
interventional probabilities.  Each update may inspect the declared parents
and inject its old value, but all other mechanisms ignore that step's pivot.
Topological order transports this invariant to every intermediate SCM.

The intervention is arbitrary, including an empty action or an action that
fixes a readout pivot.  Neither positivity nor noise bias is needed for this
preservation statement.  Conditional countermodels use it to retain their
conditioning denominator in the very same routed model pair, rather than
borrowing equality from the unmodified pair or assuming identifiability. -/
theorem FiniteLatentSCM.withHedgeReadouts_interventionalValue_equiv_of_off
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (ordered : steps.Pairwise (fun first second => first.pivot.val < second.pivot.val))
    (ignored : forall step, step ∈ steps -> base.OtherMechanismsIgnore step.pivot)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (nodes : NodeSet S) (off : forall step, step ∈ steps -> nodes step.pivot = false)
    (event : S.Assignment -> Bool) (eventLocal : EventDependsOnlyOn nodes event) :
    QProb.Equiv ((base.withHedgeReadouts rich steps).interventionalValue intervention event)
      (base.interventionalValue intervention event) := by
  induction steps generalizing base with
  | nil => exact QProb.equiv_refl _
  | cons step rest inductionHypothesis =>
      have tail := inductionHypothesis (step.apply rich base)
        (List.pairwise_cons.mp ordered).2 (tail_ignored base rich step rest ordered ignored)
        (fun next listed => off next (List.mem_cons_of_mem _ listed))
      have head : QProb.Equiv ((step.apply rich base).interventionalValue intervention event)
          (base.interventionalValue intervention event) :=
        base.withPrivateBooleanNoise_interventionalValue_equiv_of_off step.pivot step.noise _
          (ignored step List.mem_cons_self) intervention nodes (off step List.mem_cons_self) event eventLocal
      exact QProb.equiv_trans tail head

/-- Every joint kernel whose outcome is off the readout pivots is unchanged
by the whole plan.  The action is unrestricted.  Agreement cylinders depend
only on the queried outcome, so the event theorem applies at every reference
assignment.  Both branches of kernel semantics are covered explicitly: a
nonempty action uses its intervention, and an empty action uses the ordinary
observational law, equivalently evaluation under no intervention.

This lifts event preservation to supported probability-term results.  It is
therefore suitable for a conditional denominator even when that denominator
is not identifiable across the selected graph model class. -/
theorem JointKernelQuery.withHedgeReadouts_valueEquivalent_of_off
    (query : JointKernelQuery S) (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (ordered : steps.Pairwise (fun first second => first.pivot.val < second.pivot.val))
    (ignored : forall step, step ∈ steps -> base.OtherMechanismsIgnore step.pivot)
    (off : forall step, step ∈ steps -> query.outcome step.pivot = false) :
    query.ValueEquivalent (base.withHedgeReadouts rich steps) base := by
  intro reference
  let updated := base.withHedgeReadouts rich steps
  let kernel := query.operationKernel
  let event := Kernel.agreesOn query.outcome reference
  have eventLocal : EventDependsOnlyOn query.outcome event := by
    intro first second agree
    exact Kernel.agreesOn_sample_congr query.outcome reference first second agree
  have preserved (intervention : (node : Fin S.count) -> Option (S.Value node)) :
      QProb.Equiv (updated.interventionalValue intervention event)
        (base.interventionalValue intervention event) :=
    base.withHedgeReadouts_interventionalValue_equiv_of_off rich steps ordered ignored
      intervention query.outcome off event eventLocal
  have cylinderEqual : QProb.Equiv
      ((kernel.distribution updated reference).probVal event)
      ((kernel.distribution base reference).probVal event) := by
    unfold Kernel.distribution
    split
    · exact preserved (kernel.intervention reference)
    · exact preserved (FiniteLatentSCM.noIntervention S)
  exact ⟨ProbabilityResult.trans
    (Kernel.unconditionalDenote updated query.outcome query.action reference)
    (ProbabilityResult.trans (.value cylinderEqual)
      (ProbabilityResult.symm (Kernel.unconditionalDenote base query.outcome query.action reference)))⟩

/-- Full observational positivity survives every finite readout plan,
regardless of order or repeated pivots.  The explicit restoring bit at each
step recovers the whole old target assignment, even if an internal pivot is
read by other mechanisms.  Neither the initial non-influence invariant nor
its ordered transport is needed for this support theorem.

Both noise bits must have positive mass, but their denominators and biases
may vary by step.  This does not prove observational equality of two models:
that separate theorem below still needs the increasing non-influence plan. -/
theorem FiniteLatentSCM.withHedgeReadouts_positive
    (base : ExactModel S) (positive : ObservationallyPositive base) (rich : ObservedSignature.ValueRich S)
    (steps : List (HedgeReadoutStep S))
    (noisePositive : forall step, step ∈ steps ->
      forall bit, step.noise.EventPositive (FiniteProbRecord.singletonEvent bit)) :
    ObservationallyPositive (base.withHedgeReadouts rich steps) := by
  induction steps generalizing base with
  | nil => exact positive
  | cons step rest inductionHypothesis =>
      apply inductionHypothesis (step.apply rich base)
      · exact base.withHedgeReadout_positive positive rich step.pivot step.noise
          (noisePositive step List.mem_cons_self) step.injectOld step.parentSignal
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

/-- The routed positive carrier pair still agrees on every kernel whose
outcome is outside both the original large forest and all modified pivots.

Outside the large forest, the unmodified pair has pointwise equal outputs
under arbitrary interventions.  Each side of the readout plan separately
preserves those outcome cylinders, by the off-pivot kernel theorem above.
Composition therefore proves equality for the actual updated pair, although
its two augmented latent spaces need not be identified.  This is the matched
denominator needed by a routed conditional counterexample; graphical
descendants are allowed, and denominator identifiability is not assumed. -/
theorem HedgeWitness.carrierDefectParityModels_withHedgeReadouts_valueEquivalent_of_outsideLarge_of_off
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S) (steps : List (HedgeReadoutStep S))
    (ordered : steps.Pairwise (fun first second => first.pivot.val < second.pivot.val))
    (sinks : forall step, step ∈ steps -> w.child step.pivot = none)
    (outside : NodeSet.Disjoint query.outcome w.large)
    (off : forall step, step ∈ steps -> query.outcome step.pivot = false) :
    query.ValueEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich steps)
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich steps) := by
  intro reference
  rcases (query.withHedgeReadouts_valueEquivalent_of_off (w.largeCarrierDefectParityModel rich)
    rich steps ordered
    (fun step listed => w.largeCarrierDefectParityModel_otherMechanismsIgnore rich step.pivot (sinks step listed))
    off) reference with ⟨leftPreserved⟩
  rcases (w.carrierDefectParityModels_valueEquivalent_outsideLarge rich query outside) reference with ⟨originalEqual⟩
  rcases (query.withHedgeReadouts_valueEquivalent_of_off (w.smallCarrierDefectParityModel rich)
    rich steps ordered
    (fun step listed => w.smallCarrierDefectParityModel_otherMechanismsIgnore rich step.pivot (sinks step listed))
    off) reference with ⟨rightPreserved⟩
  exact ⟨ProbabilityResult.trans leftPreserved
    (ProbabilityResult.trans originalEqual (ProbabilityResult.symm rightPreserved))⟩

end Causality
end Thesis
