import Thesis.Causality.PrivateNoise
import Thesis.CausalTransport.HedgeNoise

namespace Thesis
namespace Causality

open Probability

/-!
# Realizing private noisy hedge readouts as structural models

`HedgeNoise` proves injectivity and support of independent noisy signal
records.  This module realizes one such channel with an actual fresh private
latent source and a full-alphabet observed mechanism.  The new prior is a
checked independent product, and its projection remains the original graph.

For the positive carrier pair, every vertex whose kept forest child is
`none` is ignored by all other mechanisms.  This includes common roots and
vertices outside the large forest.  A common readout at any such pivot
therefore preserves equality of the entire observational laws.  Strict
positivity has a stronger independent proof: at any pivot, even an internal
forest vertex, the explicit restoring bit recovers the whole old target
assignment by topological induction.  Both bit values must have support;
bias is needed for separation, not for full observational positivity.

The interventional theorem equates the new pivot's signal with the exact
independent XOR channel of the old model's readout signal.  Like positivity,
this local equation needs no non-influence assumption: acyclicity leaves all
parents of the pivot unchanged.  This is a genuine SCM-to-channel connection,
rather than a claim that a stand-alone signal record is already a countermodel
for the original query.  Iterated routing must still account for the effect
on later coordinates and connect its sink signal to the hedge's root parity;
unrestricted observational equivalence remains separate.

The companion `HedgeCarrierReplay` proves a stronger one-step equality at any
small-forest pivot, including internal vertices with kept children.  It uses
the joint observed/background state law and replays the responding descendants,
not the sink-based common observable map proved in this module.  Its companion
`HedgeCarrierReplayPlan` now covers arbitrary finite small-or-outside plans by
transporting a mechanism-level invariant, without order or distinct pivots.
Outer-only updates and unrestricted interventional routing remain separate.
-/

variable {S : ObservedSignature.{0}}

/-! ## Forest sinks do not influence another carrier mechanism -/

private theorem forestParentBits_eq_of_child_none
    (rich : ObservedSignature.ValueRich S) (kept : ForestChild S)
    (pivot : Fin S.count) (none : kept pivot = Option.none) (child : Fin S.count)
    (first second : S.ParentValues child)
    (agree : forall parent (edge : S.directed parent child = true), parent ≠ pivot ->
      first parent edge = second parent edge) :
    hedgeForestParentBitsFrom rich kept child first = hedgeForestParentBitsFrom rich kept child second := by
  apply hedgeForestParentBitsFrom_congr_of_kept
  intro parent edge selected
  apply congrArg (hedgeIsSecond rich parent)
  apply agree parent edge
  intro same
  subst parent
  rw [none] at selected
  cases selected

/-- A sink of the kept large-forest map is not read by any other large
carrier mechanism, even if the ambient graph has additional outgoing edges. -/
theorem HedgeWitness.largeCarrierDefectParityModel_otherMechanismsIgnore
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (none : w.child pivot = Option.none) :
    (w.largeCarrierDefectParityModel rich).OtherMechanismsIgnore pivot := by
  intro child _different first second inputs agree
  have parents := forestParentBits_eq_of_child_none rich w.child pivot none child first second agree
  simp only [HedgeWitness.largeCarrierDefectParityModel, hedgeCarrierDefectModel,
    HedgeWitness.largeParityModel, hedgeForestParityModel, hedgeForestParityOutput]
  rw [parents]

/-- The nested small carrier ignores the same pivot: restricting the kept
map cannot introduce an outgoing edge absent from the large map. -/
theorem HedgeWitness.smallCarrierDefectParityModel_otherMechanismsIgnore
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (none : w.child pivot = Option.none) :
    (w.smallCarrierDefectParityModel rich).OtherMechanismsIgnore pivot := by
  intro child _different first second inputs agree
  have outer := forestParentBits_eq_of_child_none rich w.child pivot none child first second agree
  have restricted : restrictChild w.small w.child pivot = Option.none := by simp [restrictChild, none]
  have inner := forestParentBits_eq_of_child_none rich (restrictChild w.small w.child)
    pivot restricted child first second agree
  simp only [HedgeWitness.smallCarrierDefectParityModel, hedgeCarrierDefectModel,
    HedgeWitness.smallParityModel, hedgeNestedForestParityModel, hedgeForestParityOutput]
  rw [outer, inner]

/-! ## One full-alphabet readout and its explicit restoring bit -/

/-- A root may inject its old bit; an ordinary route vertex injects only
the supplied parent signal.  In both cases the independent bit is XORed
before a full-alphabet carrier emits the observed value.  The old coordinate
value supplies the background, so the mechanism is a common observable
transformation and can preserve full observational equality. -/
def hedgeNoisyReadout (rich : ObservedSignature.ValueRich S) (pivot : Fin S.count)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (parents : S.ParentValues pivot) (old : S.Value pivot) (bit : Bool) : S.Value pivot :=
  hedgeParityCarrierValue rich pivot
    (Bool.xor (Bool.xor (if injectOld then hedgeIsSecond rich pivot old else false)
      (parentSignal parents)) bit) old

/-- The pivot's exact bit before independent noise is applied. -/
def hedgeReadoutSignal (rich : ObservedSignature.ValueRich S) (pivot : Fin S.count)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool) (sample : S.Assignment) : Bool :=
  Bool.xor (if injectOld then hedgeIsSecond rich pivot (sample pivot) else false)
    (parentSignal (fun parent _edge => sample parent))

/-- This explicit bit restores the old value, including every background
label outside the two distinguished parity values. -/
def hedgeReadoutRestoreBit (rich : ObservedSignature.ValueRich S) (pivot : Fin S.count)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool) (sample : S.Assignment) : Bool :=
  Bool.xor (hedgeReadoutSignal rich pivot injectOld parentSignal sample)
    (hedgeIsSecond rich pivot (sample pivot))

theorem hedgeNoisyReadout_restore (rich : ObservedSignature.ValueRich S) (pivot : Fin S.count)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool) (sample : S.Assignment) :
    hedgeNoisyReadout rich pivot injectOld parentSignal (fun parent _edge => sample parent)
      (sample pivot) (hedgeReadoutRestoreBit rich pivot injectOld parentSignal sample) = sample pivot := by
  unfold hedgeNoisyReadout hedgeReadoutRestoreBit hedgeReadoutSignal
  have cancels (source target : Bool) : Bool.xor source (Bool.xor source target) = target := by
    cases source <;> cases target <;> rfl
  rw [cancels]
  exact hedgeParityCarrierValue_reconstruct rich pivot (sample pivot)

/-! ## Exact full-value preimages of an injected carrier -/

/-- The old carrier bit forced by a requested new value, at fixed current
parent values and a fixed fresh input.  This inverse is used only when the
readout injects the old bit; a source-free readout has no such inverse. -/
def hedgeReadoutRequiredCarrierBit (rich : ObservedSignature.ValueRich S) (pivot : Fin S.count)
    (parentSignal : S.ParentValues pivot -> Bool) (parents : S.ParentValues pivot)
    (fresh : Bool) (target : S.Value pivot) : Bool :=
  Bool.xor (Bool.xor (hedgeIsSecond rich pivot target) (parentSignal parents)) fresh

/-- The remaining full-label constraint after inverting the injected bit.
The readout uses its old *value* as background, not the original private
background directly.  In particular, an old `second` value has already
erased a third background label: flipping it to bit zero emits `first`,
not that third label.  This common finite predicate retains that distinction
for the two incidence maps in a denominator comparison. -/
def hedgeReadoutCarrierBackgroundFits (rich : ObservedSignature.ValueRich S) (pivot : Fin S.count)
    (parentSignal : S.ParentValues pivot -> Bool) (parents : S.ParentValues pivot)
    (fresh : Bool) (target background : S.Value pivot) : Bool :=
  decide (hedgeParityCarrierValue rich pivot (hedgeIsSecond rich pivot target)
    (hedgeParityCarrierValue rich pivot
      (hedgeReadoutRequiredCarrierBit rich pivot parentSignal parents fresh target) background) = target)

/-- A full readout preimage consists of one recovered source-bit equation
and the separate common background test.  This is an exact equivalence for
every label, including impossible third-label targets; it assumes neither
positivity nor that the observed alphabet is Boolean. -/
theorem hedgeNoisyReadout_carrier_eq_iff
    (rich : ObservedSignature.ValueRich S) (pivot : Fin S.count)
    (parentSignal : S.ParentValues pivot -> Bool) (parents : S.ParentValues pivot)
    (source fresh : Bool) (background target : S.Value pivot) :
    hedgeNoisyReadout rich pivot true parentSignal parents
        (hedgeParityCarrierValue rich pivot source background) fresh = target ↔
      source = hedgeReadoutRequiredCarrierBit rich pivot parentSignal parents fresh target ∧
        hedgeReadoutCarrierBackgroundFits rich pivot parentSignal parents fresh target background = true := by
  have inverse (source signal fresh : Bool) :
      Bool.xor (Bool.xor (Bool.xor (Bool.xor source signal) fresh) signal) fresh = source := by
    cases source <;> cases signal <;> cases fresh <;> rfl
  constructor
  · intro equal
    have bitEqual := congrArg (hedgeIsSecond rich pivot) equal
    simp only [hedgeNoisyReadout, if_true, hedgeIsSecond_parityCarrierValue] at bitEqual
    have recovered : source = hedgeReadoutRequiredCarrierBit rich pivot parentSignal parents fresh target := by
      unfold hedgeReadoutRequiredCarrierBit
      rw [← bitEqual, inverse]
    refine ⟨recovered, ?_⟩
    apply decide_eq_true
    simp only [hedgeNoisyReadout, if_true, hedgeIsSecond_parityCarrierValue] at equal
    rw [bitEqual, recovered] at equal
    exact equal
  · intro parts
    have bitEqual : Bool.xor (Bool.xor source (parentSignal parents)) fresh = hedgeIsSecond rich pivot target := by
      rw [parts.1]
      exact inverse (hedgeIsSecond rich pivot target) (parentSignal parents) fresh
    simp only [hedgeNoisyReadout, if_true, hedgeIsSecond_parityCarrierValue]
    rw [bitEqual, parts.1]
    exact of_decide_eq_true parts.2

/-- Boolean form of the same exact preimage, suitable for weighted finite
fibres.  Replacing this by the source-bit test alone would accept incorrect
full-label targets after a carrier background has been erased. -/
theorem hedgeNoisyReadout_carrier_preimage
    (rich : ObservedSignature.ValueRich S) (pivot : Fin S.count)
    (parentSignal : S.ParentValues pivot -> Bool) (parents : S.ParentValues pivot)
    (source fresh : Bool) (background target : S.Value pivot) :
    decide (hedgeNoisyReadout rich pivot true parentSignal parents
        (hedgeParityCarrierValue rich pivot source background) fresh = target) =
      (decide (source = hedgeReadoutRequiredCarrierBit rich pivot parentSignal parents fresh target) &&
        hedgeReadoutCarrierBackgroundFits rich pivot parentSignal parents fresh target background) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq, Bool.and_eq_true_iff] using
    hedgeNoisyReadout_carrier_eq_iff rich pivot parentSignal parents source fresh background target

/-- Install one readout with a private independent Boolean factor. -/
def FiniteLatentSCM.withHedgeReadout (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool) : ExactModel S :=
  base.withPrivateReadout pivot noise (hedgeNoisyReadout rich pivot injectOld parentSignal)

theorem FiniteLatentSCM.withHedgeReadout_compatible {G : ObservedGraph S}
    (base : ExactModel S) (compatible : Compatible base G) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool) :
    Compatible (base.withHedgeReadout rich pivot noise injectOld parentSignal) G :=
  base.withPrivateBooleanNoise_compatible compatible pivot noise _

/-- Genuine strict observational positivity at any pivot, including an
internal kept-forest vertex.  The explicit restoring bit fixes the whole
old target assignment by topological induction, so positivity needs neither
non-influence nor a common-observable pushforward argument.  Both noise bits
have positive mass; bias is only needed by the separation theorem. -/
theorem FiniteLatentSCM.withHedgeReadout_positive
    (base : ExactModel S) (positive : ObservationallyPositive base) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool) :
    ObservationallyPositive (base.withHedgeReadout rich pivot noise injectOld parentSignal) :=
  base.withPrivateReadout_positive positive pivot noise noisePositive
    (hedgeNoisyReadout rich pivot injectOld parentSignal)
    (hedgeReadoutRestoreBit rich pivot injectOld parentSignal)
    (hedgeNoisyReadout_restore rich pivot injectOld parentSignal)

/-- A common one-step readout preserves the full positive carrier pair's
observational equivalence at any sink of its kept map.  This is a semantic
construction, not an assumed equality of the new observed tables. -/
theorem HedgeWitness.carrierDefectParityModels_withHedgeReadout_observationally_equivalent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (none : w.child pivot = Option.none)
    (noise : FiniteProbRecord Bool) (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool) :
    ObservationallyEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadout rich pivot noise injectOld parentSignal)
      ((w.smallCarrierDefectParityModel rich).withHedgeReadout rich pivot noise injectOld parentSignal) :=
  FiniteLatentSCM.withPrivateReadout_observationally_equivalent _ _
    (w.carrierDefectParityModels_observationally_equivalent rich) pivot noise
    (hedgeNoisyReadout rich pivot injectOld parentSignal)
    (w.largeCarrierDefectParityModel_otherMechanismsIgnore rich pivot none)
    (w.smallCarrierDefectParityModel_otherMechanismsIgnore rich pivot none)

/-! ## The actual interventional pivot realizes the independent signal channel -/

/-- The new observed pivot bit has exactly the probability of the old
readout signal passed through the supplied independent XOR channel.
Interventions elsewhere are arbitrary, and the full old latent record is
retained.  Only freedom of the pivot is needed: all its parents are earlier,
so replacing it cannot change those inputs.  Its later children may change,
including children inside the kept forest; this one-coordinate event never
assumes that the complete updated assignment is a common observed map. -/
theorem FiniteLatentSCM.withHedgeReadout_signal_equiv
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (free : intervention pivot = none) :
    QProb.Equiv
      ((base.withHedgeReadout rich pivot noise injectOld parentSignal).interventionalValue
        intervention (fun sample => hedgeIsSecond rich pivot (sample pivot)))
      ((base.noisyInterventionalSignal intervention
        (hedgeReadoutSignal rich pivot injectOld parentSignal) noise).probVal id) := by
  let model := base.withHedgeReadout rich pivot noise injectOld parentSignal
  let event := fun sample : S.Assignment => hedgeIsSecond rich pivot (sample pivot)
  let signal := fun latent => hedgeReadoutSignal rich pivot injectOld parentSignal
    (base.evalUnder intervention latent)
  have evaluation (pair : Bool × base.latent.Assignment) :
      event (model.evalUnder intervention (PrivateBooleanNoise.assignment base.latent pair.1 pair.2)) =
        Bool.xor (signal pair.2) pair.1 := by
    change hedgeIsSecond rich pivot ((base.withPrivateReadout pivot noise
      (hedgeNoisyReadout rich pivot injectOld parentSignal)).evalUnder intervention
      (PrivateBooleanNoise.assignment base.latent pair.1 pair.2) pivot) = _
    change hedgeIsSecond rich pivot ((base.withPrivateReadout pivot noise
      (hedgeNoisyReadout rich pivot injectOld parentSignal)).evalNodeUnder intervention
      (PrivateBooleanNoise.assignment base.latent pair.1 pair.2) pivot) = _
    rw [base.withPrivateReadout_evalNodeUnder_pivot pivot noise
      (hedgeNoisyReadout rich pivot injectOld parentSignal) intervention free pair.2 pair.1]
    simp only [hedgeNoisyReadout, hedgeIsSecond_parityCarrierValue]
    rfl
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun latent => event (model.evalUnder intervention latent))
  have channel := (noise.product base.prior).probVal_congr _ _ evaluation
  exact QProb.equiv_trans (model.interventionalValue_eq intervention event)
    (QProb.equiv_trans pushed (QProb.equiv_trans channel
      (base.prior.xorChannel_noise_first_probVal signal noise)))

/-- A biased private readout retains any old interventional signal gap in
the actual new SCMs, even at an internal vertex read by other mechanisms.
The excess stay mass is explicit and strictly positive, so fair noise cannot
be used as a separator.  Positive support is independent; observational
equality of the new pair still requires its own proof and is not supplied
by this local interventional-separation theorem. -/
theorem FiniteLatentSCM.withHedgeReadout_signal_not_equiv
    (left right : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (injectOld : Bool) (parentSignal : S.ParentValues pivot -> Bool)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (free : intervention pivot = none) (gap : Nat) (gapPositive : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap)
    (separated : Not (QProb.Equiv
      (left.interventionalValue intervention (hedgeReadoutSignal rich pivot injectOld parentSignal))
      (right.interventionalValue intervention (hedgeReadoutSignal rich pivot injectOld parentSignal)))) :
    Not (QProb.Equiv
      ((left.withHedgeReadout rich pivot noise injectOld parentSignal).interventionalValue
        intervention (fun sample => hedgeIsSecond rich pivot (sample pivot)))
      ((right.withHedgeReadout rich pivot noise injectOld parentSignal).interventionalValue
        intervention (fun sample => hedgeIsSecond rich pivot (sample pivot)))) := by
  intro equivalent
  have channel := QProb.equiv_trans
    (QProb.equiv_symm (left.withHedgeReadout_signal_equiv rich pivot noise injectOld parentSignal
      intervention free))
    (QProb.equiv_trans equivalent
      (right.withHedgeReadout_signal_equiv rich pivot noise injectOld parentSignal
        intervention free))
  exact separated ((FiniteLatentSCM.noisyInterventionalSignal_equiv_iff_of_bias
    left right intervention (hedgeReadoutSignal rich pivot injectOld parentSignal)
    noise gap gapPositive bias).mp channel)

end Causality
end Thesis
