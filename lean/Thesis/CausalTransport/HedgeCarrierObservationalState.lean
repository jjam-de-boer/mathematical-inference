import Thesis.CausalTransport.HedgePartialIncidenceProbability

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature}

/-!
# The observable carrier law together with retained private state

Equality of the carrier pair's observed laws is not enough to replay an
internal structural update.  A distinguished `second` output conceals its
private background label.  If a later parent change flips that output bit,
the mechanism emits a value using the concealed background, not a label
recoverable from the old observed assignment alone.

This module proves equality of a stronger *joint* law: the entire observed
assignment, every original private background coordinate, and the weighted
defect bit.  These are the unchanged SCMs and their actual priors.  Pair-root
coordinates are intentionally not retained: their two incidence maps differ,
and their equal admissible fibre counts are what establish the joint law.

The first theorem keeps an arbitrary background/defect predicate attached
to each observed singleton.  Exact semantic support pulls it back to one
fixed-defect stratum, a pair-root fibre, and a common background test.  The
weighted product count and the existing full-fibre comparison then give
equal natural masses.  A constructive finite enumeration lifts the result
to every event on the joint state, including predicates coupling background
coordinates with observations.  No independence from the observations is
assumed; the retained defect is generally determined by observed root parity.

This is the joint-law premise needed for a common structural replay with
private backgrounds.  It does not itself assert that an arbitrary internal
readout is such a replay, or close the unrestricted routing theorem.
-/

/-! ## Exact singleton pullback with an arbitrary retained-state test -/

private theorem target_private_pullback (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment) (defect : Bool)
    (pairTest : (Fin (pairRootCount G) -> Bool) -> Bool)
    (output : ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) -> S.Assignment)
    (support : forall unit, output unit = target ↔
      hedgeDefectBitOf G unit = defect ∧
        pairTest (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) = true ∧
        hedgeCarrierPrivateCoordinatesFit rich outer target
          (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) = true)
    (privateTest : Bool -> HedgePrivateCoordinates S -> Bool)
    (unit : (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) :
    (FiniteProbRecord.singletonEvent target (output unit) &&
      privateTest (hedgeDefectBitOf G unit)
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit))) =
      (hedgeDefectStratum G defect unit &&
        (pairTest (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) &&
          (hedgeCarrierPrivateCoordinatesFit rich outer target
            (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) &&
            privateTest defect (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit))))) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro selected
    have parts := Bool.and_eq_true_iff.mp selected
    have evaluates : output unit = target := of_decide_eq_true parts.1
    have tests := (support unit).mp evaluates
    have retained := parts.2
    rw [tests.1] at retained
    refine Bool.and_eq_true_iff.mpr ⟨?_, Bool.and_eq_true_iff.mpr
      ⟨tests.2.1, Bool.and_eq_true_iff.mpr ⟨tests.2.2, retained⟩⟩⟩
    exact beq_iff_eq.mpr tests.1
  · intro selected
    have parts := Bool.and_eq_true_iff.mp selected
    have pairPrivate := Bool.and_eq_true_iff.mp parts.2
    have privateParts := Bool.and_eq_true_iff.mp pairPrivate.2
    have defectEq : hedgeDefectBitOf G unit = defect := beq_iff_eq.mp parts.1
    have evaluates := (support unit).mpr ⟨defectEq, pairPrivate.1, privateParts.1⟩
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true evaluates, ?_⟩
    rw [defectEq]
    exact privateParts.2

/-- Observed singleton masses remain equal after attaching any common
predicate of all private backgrounds and the defect.  In particular the
predicate need not be rectangular, independent of the target, or confined
to Boolean background labels.

The target determines the same defect on both sides.  Its actual weight
(`2` or `1`) and all permitted background multiplicities are retained by the
fixed-stratum product formula, rather than replaced by a fair prior. -/
theorem HedgeWitness.carrierDefectParityModels_observational_target_private_eventMass_eq
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) (privateTest : Bool -> HedgePrivateCoordinates S -> Bool) :
    FiniteProbRecord.eventMass (w.largeCarrierDefectParityModel rich).prior.atoms
        (fun unit => FiniteProbRecord.singletonEvent target
          ((w.largeCarrierDefectParityModel rich).eval unit) &&
          privateTest (hedgeDefectBitOf G unit)
            (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit))) =
      FiniteProbRecord.eventMass (w.smallCarrierDefectParityModel rich).prior.atoms
        (fun unit => FiniteProbRecord.singletonEvent target
          ((w.smallCarrierDefectParityModel rich).eval unit) &&
          privateTest (hedgeDefectBitOf G unit)
            (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit))) := by
  have largeSupport (unit) : (w.largeCarrierDefectParityModel rich).eval unit = target ↔
      hedgeDefectBitOf G unit = w.largeCarrierDefectBit rich target ∧
        hedgePairBitsRealizes G w.large (w.largeCarrierDefectIncidence rich target)
          (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) = true ∧
        hedgeCarrierPrivateCoordinatesFit rich w.large target
          (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) = true := by
    rw [w.largeCarrierDefectParityModel_eval_mem_support_iff rich target unit]
    exact (hedgeCarrierDefectSupportLatents_mem_iff G rich w.large target _ _ unit).trans
      (and_congr_right (fun _ => hedgeCarrierCoordinateSupportLatents_mem_iff G rich w.large target _ _))
  have smallSupport (unit) : (w.smallCarrierDefectParityModel rich).eval unit = target ↔
      hedgeDefectBitOf G unit = w.smallCarrierDefectBit rich target ∧
        hedgeNestedPairBitsRealizes G w.large w.small (w.smallCarrierDefectIncidence rich target)
          (hedgePairBitsOf G (hedgeDefectOldAssignment G unit)) = true ∧
        hedgeCarrierPrivateCoordinatesFit rich w.large target
          (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) = true := by
    rw [w.smallCarrierDefectParityModel_eval_mem_support_iff rich target unit]
    exact (hedgeCarrierDefectSupportLatents_mem_iff G rich w.large target _ _ unit).trans
      (and_congr_right (fun _ => hedgeCarrierCoordinateSupportLatents_mem_iff G rich w.large target _ _))
  have largePullback := FiniteProbRecord.eventMass_congr (w.largeCarrierDefectParityModel rich).prior.atoms _ _
    (target_private_pullback G rich w.large target (w.largeCarrierDefectBit rich target)
      (hedgePairBitsRealizes G w.large (w.largeCarrierDefectIncidence rich target))
      (w.largeCarrierDefectParityModel rich).eval largeSupport privateTest)
  have smallPullback := FiniteProbRecord.eventMass_congr (w.smallCarrierDefectParityModel rich).prior.atoms _ _
    (target_private_pullback G rich w.large target (w.smallCarrierDefectBit rich target)
      (hedgeNestedPairBitsRealizes G w.large w.small (w.smallCarrierDefectIncidence rich target))
      (w.smallCarrierDefectParityModel rich).eval smallSupport privateTest)
  rw [largePullback, smallPullback]
  have largeMass := hedgeDefectPrior_eventMass_stratum_pair_private G
    (w.largeCarrierDefectBit rich target)
    (hedgePairBitsRealizes G w.large (w.largeCarrierDefectIncidence rich target))
    (fun backgrounds => hedgeCarrierPrivateCoordinatesFit rich w.large target backgrounds &&
      privateTest (w.largeCarrierDefectBit rich target) backgrounds)
  have smallMass := hedgeDefectPrior_eventMass_stratum_pair_private G
    (w.smallCarrierDefectBit rich target)
    (hedgeNestedPairBitsRealizes G w.large w.small (w.smallCarrierDefectIncidence rich target))
    (fun backgrounds => hedgeCarrierPrivateCoordinatesFit rich w.large target backgrounds &&
      privateTest (w.smallCarrierDefectBit rich target) backgrounds)
  dsimp only [HedgeWitness.largeCarrierDefectParityModel,
    HedgeWitness.smallCarrierDefectParityModel, hedgeCarrierDefectModel]
  refine largeMass.trans (Eq.trans ?_ smallMass.symm)
  rw [w.carrierDefectPairBitRealizers_length_eq rich target,
    w.largeCarrierDefectBit_eq_small rich target]

/-! ## A constructively enumerated joint state -/

/-- Retained information needed to replay a structural carrier response.
The private block is kept in its original dependent coordinate types. -/
abbrev HedgeCarrierObservedState (S : ObservedSignature) :=
  S.Assignment × (HedgePrivateCoordinates S × Bool)

private def stateEnumeration (S : ObservedSignature) : List (HedgeCarrierObservedState S) :=
  ConstructivePermutation.pairList S.assignmentEnumeration
    (ConstructivePermutation.pairList (hedgePrivateCoordinateEnum S) [false, true])

private theorem stateEnumeration_nodup (S : ObservedSignature) : (stateEnumeration S).Nodup :=
  ConstructivePermutation.pairList_nodup _ _ S.assignmentEnumeration_nodup
    (ConstructivePermutation.pairList_nodup _ _ (hedgePrivateCoordinateEnum_nodup S) (by decide))

private theorem stateEnumeration_complete (S : ObservedSignature) (state : HedgeCarrierObservedState S) :
    state ∈ stateEnumeration S := by
  apply (ConstructivePermutation.mem_pairList _ _ _ _).mpr
  refine ⟨S.assignmentEnumeration_complete state.1,
    (ConstructivePermutation.mem_pairList _ _ _ _).mpr ⟨hedgePrivateCoordinateEnum_complete S state.2.1, ?_⟩⟩
  cases state.2.2 <;> decide

/-- Pair an actual evaluated assignment with its recovered private block
and actual defect bit.  The function does not modify the SCM or its prior. -/
def hedgeCarrierObservedState (G : ObservedGraph S)
    (output : ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) -> S.Assignment)
    (unit : (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) :
    HedgeCarrierObservedState S :=
  (output unit, (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit), hedgeDefectBitOf G unit))

private theorem state_singleton_eq (G : ObservedGraph S)
    (output : ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) -> S.Assignment)
    (target : HedgeCarrierObservedState S)
    (unit : (root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) :
    FiniteProbRecord.singletonEvent target (hedgeCarrierObservedState G output unit) =
      (FiniteProbRecord.singletonEvent target.1 (output unit) &&
        (decide (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit) = target.2.1) &&
          decide (hedgeDefectBitOf G unit = target.2.2))) := by
  rcases target with ⟨sample, backgrounds, defect⟩
  apply Bool.eq_iff_iff.mpr
  simp only [FiniteProbRecord.singletonEvent, hedgeCarrierObservedState,
    decide_eq_true_eq, Prod.mk.injEq, Bool.and_eq_true_iff]

/-- The actual carrier pair has the same full joint observational law of
observed values, private backgrounds, and defect, not merely the same observed
marginal.  Arbitrary events may couple all three blocks.

Finite singleton extensionality uses an explicit duplicate-free product
enumeration.  No coupling of latent units or family of background witnesses
is selected from propositional existence.  This permits a subsequent common
replay to read the concealed backgrounds, but that replay must still prove
its own connection to actual updated SCM evaluation. -/
theorem HedgeWitness.carrierDefectParityModels_observationalState_probVal_equiv
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (event : Event (HedgeCarrierObservedState S)) :
    QProb.Equiv
      ((w.largeCarrierDefectParityModel rich).prior.probVal
        (fun unit => event (hedgeCarrierObservedState G (w.largeCarrierDefectParityModel rich).eval unit)))
      ((w.smallCarrierDefectParityModel rich).prior.probVal
        (fun unit => event (hedgeCarrierObservedState G (w.smallCarrierDefectParityModel rich).eval unit))) := by
  let large := w.largeCarrierDefectParityModel rich
  let small := w.smallCarrierDefectParityModel rich
  let leftMap := hedgeCarrierObservedState G large.eval
  let rightMap := hedgeCarrierObservedState G small.eval
  have singletons (target : HedgeCarrierObservedState S) :
      QProb.Equiv ((large.prior.map leftMap).probVal (FiniteProbRecord.singletonEvent target))
        ((small.prior.map rightMap).probVal (FiniteProbRecord.singletonEvent target)) := by
    have pullback : QProb.Equiv
        (large.prior.probVal (fun unit => FiniteProbRecord.singletonEvent target (leftMap unit)))
        (small.prior.probVal (fun unit => FiniteProbRecord.singletonEvent target (rightMap unit))) := by
      unfold QProb.Equiv FiniteProbRecord.probVal
      have leftEq := FiniteProbRecord.eventMass_congr large.prior.atoms _ _
        (state_singleton_eq G large.eval target)
      have rightEq := FiniteProbRecord.eventMass_congr small.prior.atoms _ _
        (state_singleton_eq G small.eval target)
      rw [leftEq, rightEq]
      rw [w.carrierDefectParityModels_observational_target_private_eventMass_eq rich target.1
        (fun defect backgrounds => decide (backgrounds = target.2.1) && decide (defect = target.2.2))]
      rfl
    exact QProb.equiv_trans (large.prior.map_probVal _ _)
      (QProb.equiv_trans pullback (QProb.equiv_symm (small.prior.map_probVal _ _)))
  have mapped := FiniteProbRecord.probVal_extensional_of_singletons
    (large.prior.map leftMap) (small.prior.map rightMap)
    (stateEnumeration S) (stateEnumeration_nodup S) (stateEnumeration_complete S) singletons event
  exact QProb.equiv_trans (QProb.equiv_symm (large.prior.map_probVal leftMap event))
    (QProb.equiv_trans mapped (small.prior.map_probVal rightMap event))

end Causality
end Thesis
