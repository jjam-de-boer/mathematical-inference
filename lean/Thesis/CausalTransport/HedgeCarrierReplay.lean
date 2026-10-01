import Thesis.CausalTransport.HedgeCarrierObservationalState
import Thesis.CausalTransport.HedgeInterventionalMarginal
import Thesis.Causality.PrivateNoise

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Replaying an internal small-forest carrier update

An internal pivot is read by its kept child, so replacing it cannot be treated
as an observed map changing only that coordinate.  This module instead replays
the complete descendant response from the factual carrier state: old observed
values and retained private backgrounds.  The pair-root incidence and defect
cancel from each unchanged mechanism's parent-response equation.

When the pivot belongs to the small forest, every responding kept child also
belongs to that forest.  Outer-only coordinates remain factual.  Consequently
the large and restricted parent maps have the same *change* in parity, even
though their individual parent parities need not agree.  Both actual SCMs
therefore use the same replay.  Their stronger joint observational state law
then proves equality of the full updated observational laws.

No non-influence or kept-sink premise is imposed on the small-forest pivot.
The background block is essential for full nonbinary labels.  This is a
single actual private readout, not yet an assertion about arbitrary plans or
updates in the outer-only forest, where the common-response argument fails.
-/

/-! ## Parent changes, not absolute parent parities -/

private def parentContribution (rich : ObservedSignature.ValueRich S)
    (kept : ForestChild S) (child : Fin S.count) (parents : S.ParentValues child)
    (parent : Fin S.count) : Bool :=
  if edge : S.directed parent child = true then
    if kept parent = some child then hedgeIsSecond rich parent (parents parent edge) else false
  else false

private theorem parentBits_eq_fold (rich : ObservedSignature.ValueRich S)
    (kept : ForestChild S) (child : Fin S.count) (parents : S.ParentValues child) :
    hedgeForestParentBitsFrom rich kept child parents =
      (List.finRange S.count).foldl
        (fun total parent => Bool.xor total (parentContribution rich kept child parents parent)) false := by
  unfold hedgeForestParentBitsFrom
  apply foldl_congr
  intro total parent
  by_cases edge : S.directed parent child = true
  · by_cases selected : kept parent = some child
    · simp only [parentContribution, dif_pos edge, if_pos selected]
    · simp only [parentContribution, dif_pos edge, if_neg selected, Bool.xor_false]
  · simp only [parentContribution, dif_neg edge, Bool.xor_false]

/-- If every excluded parent keeps its old value, restricting the kept map
does not change its parity *difference*.  Absolute parent parities can differ:
the outside contributions cancel only between the old and new assignments. -/
theorem hedgeForestParentBitsFrom_delta_restrict_eq
    (rich : ObservedSignature.ValueRich S) (nodes : NodeSet S)
    (kept : ForestChild S) (child : Fin S.count)
    (old new : S.ParentValues child)
    (unchanged : forall parent edge, nodes parent = false -> old parent edge = new parent edge) :
    Bool.xor (hedgeForestParentBitsFrom rich kept child old)
        (hedgeForestParentBitsFrom rich kept child new) =
      Bool.xor (hedgeForestParentBitsFrom rich (restrictChild nodes kept) child old)
        (hedgeForestParentBitsFrom rich (restrictChild nodes kept) child new) := by
  simp only [parentBits_eq_fold]
  rw [← foldl_xor_pointwise, ← foldl_xor_pointwise]
  apply foldl_congr
  intro total parent
  cases selected : nodes parent with
  | true => simp only [parentContribution, restrictChild, selected, if_true]
  | false =>
      by_cases edge : S.directed parent child = true
      · simp only [parentContribution, dif_pos edge, restrictChild, selected,
          Bool.false_eq_true, if_false, reduceCtorEq]
        rw [unchanged parent edge selected]
        by_cases keptAt : kept parent = some child
        · simp only [if_pos keptAt, Bool.xor_self, Bool.xor_false]
        · simp only [if_neg keptAt, Bool.xor_self, Bool.xor_false]
      · simp only [parentContribution, dif_neg edge, Bool.xor_self]

/-! ## A complete structural response from retained state -/

/-- Set one pivot to a supplied full value and replay every later carrier
equation.  The old factual bit supplies the exogenous residual; the new
parent parity supplies its causal change.  No latent pair bits are read. -/
def HedgeWitness.carrierReplayNode {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (sample : S.Assignment) (backgrounds : HedgePrivateCoordinates S)
    (pivot : Fin S.count) (value : S.Value pivot) (child : Fin S.count) : S.Value child :=
  if child = pivot then S.replace sample pivot value child
  else if w.large child then hedgeParityCarrierValue rich child
    (Bool.xor
      (Bool.xor (hedgeIsSecond rich child (sample child))
        (hedgeForestParentBitsFrom rich w.child child (fun parent _edge => sample parent)))
      (hedgeForestParentBitsFrom rich w.child child (fun parent _edge =>
        w.carrierReplayNode rich sample backgrounds pivot value parent)))
    (hedgePrivateDecode S child (backgrounds child))
  else sample child
termination_by child.val
decreasing_by exact S.directed_earlier _edge

private theorem replay_unchanged_of_not_small {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (sample : S.Assignment) (backgrounds : HedgePrivateCoordinates S)
    (fits : hedgeCarrierPrivateCoordinatesFit rich w.large sample backgrounds = true)
    (pivot : Fin S.count) (inSmall : w.small pivot = true) (value : S.Value pivot)
    (child : Fin S.count) (outside : w.small child = false) :
    w.carrierReplayNode rich sample backgrounds pivot value child = sample child := by
  have different : child ≠ pivot := by
    intro same
    subst child
    rw [inSmall] at outside
    cases outside
  rw [HedgeWitness.carrierReplayNode, if_neg different]
  cases inside : w.large child with
  | false => simp only [Bool.false_eq_true, if_false]
  | true =>
      simp only [if_true]
      have parents : hedgeForestParentBitsFrom rich w.child child
          (fun parent _edge => w.carrierReplayNode rich sample backgrounds pivot value parent) =
          hedgeForestParentBitsFrom rich w.child child (fun parent _edge => sample parent) := by
        apply hedgeForestParentBitsFrom_congr_of_kept
        intro parent edge keptAt
        have notSmall : w.small parent = false := by
          cases selected : w.small parent with
          | false => rfl
          | true =>
              have restricted : restrictChild w.small w.child parent = some child := by
                simpa only [restrictChild, selected, if_true] using keptAt
              have childInside := (w.small_forest.child_edge parent child restricted).2.1
              rw [outside] at childInside
              cases childInside
        exact congrArg (hedgeIsSecond rich parent)
          (replay_unchanged_of_not_small w rich sample backgrounds fits pivot inSmall value parent notSmall)
      rw [parents]
      have cancel (bit parentBit : Bool) : Bool.xor (Bool.xor bit parentBit) parentBit = bit := by
        cases bit <;> cases parentBit <;> rfl
      rw [cancel]
      exact hedgeCarrierPrivateCoordinatesFit_inside rich w.large sample backgrounds fits child inside
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-! ## The replay is actual evaluation, including responding children -/

private def readoutValue (sample : S.Assignment) (pivot : Fin S.count)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot) (bit : Bool) : S.Value pivot :=
  readout (fun parent _edge => sample parent) (sample pivot) bit

private theorem large_readout_eval_replay {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment) (bit : Bool)
    (child : Fin S.count) :
    ((w.largeCarrierDefectParityModel rich).withPrivateReadout pivot noise readout).evalNodeUnder
        (FiniteLatentSCM.noIntervention S)
        (PrivateBooleanNoise.assignment (w.largeCarrierDefectParityModel rich).latent bit unit) child =
      w.carrierReplayNode rich ((w.largeCarrierDefectParityModel rich).eval unit)
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) pivot
        (readoutValue ((w.largeCarrierDefectParityModel rich).eval unit) pivot readout bit) child := by
  by_cases same : child = pivot
  · subst child
    rw [FiniteLatentSCM.withPrivateReadout_evalNodeUnder_pivot _ pivot noise readout _ rfl unit bit]
    rw [HedgeWitness.carrierReplayNode, if_pos rfl, S.replace_at]
    rfl
  · rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder
    simp only [FiniteLatentSCM.noIntervention]
    dsimp only [FiniteLatentSCM.withPrivateReadout]
    rw [FiniteLatentSCM.withPrivateBooleanNoise_mechanism_of_ne _ pivot noise _ child same]
    have oldInputs := PrivateBooleanNoise.oldInputs_assignment
      (w.largeCarrierDefectParityModel rich).latent pivot child bit unit
    refine (congrArg ((w.largeCarrierDefectParityModel rich).mechanism child _) oldInputs).trans ?_
    rw [w.largeCarrierDefectParityModel_mechanism_parent_response rich unit child]
    rw [HedgeWitness.carrierReplayNode, if_neg same]
    cases inside : w.large child with
    | false => simp only [Bool.false_eq_true, if_false]
    | true =>
        simp only [if_true]
        congr 1
        congr 1
        apply hedgeForestParentBitsFrom_congr_of_kept
        intro parent edge _kept
        exact congrArg (hedgeIsSecond rich parent)
          (large_readout_eval_replay w rich pivot noise readout unit bit parent)
termination_by child.val
decreasing_by exact S.directed_earlier edge

private theorem small_readout_eval_replay {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (inSmall : w.small pivot = true) (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (unit : (w.smallCarrierDefectParityModel rich).latent.Assignment) (bit : Bool)
    (child : Fin S.count) :
    ((w.smallCarrierDefectParityModel rich).withPrivateReadout pivot noise readout).evalNodeUnder
        (FiniteLatentSCM.noIntervention S)
        (PrivateBooleanNoise.assignment (w.smallCarrierDefectParityModel rich).latent bit unit) child =
      w.carrierReplayNode rich ((w.smallCarrierDefectParityModel rich).eval unit)
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) pivot
        (readoutValue ((w.smallCarrierDefectParityModel rich).eval unit) pivot readout bit) child := by
  by_cases same : child = pivot
  · subst child
    rw [FiniteLatentSCM.withPrivateReadout_evalNodeUnder_pivot _ pivot noise readout _ rfl unit bit]
    rw [HedgeWitness.carrierReplayNode, if_pos rfl, S.replace_at]
    rfl
  · rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder
    simp only [FiniteLatentSCM.noIntervention]
    dsimp only [FiniteLatentSCM.withPrivateReadout]
    rw [FiniteLatentSCM.withPrivateBooleanNoise_mechanism_of_ne _ pivot noise _ child same]
    have oldInputs := PrivateBooleanNoise.oldInputs_assignment
      (w.smallCarrierDefectParityModel rich).latent pivot child bit unit
    refine (congrArg ((w.smallCarrierDefectParityModel rich).mechanism child _) oldInputs).trans ?_
    rw [w.smallCarrierDefectParityModel_mechanism_parent_response rich unit child]
    rw [HedgeWitness.carrierReplayNode, if_neg same]
    cases inside : w.large child with
    | false => simp only [Bool.false_eq_true, if_false]
    | true =>
        simp only [if_true]
        have parentsEqual :
            (fun parent (_edge : S.directed parent child = true) =>
              ((w.smallCarrierDefectParityModel rich).withPrivateReadout pivot noise readout).evalNodeUnder
                (FiniteLatentSCM.noIntervention S)
                (PrivateBooleanNoise.assignment (w.smallCarrierDefectParityModel rich).latent bit unit) parent) =
            (fun parent (_edge : S.directed parent child = true) =>
              w.carrierReplayNode rich ((w.smallCarrierDefectParityModel rich).eval unit)
                (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) pivot
                (readoutValue ((w.smallCarrierDefectParityModel rich).eval unit) pivot readout bit) parent) := by
          funext parent edge
          exact small_readout_eval_replay w rich pivot inSmall noise readout unit bit parent
        dsimp only [FiniteLatentSCM.withPrivateReadout] at parentsEqual
        rw [parentsEqual]
        cases selected : w.small child with
        | false => simp only [Bool.false_eq_true, if_false]
        | true =>
            simp only [if_true]
            congr 1
            rw [Bool.xor_assoc, Bool.xor_assoc]
            congr 1
            apply (hedgeForestParentBitsFrom_delta_restrict_eq rich w.small w.child child _ _ ?_).symm
            intro parent edge outside
            exact (replay_unchanged_of_not_small w rich _ _
              (w.smallCarrierPrivateCoordinatesFit_eval rich unit) pivot inSmall _ parent outside).symm
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-! ## Full observational equality of an actual internal readout -/

/-- Full-assignment presentation of the topological carrier replay. -/
def HedgeWitness.carrierReplay {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (sample : S.Assignment) (backgrounds : HedgePrivateCoordinates S)
    (pivot : Fin S.count) (value : S.Value pivot) : S.Assignment :=
  fun child => w.carrierReplayNode rich sample backgrounds pivot value child

/-- Actual large-model evaluation is the complete retained-state replay,
at every coordinate, including later responding descendants.  The new pivot
value is the common readout of its unchanged factual parent inputs. -/
theorem HedgeWitness.largeCarrierDefectParityModel_withPrivateReadout_eval_eq_replay
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment) (bit : Bool) :
    ((w.largeCarrierDefectParityModel rich).withPrivateReadout pivot noise readout).eval
        (PrivateBooleanNoise.assignment (w.largeCarrierDefectParityModel rich).latent bit unit) =
      w.carrierReplay rich ((w.largeCarrierDefectParityModel rich).eval unit)
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) pivot
        (readout (fun parent _edge => (w.largeCarrierDefectParityModel rich).eval unit parent)
          ((w.largeCarrierDefectParityModel rich).eval unit pivot) bit) :=
  funext (large_readout_eval_replay w rich pivot noise readout unit bit)

/-- The actual nested model uses the very same full replay when the pivot
is in the small forest.  The equality concerns full values, not only their
distinguished parity bits or a prefix ending at the pivot. -/
theorem HedgeWitness.smallCarrierDefectParityModel_withPrivateReadout_eval_eq_replay
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (inSmall : w.small pivot = true) (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot)
    (unit : (w.smallCarrierDefectParityModel rich).latent.Assignment) (bit : Bool) :
    ((w.smallCarrierDefectParityModel rich).withPrivateReadout pivot noise readout).eval
        (PrivateBooleanNoise.assignment (w.smallCarrierDefectParityModel rich).latent bit unit) =
      w.carrierReplay rich ((w.smallCarrierDefectParityModel rich).eval unit)
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G unit)) pivot
        (readout (fun parent _edge => (w.smallCarrierDefectParityModel rich).eval unit parent)
          ((w.smallCarrierDefectParityModel rich).eval unit pivot) bit) :=
  funext (small_readout_eval_replay w rich pivot inSmall noise readout unit bit)

/-- A common private readout at *any* small-forest vertex preserves the full
carrier pair's observational equality, including responding kept descendants
and every observed background label.

The pivot need not be a kept sink, and no other-mechanisms-ignore premise is
supplied.  Both evaluated models are proved to equal the same retained-state
replay for each actual independent noise input.  The stronger joint state law
then matches every noise slice, and the genuine product prior integrates the
common noise factor.  Neither strict positivity nor noise bias is needed for
this equality theorem; those remain separate requirements for a countermodel.

The small-membership hypothesis is substantive.  At an outer-only pivot the
large and restricted forest responses can differ, so this theorem must not
be used to justify arbitrary action overwrites or unrestricted finite plans. -/
theorem HedgeWitness.carrierDefectParityModels_withPrivateReadout_observationally_equivalent_of_small
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (pivot : Fin S.count) (inSmall : w.small pivot = true)
    (noise : FiniteProbRecord Bool)
    (readout : S.ParentValues pivot -> S.Value pivot -> Bool -> S.Value pivot) :
    ObservationallyEquivalent
      ((w.largeCarrierDefectParityModel rich).withPrivateReadout pivot noise readout)
      ((w.smallCarrierDefectParityModel rich).withPrivateReadout pivot noise readout) := by
  intro event
  let large := w.largeCarrierDefectParityModel rich
  let small := w.smallCarrierDefectParityModel rich
  let left := large.withPrivateReadout pivot noise readout
  let right := small.withPrivateReadout pivot noise readout
  let stateEvent := fun (bit : Bool) (state : HedgeCarrierObservedState S) =>
    event (w.carrierReplay rich state.1 state.2.1 pivot (readoutValue state.1 pivot readout bit))
  let leftEvent : Event (Bool × large.latent.Assignment) := fun pair =>
    stateEvent pair.1 (hedgeCarrierObservedState G large.eval pair.2)
  let rightEvent : Event (Bool × small.latent.Assignment) := fun pair =>
    stateEvent pair.1 (hedgeCarrierObservedState G small.eval pair.2)
  have leftEvaluation (pair : Bool × large.latent.Assignment) :
      event (left.eval (PrivateBooleanNoise.assignment large.latent pair.1 pair.2)) = leftEvent pair :=
    congrArg event (funext (large_readout_eval_replay w rich pivot noise readout pair.2 pair.1))
  have rightEvaluation (pair : Bool × small.latent.Assignment) :
      event (right.eval (PrivateBooleanNoise.assignment small.latent pair.1 pair.2)) = rightEvent pair :=
    congrArg event (funext (small_readout_eval_replay w rich pivot inSmall noise readout pair.2 pair.1))
  have leftPushed := (noise.product large.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment large.latent pair.1 pair.2)
    (fun unit => event (left.eval unit))
  have rightPushed := (noise.product small.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment small.latent pair.1 pair.2)
    (fun unit => event (right.eval unit))
  have leftReplay := (noise.product large.prior).probVal_congr _ leftEvent leftEvaluation
  have rightReplay := (noise.product small.prior).probVal_congr _ rightEvent rightEvaluation
  have slices := noise.product_probVal_equiv_of_slices large.prior small.prior leftEvent rightEvent
    (fun bit => w.carrierDefectParityModels_observationalState_probVal_equiv rich (stateEvent bit))
  exact QProb.equiv_trans (left.observationalValue_eq event)
    (QProb.equiv_trans leftPushed
      (QProb.equiv_trans leftReplay
        (QProb.equiv_trans slices
          (QProb.equiv_trans (QProb.equiv_symm rightReplay)
            (QProb.equiv_trans (QProb.equiv_symm rightPushed)
              (QProb.equiv_symm (right.observationalValue_eq event)))))))

end Causality
end Thesis
