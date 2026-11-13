import Thesis.Causality.SharedNoise

namespace Thesis
namespace Causality

open Probability

/-!
# The actual semantics of a two-coordinate shared readout

An independent pair source is useful for conditional countermodels only if
its mechanism changes can be related to the whole original observed law.
Here the two selected coordinates undergo one displayed observable update,
with the same shared bit at both coordinates.  Non-influence of both base
pivots ensures that no unmodified mechanism sees a changed parent value.

The evaluation theorem applies to arbitrary interventions.  Its observable
map keeps forced coordinates fixed and leaves every off-pair coordinate
unchanged.  Observational equality then follows by finite integration over
the actual `noise × old prior`, separately for the two base models.  Their
latent spaces and prior denominators may differ.

This layer does not assert positivity for arbitrary shared readouts: one
shared bit need not simultaneously restore two requested labels.  In
particular, sequential XOR carriers can erase a nonbinary background label.
A collider construction must combine the old value, shared mask, and its
private noise before emitting that value, and prove its own full support.
-/

variable {S : ObservedSignature.{0}}

private theorem mechanism_eq_of_ignored (base : ExactModel S) (pivot child : Fin S.count)
    (ignored : base.OtherMechanismsIgnore pivot)
    (first second : S.ParentValues child) (inputs : base.latent.Inputs child)
    (agree : forall parent (edge : S.directed parent child = true), parent ≠ pivot ->
      first parent edge = second parent edge) :
    base.mechanism child first inputs = base.mechanism child second inputs := by
  by_cases own : child = pivot
  · subst child
    have parentsEqual : first = second := by
      funext parent edge
      apply agree parent edge
      intro same
      have earlier := S.directed_earlier edge
      rw [same] at earlier
      exact Nat.lt_irrefl _ earlier
    rw [parentsEqual]
  · exact ignored child own first second inputs agree

/-- Parent inputs may differ at both ignored coordinates at once.  The
intermediate typed input changes one coordinate at a time; the self-parent
boundary is discharged by the signature's strict topological order. -/
private theorem mechanism_eq_of_two_ignored (base : ExactModel S) (first second child : Fin S.count)
    (firstIgnored : base.OtherMechanismsIgnore first) (secondIgnored : base.OtherMechanismsIgnore second)
    (left right : S.ParentValues child) (inputs : base.latent.Inputs child)
    (agree : forall parent (edge : S.directed parent child = true), parent ≠ first -> parent ≠ second ->
      left parent edge = right parent edge) :
    base.mechanism child left inputs = base.mechanism child right inputs := by
  let middle : S.ParentValues child := fun parent edge => if parent = first then right parent edge else left parent edge
  have initial := mechanism_eq_of_ignored base first child firstIgnored left middle inputs (fun parent edge away => by
    simp only [middle, away, if_false])
  have final := mechanism_eq_of_ignored base second child secondIgnored middle right inputs (fun parent edge away => by
    by_cases atFirst : parent = first
    · simp only [middle, atFirst, if_true]
    · simp only [middle, atFirst, if_false]
      exact agree parent edge atFirst away)
  exact initial.trans final

/-- One mechanism on the explicitly encoded independent pair.  The fresh
bit is read through the new incident input, not supplied as an extra semantic
assumption about the SCM's evaluation. -/
theorem FiniteLatentSCM.withSharedReadout_mechanism_assignment
    (base : ExactModel S) (first second : Fin S.count) (noise : FiniteProbRecord Bool)
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node)
    (child : Fin S.count) (parents : S.ParentValues child) (value : Bool) (old : base.latent.Assignment) :
    (base.withSharedReadout first second noise readout).mechanism child parents
      (fun root _selected => PrivateBooleanNoise.assignment base.latent value old root) =
      if SharedBooleanNoise.membership first second child = true then
        readout child (base.mechanism child parents (fun root _selected => old root)) value
      else base.mechanism child parents (fun root _selected => old root) := by
  simp only [FiniteLatentSCM.withSharedReadout, SharedBooleanNoise.oldInputs_assignment,
    SharedBooleanNoise.bit_assignment]
  by_cases selected : SharedBooleanNoise.membership first second child = true
  · simp only [dif_pos selected, if_pos selected]
  · simp only [dif_neg selected, if_neg selected]

/-- The common whole-assignment update, including arbitrary forced values.
An off-pair coordinate is literally the old sample coordinate. -/
def ObservedSignature.sharedReadoutAssignment (first second : Fin S.count)
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (sample : S.Assignment) (value : Bool) : S.Assignment :=
  fun node => if SharedBooleanNoise.membership first second node = true then
    match intervention node with
    | some fixed => fixed
    | none => readout node (sample node) value
  else sample node

/-- Both ignored pivots can be updated simultaneously without changing any
off-pair mechanism response.  The proof follows the actual observed order;
the two coordinates need not be adjacent, ordered as displayed, or distinct. -/
theorem FiniteLatentSCM.withSharedReadout_evalNodeUnder
    (base : ExactModel S) (first second : Fin S.count) (noise : FiniteProbRecord Bool)
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node)
    (firstIgnored : base.OtherMechanismsIgnore first) (secondIgnored : base.OtherMechanismsIgnore second)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (value : Bool) (child : Fin S.count) :
    (base.withSharedReadout first second noise readout).evalNodeUnder intervention
      (PrivateBooleanNoise.assignment base.latent value old) child =
      S.sharedReadoutAssignment first second readout intervention (base.evalUnder intervention old) value child := by
  let modified := base.withSharedReadout first second noise readout
  have parentAgreement : forall parent (edge : S.directed parent child = true), parent ≠ first -> parent ≠ second ->
      modified.evalNodeUnder intervention (PrivateBooleanNoise.assignment base.latent value old) parent =
        base.evalNodeUnder intervention old parent := by
    intro parent edge firstAway secondAway
    have off : SharedBooleanNoise.membership first second parent = false := by
      simp only [SharedBooleanNoise.membership, firstAway, secondAway, decide_false, Bool.false_or]
    rw [base.withSharedReadout_evalNodeUnder first second noise readout firstIgnored secondIgnored
      intervention old value parent]
    simp only [ObservedSignature.sharedReadoutAssignment, off, Bool.false_eq_true, if_false, FiniteLatentSCM.evalUnder]
  have mechanismEqual := mechanism_eq_of_two_ignored base first second child firstIgnored secondIgnored
    (fun parent _edge => modified.evalNodeUnder intervention (PrivateBooleanNoise.assignment base.latent value old) parent)
    (fun parent _edge => base.evalNodeUnder intervention old parent) (fun root _selected => old root) parentAgreement
  unfold ObservedSignature.sharedReadoutAssignment
  cases selected : SharedBooleanNoise.membership first second child with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      change modified.evalNodeUnder intervention (PrivateBooleanNoise.assignment base.latent value old) child =
        base.evalNodeUnder intervention old child
      rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder
      cases forced : intervention child with
      | some fixed => rfl
      | none =>
          rw [base.withSharedReadout_mechanism_assignment first second noise readout]
          simp only [selected, Bool.false_eq_true, if_false]
          exact mechanismEqual
  | true =>
      simp only [if_true]
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder
      cases forced : intervention child with
      | some fixed => rfl
      | none =>
          rw [base.withSharedReadout_mechanism_assignment first second noise readout]
          simp only [selected, if_true]
          rw [mechanismEqual, FiniteLatentSCM.evalUnder, FiniteLatentSCM.evalNodeUnder]
          unfold FiniteLatentSCM.equationUnder
          rw [forced]
termination_by child.val
decreasing_by exact S.directed_earlier edge

theorem FiniteLatentSCM.withSharedReadout_evalUnder
    (base : ExactModel S) (first second : Fin S.count) (noise : FiniteProbRecord Bool)
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node)
    (firstIgnored : base.OtherMechanismsIgnore first) (secondIgnored : base.OtherMechanismsIgnore second)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (value : Bool) :
    (base.withSharedReadout first second noise readout).evalUnder intervention
      (PrivateBooleanNoise.assignment base.latent value old) =
      S.sharedReadoutAssignment first second readout intervention (base.evalUnder intervention old) value := by
  funext child
  exact base.withSharedReadout_evalNodeUnder first second noise readout firstIgnored secondIgnored
    intervention old value child

/-- A shared readout of an old output does not introduce dependence on an
observed coordinate that the old mechanism ignored.  The new bit is an
incident latent input, not an additional observed parent. -/
theorem FiniteLatentSCM.withSharedReadout_otherMechanismsIgnore
    (base : ExactModel S) (first second pivot : Fin S.count) (noise : FiniteProbRecord Bool)
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node)
    (ignored : base.OtherMechanismsIgnore pivot) :
    (base.withSharedReadout first second noise readout).OtherMechanismsIgnore pivot := by
  intro child different left right inputs agree
  simp only [FiniteLatentSCM.withSharedReadout]
  rw [ignored child different left right (SharedBooleanNoise.oldInputs base.latent first second child inputs) agree]

/-! ## Full observational equality via the same observable update -/

theorem FiniteLatentSCM.withSharedReadout_observationalValue_equiv
    (base : ExactModel S) (first second : Fin S.count) (noise : FiniteProbRecord Bool)
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node)
    (firstIgnored : base.OtherMechanismsIgnore first) (secondIgnored : base.OtherMechanismsIgnore second)
    (event : Event S.Assignment) :
    QProb.Equiv ((base.withSharedReadout first second noise readout).observationalValue event)
      ((noise.product base.observationalDist).probVal (fun pair => event
        (S.sharedReadoutAssignment first second readout (FiniteLatentSCM.noIntervention S) pair.2 pair.1))) := by
  let modified := base.withSharedReadout first second noise readout
  have evaluation (pair : Bool × base.latent.Assignment) :
      modified.eval (PrivateBooleanNoise.assignment base.latent pair.1 pair.2) =
        S.sharedReadoutAssignment first second readout (FiniteLatentSCM.noIntervention S) (base.eval pair.2) pair.1 :=
    base.withSharedReadout_evalUnder first second noise readout firstIgnored secondIgnored
      (FiniteLatentSCM.noIntervention S) pair.2 pair.1
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun latent => event (modified.eval latent))
  have observed := (noise.product base.prior).probVal_congr _ _ (fun pair => congrArg event (evaluation pair))
  have originals := noise.product_map_right_probVal base.prior base.eval (fun pair => event
    (S.sharedReadoutAssignment first second readout (FiniteLatentSCM.noIntervention S) pair.2 pair.1))
  exact QProb.equiv_trans (modified.observationalValue_eq event)
    (QProb.equiv_trans pushed (QProb.equiv_trans observed (QProb.equiv_symm originals)))

/-- The same shared-bit transformation preserves the entire observed law
of an observationally equal pair.  Equality is applied on each finite noise
slice; no common latent carrier, coupling, or equal denominator is assumed. -/
theorem FiniteLatentSCM.withSharedReadout_observationally_equivalent
    (left right : ExactModel S) (observational : ObservationallyEquivalent left right)
    (first second : Fin S.count) (noise : FiniteProbRecord Bool)
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node)
    (leftFirstIgnored : left.OtherMechanismsIgnore first) (rightFirstIgnored : right.OtherMechanismsIgnore first)
    (leftSecondIgnored : left.OtherMechanismsIgnore second) (rightSecondIgnored : right.OtherMechanismsIgnore second) :
    ObservationallyEquivalent (left.withSharedReadout first second noise readout)
      (right.withSharedReadout first second noise readout) := by
  intro event
  exact QProb.equiv_trans
    (left.withSharedReadout_observationalValue_equiv first second noise readout leftFirstIgnored leftSecondIgnored event)
    (QProb.equiv_trans
      (noise.product_probVal_equiv_of_slices left.observationalDist right.observationalDist
        (fun pair => event (S.sharedReadoutAssignment first second readout (FiniteLatentSCM.noIntervention S) pair.2 pair.1))
        (fun pair => event (S.sharedReadoutAssignment first second readout (FiniteLatentSCM.noIntervention S) pair.2 pair.1))
        (fun bit => observational (fun sample => event
          (S.sharedReadoutAssignment first second readout (FiniteLatentSCM.noIntervention S) sample bit))))
      (QProb.equiv_symm
        (right.withSharedReadout_observationalValue_equiv first second noise readout rightFirstIgnored rightSecondIgnored event)))

/-! ## Positivity when an explicit common bit restores both coordinates -/

/-- Full support of the shared readout needs a restoring bit for both
coordinates simultaneously.  This hypothesis is supplied as explicit data,
not extracted from a statement that some noise outcome must work.  A later
collider uses this theorem for its parent-mask step, whose other readout is
the identity; its latent-dependent child update has a separate support proof. -/
theorem FiniteLatentSCM.withSharedReadout_positive
    (base : ExactModel S) (positive : ObservationallyPositive base) (first second : Fin S.count)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (readout : (node : Fin S.count) -> S.Value node -> Bool -> S.Value node)
    (firstIgnored : base.OtherMechanismsIgnore first) (secondIgnored : base.OtherMechanismsIgnore second)
    (restoreBit : S.Assignment -> Bool)
    (restore : forall target node, SharedBooleanNoise.membership first second node = true ->
      readout node (target node) (restoreBit target) = target node) :
    ObservationallyPositive (base.withSharedReadout first second noise readout) := by
  intro target
  let modified := base.withSharedReadout first second noise readout
  let oldEvent := fun old : base.latent.Assignment => FiniteProbRecord.singletonEvent target (base.eval old)
  let rectangle := fun pair : Bool × base.latent.Assignment =>
    FiniteProbRecord.singletonEvent (restoreBit target) pair.1 && oldEvent pair.2
  let event := fun pair : Bool × base.latent.Assignment =>
    FiniteProbRecord.singletonEvent target (modified.eval (PrivateBooleanNoise.assignment base.latent pair.1 pair.2))
  have oldPositive : 0 < FiniteProbRecord.eventMass base.prior.atoms oldEvent := by
    simpa only [FiniteLatentSCM.observationalDist, FiniteProbRecord.map, FiniteProbRecord.probVal,
      FiniteProbRecord.eventMass_map_labels, oldEvent] using positive target
  have rectanglePositive : 0 < FiniteProbRecord.eventMass (noise.product base.prior).atoms rectangle := by
    rw [FiniteProbRecord.product, FiniteProbRecord.eventMass_weightedCartesian]
    exact Nat.mul_pos (noisePositive (restoreBit target)) oldPositive
  have included : forall pair, rectangle pair = true -> event pair = true := by
    intro pair selected
    have parts := Bool.and_eq_true_iff.mp selected
    have sameBit : pair.1 = restoreBit target := of_decide_eq_true parts.1
    have oldTarget : base.eval pair.2 = target := of_decide_eq_true parts.2
    have restored : modified.eval (PrivateBooleanNoise.assignment base.latent pair.1 pair.2) = target := by
      unfold FiniteLatentSCM.eval at oldTarget ⊢
      rw [base.withSharedReadout_evalUnder first second noise readout firstIgnored secondIgnored,
        oldTarget, sameBit]
      funext node
      cases member : SharedBooleanNoise.membership first second node with
      | false => simp only [ObservedSignature.sharedReadoutAssignment, member, Bool.false_eq_true, if_false]
      | true =>
          simp only [ObservedSignature.sharedReadoutAssignment, member, if_true, FiniteLatentSCM.noIntervention]
          exact restore target node member
    exact decide_eq_true restored
  have bound := FiniteProbRecord.eventMass_mono (noise.product base.prior).atoms rectangle event included
  have pushedPositive := Nat.lt_of_lt_of_le rectanglePositive bound
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun latent => FiniteProbRecord.singletonEvent target (modified.eval latent))
  exact (QProb.equiv_num_pos_iff (QProb.equiv_trans
    (modified.observationalValue_eq (FiniteProbRecord.singletonEvent target)) pushed)).mpr pushedPositive

end Causality
end Thesis
