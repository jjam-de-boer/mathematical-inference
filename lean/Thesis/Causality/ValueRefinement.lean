import Thesis.Causality.PrivateNoise

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Private refinements of binary observed labels

A binary countermodel need not use a larger observed alphabet internally.
It does, however, have to give positive mass to every supplied label before
it belongs to `GraphModelClass.positive`.  Simply replacing observed values
by two distinguished labels does not satisfy that requirement.

The construction here separates these obligations.  A mechanism may depend
on the bits of its declared parents while retaining arbitrary labels at its
own output.  Independent private readouts then refine bit-zero labels,
without changing any bit or any descendant response.  The bit-one class is
the single distinguished `second` label.  Every other supplied label belongs
to the bit-zero class, including `first`.

These are actual SCM updates with the product priors from `PrivateNoise`.
No common switch is shared between observed nodes, and no extra projected
bidirected edge is introduced.  Observational equality is proved for the
whole refined assignment, whereas interventional preservation concerns
bit-dependent events.  The construction does not manufacture a binary hedge
countermodel: that remains the substantive general completeness obligation.
-/

namespace ObservedValueRefinement

/-- The two-valued information retained by a label refinement.  This uses
the supplied decidable equality, not a decision of an arbitrary proposition. -/
def bit (rich : ObservedSignature.ValueRich S) (node : Fin S.count)
    (value : S.Value node) : Bool :=
  decide (value = rich.second node)

/-- Decode all observed coordinates without identifying their value types. -/
def bits (rich : ObservedSignature.ValueRich S) (sample : S.Assignment) :
    Fin S.count -> Bool :=
  fun node => bit rich node (sample node)

instance bitsDecidableEq : DecidableEq (Fin S.count -> Bool) :=
  FiniteProduct.assignmentDecidableEq S.count (fun _ => Bool) (fun _ => inferInstance)

/-- Exact parent-label irrelevance, at fixed incident latent inputs.
Equality is required only of the declared parents' bits.  In particular,
this is stronger than an equality restricted to factual observations. -/
def RespectsParentBits (base : ExactModel S)
    (rich : ObservedSignature.ValueRich S) : Prop :=
  forall child (first second : S.ParentValues child) (inputs : base.latent.Inputs child),
    (forall parent (edge : S.directed parent child = true),
      bit rich parent (first parent edge) = bit rich parent (second parent edge)) ->
    base.mechanism child first inputs = base.mechanism child second inputs

/-- One candidate bit-zero label.  Its proof field prevents a refinement
from silently changing a binary signal. -/
structure Step (rich : ObservedSignature.ValueRich S) where
  pivot : Fin S.count
  label : S.Value pivot
  label_bit : bit rich pivot label = false

namespace Step

variable {rich : ObservedSignature.ValueRich S}

/-- A supported private coin.  Bias is immaterial here: the readout preserves
the old bit exactly, rather than passing it through an XOR channel. -/
def noise : FiniteProbRecord Bool :=
  ⟨[(false, 1), (true, 1)], 2, by decide, rfl⟩

theorem noise_positive (value : Bool) :
    noise.EventPositive (FiniteProbRecord.singletonEvent value) := by
  cases value <;> decide +kernel

/-- Replace a bit-zero output by the candidate label when the fresh input
is true.  The false input is the identity on every label, and a bit-one
output is always kept.  Declared parent values are not inspected here. -/
def readout (step : Step rich) (_parents : S.ParentValues step.pivot)
    (old : S.Value step.pivot) (fresh : Bool) : S.Value step.pivot :=
  if bit rich step.pivot old then old else if fresh then step.label else old

theorem readout_bit (step : Step rich) (parents : S.ParentValues step.pivot)
    (old : S.Value step.pivot) (fresh : Bool) :
    bit rich step.pivot (step.readout parents old fresh) = bit rich step.pivot old := by
  cases oldBit : bit rich step.pivot old <;> cases fresh <;>
    simp only [readout, oldBit, Bool.false_eq_true, if_false, if_true, step.label_bit]

/-- Install the readout at its actual mechanism with one new private root. -/
def apply (step : Step rich) (base : ExactModel S) : ExactModel S :=
  base.withPrivateReadout step.pivot noise step.readout

/-- The complete observed map for a supplied private input.  An intervention
at the pivot takes precedence over the installed mechanism. -/
def assignment (step : Step rich)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (sample : S.Assignment) (fresh : Bool) : S.Assignment :=
  if (intervention step.pivot).isSome then sample
  else S.privateReadoutAssignment step.pivot step.readout sample fresh

theorem assignment_of_ne (step : Step rich)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (sample : S.Assignment) (fresh : Bool) (node : Fin S.count)
    (different : node ≠ step.pivot) :
    step.assignment intervention sample fresh node = sample node := by
  cases selected : intervention step.pivot <;>
    simp only [assignment, selected, Option.isSome, Bool.false_eq_true, if_false, if_true,
      ObservedSignature.privateReadoutAssignment, ObservedSignature.replace, dif_neg different]

theorem assignment_bits (step : Step rich)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (sample : S.Assignment) (fresh : Bool) :
    bits rich (step.assignment intervention sample fresh) = bits rich sample := by
  funext node
  by_cases same : node = step.pivot
  · subst node
    cases selected : intervention step.pivot <;>
      simp only [bits, assignment, selected, Option.isSome, Bool.false_eq_true, if_false,
        if_true, ObservedSignature.privateReadoutAssignment, ObservedSignature.replace,
        dite_true, readout_bit]
  · exact congrArg (bit rich node) (step.assignment_of_ne intervention sample fresh node same)

/-- Refining labels does not give a mechanism access to any new shared
source, and retains the original graph exactly. -/
theorem compatible (step : Step rich) (base : ExactModel S)
    {graph : ObservedGraph S} (member : Compatible base graph) :
    Compatible (step.apply base) graph :=
  base.withPrivateBooleanNoise_compatible member step.pivot noise _

/-- Every updated mechanism still inspects only parent bits.  At the pivot,
the old mechanism's complete value is first matched; the same local readout
is then applied to that value and the same supplied private bit. -/
theorem respectsParentBits (step : Step rich) (base : ExactModel S)
    (respects : RespectsParentBits base rich) : RespectsParentBits (step.apply base) rich := by
  intro child first second inputs agree
  change (base.withPrivateBooleanNoise step.pivot noise _).mechanism child first inputs =
    (base.withPrivateBooleanNoise step.pivot noise _).mechanism child second inputs
  by_cases same : child = step.pivot
  · subst child
    rw [FiniteLatentSCM.withPrivateBooleanNoise_mechanism_pivot,
      FiniteLatentSCM.withPrivateBooleanNoise_mechanism_pivot]
    have old := respects step.pivot first second
      (PrivateBooleanNoise.oldInputs base.latent step.pivot step.pivot inputs) agree
    simp only [readout]
    rw [old]
  · rw [FiniteLatentSCM.withPrivateBooleanNoise_mechanism_of_ne base _ _ _ _ same,
      FiniteLatentSCM.withPrivateBooleanNoise_mechanism_of_ne base _ _ _ _ same]
    exact respects child first second _ agree

/-- Exact full-value evaluation, including responding descendants.  The
descendants keep their values because their mechanisms ignore *labels*
within a bit class, not because they ignore the pivot's binary value.
Every intervention and every supplied original latent unit is covered. -/
theorem evalNodeUnder (step : Step rich) (base : ExactModel S)
    (respects : RespectsParentBits base rich)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (fresh : Bool) (child : Fin S.count) :
    (step.apply base).evalNodeUnder intervention
        (PrivateBooleanNoise.assignment base.latent fresh old) child =
      step.assignment intervention (base.evalUnder intervention old) fresh child := by
  have parentsAgree : forall parent (edge : S.directed parent child = true),
      bit rich parent ((step.apply base).evalNodeUnder intervention
        (PrivateBooleanNoise.assignment base.latent fresh old) parent) =
      bit rich parent (base.evalNodeUnder intervention old parent) := by
    intro parent edge
    rw [step.evalNodeUnder base respects intervention old fresh parent]
    exact congrFun (step.assignment_bits intervention (base.evalUnder intervention old) fresh) parent
  by_cases same : child = step.pivot
  · subst child
    cases selected : intervention step.pivot with
    | some value =>
        simp only [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.equationUnder,
          selected, assignment, Option.isSome, if_true]
        exact (base.evalUnder_effectiveness intervention old step.pivot value selected).symm
    | none =>
        rw [FiniteLatentSCM.evalNodeUnder]
        simp only [FiniteLatentSCM.equationUnder, selected]
        dsimp only [apply, FiniteLatentSCM.withPrivateReadout]
        rw [FiniteLatentSCM.withPrivateBooleanNoise_mechanism_pivot]
        unfold PrivateBooleanNoise.oldInputs PrivateBooleanNoise.bit
        simp only [PrivateBooleanNoise.assignment_castSucc, PrivateBooleanNoise.assignment_last]
        have oldResponse := respects step.pivot
          (fun parent _edge => (step.apply base).evalNodeUnder intervention
            (PrivateBooleanNoise.assignment base.latent fresh old) parent)
          (fun parent _edge => base.evalNodeUnder intervention old parent)
          (fun root _selected => old root) parentsAgree
        change step.readout _
          (base.mechanism step.pivot
            (fun parent _edge => (step.apply base).evalNodeUnder intervention
              (PrivateBooleanNoise.assignment base.latent fresh old) parent)
            (fun root _selected => old root)) fresh = _
        rw [oldResponse]
        simp only [assignment, selected, Option.isSome, Bool.false_eq_true, if_false,
          ObservedSignature.privateReadoutAssignment, ObservedSignature.replace, dite_true]
        have equation : base.evalUnder intervention old step.pivot =
            base.mechanism step.pivot
              (fun parent _edge => base.evalNodeUnder intervention old parent)
              (fun root _selected => old root) := by
          change base.evalNodeUnder intervention old step.pivot = _
          rw [FiniteLatentSCM.evalNodeUnder]
          simp only [FiniteLatentSCM.equationUnder, selected]
        rw [equation]
        rfl
  · rw [step.assignment_of_ne intervention _ fresh child same]
    change (step.apply base).evalNodeUnder intervention _ child =
      base.evalNodeUnder intervention old child
    rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
    cases selected : intervention child with
    | some value => simp only [FiniteLatentSCM.equationUnder, selected]
    | none =>
        simp only [FiniteLatentSCM.equationUnder, selected]
        dsimp only [apply, FiniteLatentSCM.withPrivateReadout]
        rw [FiniteLatentSCM.withPrivateBooleanNoise_mechanism_of_ne base _ _ _ _ same]
        unfold PrivateBooleanNoise.oldInputs
        simp only [PrivateBooleanNoise.assignment_castSucc]
        exact respects child _ _ _ parentsAgree
termination_by child.val
decreasing_by exact S.directed_earlier edge

theorem evalUnder (step : Step rich) (base : ExactModel S)
    (respects : RespectsParentBits base rich)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (old : base.latent.Assignment) (fresh : Bool) :
    (step.apply base).evalUnder intervention
        (PrivateBooleanNoise.assignment base.latent fresh old) =
      step.assignment intervention (base.evalUnder intervention old) fresh :=
  funext (step.evalNodeUnder base respects intervention old fresh)

/-- Integrate the actual independent private factor.  The right-hand side
is a common stochastic map of the old *complete* observed assignment, not
only an equality of decoded marginals. -/
theorem observationalValue (step : Step rich) (base : ExactModel S)
    (respects : RespectsParentBits base rich) (event : Event S.Assignment) :
    QProb.Equiv ((step.apply base).observationalValue event)
      ((noise.product base.observationalDist).probVal
        (fun pair => event (step.assignment (FiniteLatentSCM.noIntervention S) pair.2 pair.1))) := by
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun unit => event ((step.apply base).eval unit))
  have evaluated := (noise.product base.prior).probVal_congr _ _ (fun pair =>
    congrArg event (step.evalUnder base respects (FiniteLatentSCM.noIntervention S) pair.2 pair.1))
  have observed := noise.product_map_right_probVal base.prior base.eval
    (fun pair => event (step.assignment (FiniteLatentSCM.noIntervention S) pair.2 pair.1))
  exact QProb.equiv_trans ((step.apply base).observationalValue_eq event)
    (QProb.equiv_trans pushed (QProb.equiv_trans evaluated (QProb.equiv_symm observed)))

/-- Apply the same refinement to both models.  Their latent spaces and
prior denominators may differ; the common observed map is compared one
fresh-input slice at a time. -/
theorem observationally_equivalent (step : Step rich) (left right : ExactModel S)
    (leftRespects : RespectsParentBits left rich) (rightRespects : RespectsParentBits right rich)
    (equivalent : ObservationallyEquivalent left right) :
    ObservationallyEquivalent (step.apply left) (step.apply right) := by
  intro event
  exact QProb.equiv_trans (step.observationalValue left leftRespects event)
    (QProb.equiv_trans (noise.product_probVal_equiv_of_slices left.observationalDist right.observationalDist
      (fun pair => event (step.assignment (FiniteLatentSCM.noIntervention S) pair.2 pair.1))
      (fun pair => event (step.assignment (FiniteLatentSCM.noIntervention S) pair.2 pair.1))
      (fun fresh => equivalent (fun sample =>
        event (step.assignment (FiniteLatentSCM.noIntervention S) sample fresh))))
      (QProb.equiv_symm (step.observationalValue right rightRespects event)))

/-- Every bit-dependent interventional event keeps its exact probability.
The fresh coin is integrated, rather than restricted to a favourable unit. -/
theorem interventionalBitsValue (step : Step rich) (base : ExactModel S)
    (respects : RespectsParentBits base rich)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : Event (Fin S.count -> Bool)) :
    QProb.Equiv ((step.apply base).interventionalValue intervention (fun sample => event (bits rich sample)))
      (base.interventionalValue intervention (fun sample => event (bits rich sample))) := by
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun unit => event (bits rich ((step.apply base).evalUnder intervention unit)))
  have evaluated := (noise.product base.prior).probVal_congr
    (fun pair => event (bits rich ((step.apply base).evalUnder intervention
      (PrivateBooleanNoise.assignment base.latent pair.1 pair.2))))
    (fun pair => event (bits rich (base.evalUnder intervention pair.2))) (by
    intro pair
    exact congrArg event ((congrArg (bits rich)
      (step.evalUnder base respects intervention pair.2 pair.1)).trans
      (step.assignment_bits intervention (base.evalUnder intervention pair.2) pair.1)))
  have integrated := noise.product_probVal_right base.prior
    (fun unit => event (bits rich (base.evalUnder intervention unit)))
  exact QProb.equiv_trans ((step.apply base).interventionalValue_eq intervention _)
    (QProb.equiv_trans pushed (QProb.equiv_trans evaluated
      (QProb.equiv_trans integrated (QProb.equiv_symm (base.interventionalValue_eq intervention _)))))

/-- A positive old observed atom and a supported private input give a
positive new observed atom at their explicit image. -/
theorem image_positive (step : Step rich) (base : ExactModel S)
    (respects : RespectsParentBits base rich) (sample : S.Assignment)
    (positive : base.observationalDist.EventPositive (FiniteProbRecord.singletonEvent sample))
    (fresh : Bool) :
    (step.apply base).observationalDist.EventPositive
      (FiniteProbRecord.singletonEvent
        (step.assignment (FiniteLatentSCM.noIntervention S) sample fresh)) := by
  let target := step.assignment (FiniteLatentSCM.noIntervention S) sample fresh
  let rectangle := fun pair : Bool × S.Assignment =>
    FiniteProbRecord.singletonEvent fresh pair.1 && FiniteProbRecord.singletonEvent sample pair.2
  let image := fun pair : Bool × S.Assignment =>
    FiniteProbRecord.singletonEvent target
      (step.assignment (FiniteLatentSCM.noIntervention S) pair.2 pair.1)
  have rectanglePositive : 0 < FiniteProbRecord.eventMass (noise.product base.observationalDist).atoms rectangle := by
    rw [FiniteProbRecord.product, FiniteProbRecord.eventMass_weightedCartesian]
    exact Nat.mul_pos (noise_positive fresh) positive
  have included : forall pair, rectangle pair = true -> image pair = true := by
    intro pair selected
    have selected := Bool.and_eq_true_iff.mp selected
    have inputEqual : pair.1 = fresh := of_decide_eq_true selected.1
    have sampleEqual : pair.2 = sample := of_decide_eq_true selected.2
    exact decide_eq_true (by rw [inputEqual, sampleEqual])
  have positiveImage := Nat.lt_of_lt_of_le rectanglePositive
    (FiniteProbRecord.eventMass_mono _ rectangle image included)
  exact (QProb.equiv_num_pos_iff (step.observationalValue base respects
    (FiniteProbRecord.singletonEvent target))).mpr positiveImage

end Step

/-! ## Finite label plans and the full-alphabet support argument -/

/-- Install the head first, then every remaining independent instruction.
Repeated pivots are intentional: a node has one candidate for each bit-zero
label, not one shared noise bit for its entire label family. -/
def applyPlan (rich : ObservedSignature.ValueRich S) (base : ExactModel S) :
    List (Step rich) -> ExactModel S
  | [] => base
  | step :: rest => applyPlan rich (step.apply base) rest

theorem applyPlan_respectsParentBits (rich : ObservedSignature.ValueRich S)
    (steps : List (Step rich)) (base : ExactModel S) (respects : RespectsParentBits base rich) :
    RespectsParentBits (applyPlan rich base steps) rich := by
  induction steps generalizing base with
  | nil => exact respects
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis (step.apply base) (step.respectsParentBits base respects)

theorem applyPlan_compatible (rich : ObservedSignature.ValueRich S) (steps : List (Step rich))
    (base : ExactModel S) {graph : ObservedGraph S} (member : Compatible base graph) :
    Compatible (applyPlan rich base steps) graph := by
  induction steps generalizing base with
  | nil => exact member
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis (step.apply base) (step.compatible base member)

theorem applyPlan_observationally_equivalent (rich : ObservedSignature.ValueRich S)
    (steps : List (Step rich)) (left right : ExactModel S)
    (leftRespects : RespectsParentBits left rich) (rightRespects : RespectsParentBits right rich)
    (equivalent : ObservationallyEquivalent left right) :
    ObservationallyEquivalent (applyPlan rich left steps) (applyPlan rich right steps) := by
  induction steps generalizing left right with
  | nil => exact equivalent
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis (step.apply left) (step.apply right)
        (step.respectsParentBits left leftRespects) (step.respectsParentBits right rightRespects)
        (step.observationally_equivalent left right leftRespects rightRespects equivalent)

theorem applyPlan_interventionalBitsValue (rich : ObservedSignature.ValueRich S)
    (steps : List (Step rich)) (base : ExactModel S) (respects : RespectsParentBits base rich)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : Event (Fin S.count -> Bool)) :
    QProb.Equiv ((applyPlan rich base steps).interventionalValue intervention (fun sample => event (bits rich sample)))
      (base.interventionalValue intervention (fun sample => event (bits rich sample))) := by
  induction steps generalizing base with
  | nil => exact QProb.equiv_refl _
  | cons step rest inductionHypothesis =>
      exact QProb.equiv_trans
        (inductionHypothesis (step.apply base) (step.respectsParentBits base respects))
        (step.interventionalBitsValue base respects intervention event)

/-- Explicit target-directed label selection.  This is proof data for
support, not a change of the installed prior: each chosen input is an atom
of its own actual supported private coin. -/
def targetMap (rich : ObservedSignature.ValueRich S) (target : S.Assignment) :
    List (Step rich) -> S.Assignment -> S.Assignment
  | [], sample => sample
  | step :: rest, sample => targetMap rich target rest
      (if step.label = target step.pivot then S.replace sample step.pivot (target step.pivot) else sample)

private theorem targetStep_eq (rich : ObservedSignature.ValueRich S) (step : Step rich)
    (target sample : S.Assignment) (agree : bits rich sample = bits rich target) :
    step.assignment (FiniteLatentSCM.noIntervention S) sample (decide (step.label = target step.pivot)) =
      (if step.label = target step.pivot then S.replace sample step.pivot (target step.pivot) else sample) := by
  by_cases selected : step.label = target step.pivot
  · have oldBit : bit rich step.pivot (sample step.pivot) = false := by
      have := congrFun agree step.pivot
      change bit rich step.pivot (sample step.pivot) = bit rich step.pivot (target step.pivot) at this
      rw [← selected] at this
      exact this.trans step.label_bit
    simp only [Step.assignment, FiniteLatentSCM.noIntervention, Option.isSome, Bool.false_eq_true,
      if_false, ObservedSignature.privateReadoutAssignment, Step.readout, oldBit,
      if_true, selected, decide_true]
  · simp only [Step.assignment, FiniteLatentSCM.noIntervention, Option.isSome, Bool.false_eq_true,
      if_false, ObservedSignature.privateReadoutAssignment, Step.readout,
      decide_eq_false selected, if_neg selected]
    funext node
    by_cases same : node = step.pivot
    · subst node
      rw [ObservedSignature.replace_at]
      cases bit rich step.pivot (sample step.pivot) <;> rfl
    · exact S.replace_ne sample step.pivot node _ same

private theorem targetStep_bits (rich : ObservedSignature.ValueRich S) (step : Step rich)
    (target sample : S.Assignment) (agree : bits rich sample = bits rich target) :
    bits rich (if step.label = target step.pivot then S.replace sample step.pivot (target step.pivot) else sample) =
      bits rich target := by
  rw [← targetStep_eq rich step target sample agree, step.assignment_bits]
  exact agree

private theorem targetMap_bits (rich : ObservedSignature.ValueRich S) (steps : List (Step rich))
    (target sample : S.Assignment) (agree : bits rich sample = bits rich target) :
    bits rich (targetMap rich target steps sample) = bits rich target := by
  induction steps generalizing sample with
  | nil => exact agree
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis _ (targetStep_bits rich step target sample agree)

private theorem targetMap_positive (rich : ObservedSignature.ValueRich S) (steps : List (Step rich))
    (base : ExactModel S) (respects : RespectsParentBits base rich) (target sample : S.Assignment)
    (agree : bits rich sample = bits rich target)
    (positive : base.observationalDist.EventPositive (FiniteProbRecord.singletonEvent sample)) :
    (applyPlan rich base steps).observationalDist.EventPositive
      (FiniteProbRecord.singletonEvent (targetMap rich target steps sample)) := by
  induction steps generalizing base sample with
  | nil => exact positive
  | cons step rest inductionHypothesis =>
      have image := step.image_positive base respects sample (positive := positive)
        (decide (step.label = target step.pivot))
      rw [targetStep_eq rich step target sample agree] at image
      exact inductionHypothesis (step.apply base) (step.respectsParentBits base respects) _
        (targetStep_bits rich step target sample agree) image

private theorem targetMap_keeps (rich : ObservedSignature.ValueRich S) (steps : List (Step rich))
    (target sample : S.Assignment) (node : Fin S.count) (same : sample node = target node) :
    targetMap rich target steps sample node = target node := by
  induction steps generalizing sample with
  | nil => exact same
  | cons step rest inductionHypothesis =>
      apply inductionHypothesis
      by_cases selected : step.label = target step.pivot
      · rw [if_pos selected]
        by_cases pivot : node = step.pivot
        · subst node; exact S.replace_at sample step.pivot _
        · exact (S.replace_ne sample step.pivot node _ pivot).trans same
      · simpa only [if_neg selected] using same

private theorem targetMap_selected (rich : ObservedSignature.ValueRich S) (steps : List (Step rich))
    (target sample : S.Assignment) (step : Step rich) (listed : step ∈ steps)
    (selected : step.label = target step.pivot) :
    targetMap rich target steps sample step.pivot = target step.pivot := by
  induction steps generalizing sample with
  | nil => cases listed
  | cons head rest inductionHypothesis =>
      cases List.mem_cons.mp listed with
      | inl same =>
          subst head
          simp only [targetMap, if_pos selected]
          exact targetMap_keeps rich rest target _ step.pivot (S.replace_at sample step.pivot _)
      | inr later => exact inductionHypothesis _ later

/-- Every bit-zero candidate of every coordinate, in the existing finite
enumeration order.  Repeated pivots are harmless, and only decidable label
equality is tested.  No representative of a fibre is chosen. -/
def allSteps (rich : ObservedSignature.ValueRich S) : List (Step rich) :=
  (NodeSet.enumerated S).flatMap fun node => (S.valueEnumeration node).flatMap fun label =>
    if selected : label = rich.second node then [] else
      [⟨node, label, by simp only [bit, decide_eq_false selected]⟩]

private theorem allSteps_covers (rich : ObservedSignature.ValueRich S) (target : S.Assignment)
    (node : Fin S.count) (zero : bit rich node (target node) = false) :
    Exists fun step : Step rich => step ∈ allSteps rich ∧ step.pivot = node ∧ step.label = target step.pivot := by
  have different : target node ≠ rich.second node := of_decide_eq_false zero
  let step : Step rich := ⟨node, target node, zero⟩
  refine ⟨step, ?_, rfl, rfl⟩
  unfold allSteps
  apply List.mem_flatMap.mpr
  refine ⟨node, List.mem_finRange node, List.mem_flatMap.mpr ?_⟩
  refine ⟨target node, S.value_complete node (target node), ?_⟩
  change step ∈ (if selected : target node = rich.second node then [] else
    [⟨node, target node, by simp only [bit, decide_eq_false selected]⟩])
  rw [dif_neg different]
  exact List.mem_cons_self

private theorem targetMap_allSteps (rich : ObservedSignature.ValueRich S)
    (target sample : S.Assignment) (agree : bits rich sample = bits rich target) :
    targetMap rich target (allSteps rich) sample = target := by
  funext node
  cases selected : bit rich node (target node) with
  | true =>
      have finalBit := congrFun (targetMap_bits rich (allSteps rich) target sample agree) node
      change bit rich node (targetMap rich target (allSteps rich) sample node) = bit rich node (target node) at finalBit
      rw [selected] at finalBit
      exact (of_decide_eq_true finalBit).trans (of_decide_eq_true selected).symm
  | false =>
      rcases allSteps_covers rich target node selected with ⟨step, listed, pivot, label⟩
      have final := targetMap_selected rich (allSteps rich) target sample step listed label
      rw [pivot] at final
      exact final

private theorem positive_atom_of_event (atoms : List (S.Assignment × Nat)) (event : Event S.Assignment)
    (positive : 0 < FiniteProbRecord.eventMass atoms event) :
    Exists fun atom => atom ∈ atoms ∧ 0 < atom.2 ∧ event atom.1 = true := by
  induction atoms with
  | nil => exact False.elim (Nat.not_lt_zero _ positive)
  | cons atom rest inductionHypothesis =>
      cases selected : event atom.1 with
      | false =>
          have tail : 0 < FiniteProbRecord.eventMass rest event := by
            simpa only [FiniteProbRecord.eventMass, selected, Bool.false_eq_true, if_false, Nat.zero_add] using positive
          rcases inductionHypothesis tail with ⟨found, member, weight, accepted⟩
          exact ⟨found, List.mem_cons_of_mem atom member, weight, accepted⟩
      | true =>
          by_cases weight : 0 < atom.2
          · exact ⟨atom, List.mem_cons_self, weight, selected⟩
          · have tail : 0 < FiniteProbRecord.eventMass rest event := by
              have zero : atom.2 = 0 := Nat.eq_zero_of_not_pos weight
              simpa only [FiniteProbRecord.eventMass, selected, if_true, zero, Nat.zero_add] using positive
            rcases inductionHypothesis tail with ⟨found, member, weight, accepted⟩
            exact ⟨found, List.mem_cons_of_mem atom member, weight, accepted⟩

private theorem atom_le_singleton (atoms : List (S.Assignment × Nat)) (atom : S.Assignment × Nat)
    (member : atom ∈ atoms) :
    atom.2 ≤ FiniteProbRecord.eventMass atoms (FiniteProbRecord.singletonEvent atom.1) := by
  induction atoms with
  | nil => cases member
  | cons head rest inductionHypothesis =>
      cases List.mem_cons.mp member with
      | inl same =>
          subst head
          simp only [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent, decide_true, if_true]
          exact Nat.le_add_right _ _
      | inr later =>
          exact Nat.le_trans (inductionHypothesis later) (by
            cases selected : FiniteProbRecord.singletonEvent atom.1 head.1 <;>
              simp only [FiniteProbRecord.eventMass, selected, Bool.false_eq_true,
                if_false, if_true] <;> omega)

/-- The support obligation of a binary core.  Only the decoded joint needs
full support at this stage; individual nonbinary labels need not occur yet. -/
def BitsPositive (base : ExactModel S) (rich : ObservedSignature.ValueRich S) : Prop :=
  forall target : S.Assignment, base.observationalDist.EventPositive
    (fun sample => decide (bits rich sample = bits rich target))

/-- The complete finite label sweep.  The supplied observed signature,
directed graph, and two distinguished values are unchanged. -/
def refine (rich : ObservedSignature.ValueRich S) (base : ExactModel S) : ExactModel S :=
  applyPlan rich base (allSteps rich)

/-- Every supplied full-alphabet assignment has positive mass.  We extract
one supported old atom inside a proposition, and then explicitly give each
refinement its own supported input.  This is existential elimination in a
finite support proof, not selection of a family by an axiom of choice. -/
theorem refine_positive (rich : ObservedSignature.ValueRich S) (base : ExactModel S)
    (respects : RespectsParentBits base rich) (positive : BitsPositive base rich) :
    ObservationallyPositive (refine rich base) := by
  intro target
  rcases positive_atom_of_event base.observationalDist.atoms _ (positive target) with
    ⟨atom, listed, weight, selected⟩
  have agree : bits rich atom.1 = bits rich target := of_decide_eq_true selected
  have oldPositive : base.observationalDist.EventPositive (FiniteProbRecord.singletonEvent atom.1) :=
    Nat.lt_of_lt_of_le weight (atom_le_singleton base.observationalDist.atoms atom listed)
  have final := targetMap_positive rich (allSteps rich) base respects target atom.1 agree oldPositive
  rw [targetMap_allSteps rich target atom.1 agree] at final
  exact final

/-- The complete sweep retains the same canonical semi-Markovian graph. -/
theorem refine_compatible (rich : ObservedSignature.ValueRich S) (base : ExactModel S)
    {graph : ObservedGraph S} (member : Compatible base graph) :
    Compatible (refine rich base) graph :=
  applyPlan_compatible rich (allSteps rich) base member

/-- No parent begins to inspect a newly introduced label. -/
theorem refine_respectsParentBits (rich : ObservedSignature.ValueRich S) (base : ExactModel S)
    (respects : RespectsParentBits base rich) : RespectsParentBits (refine rich base) rich :=
  applyPlan_respectsParentBits rich (allSteps rich) base respects

/-- Refining both sides preserves equality of every full observed event,
including events distinguishing any of the additional supplied labels. -/
theorem refine_observationally_equivalent (rich : ObservedSignature.ValueRich S)
    (left right : ExactModel S)
    (leftRespects : RespectsParentBits left rich) (rightRespects : RespectsParentBits right rich)
    (equivalent : ObservationallyEquivalent left right) :
    ObservationallyEquivalent (refine rich left) (refine rich right) :=
  applyPlan_observationally_equivalent rich (allSteps rich) left right leftRespects rightRespects equivalent

/-- Preserve every decoded event under every intervention.  The arbitrary
finite label alphabets are retained; only the event factors through bits. -/
theorem refine_interventionalBitsValue (rich : ObservedSignature.ValueRich S) (base : ExactModel S)
    (respects : RespectsParentBits base rich)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : Event (Fin S.count -> Bool)) :
    QProb.Equiv ((refine rich base).interventionalValue intervention (fun sample => event (bits rich sample)))
      (base.interventionalValue intervention (fun sample => event (bits rich sample))) :=
  applyPlan_interventionalBitsValue rich (allSteps rich) base respects intervention event

end ObservedValueRefinement
end Causality
end Thesis
