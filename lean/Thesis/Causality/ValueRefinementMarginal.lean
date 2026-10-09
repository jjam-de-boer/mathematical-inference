import Thesis.Causality.BinaryEncoding
import Thesis.Causality.Identification

namespace Thesis
namespace Causality

open Probability

/-!
# Matched interventional marginals through full-alphabet refinement

A binary numerator gap is not sufficient for conditional non-identifiability:
the conditioning denominator must be compared in the same final models.
The original refinement theorem preserves decoded events in each model, but
a conditioning kernel on the original alphabet also distinguishes individual
labels inside a decoded fibre.  This module proves the stronger pairwise
marginal transport needed for that denominator.

Each private label step is a common stochastic map of the old assignment.
On a selected coordinate set, that map reads only the same selected old
coordinates.  Thus equality of every old local event probability implies
equality of every new local event probability, even when the step refines a
selected coordinate.  It is not necessary to keep the conditioner outside
the refinement pivots, to protect all its parents, or to assume full-joint
interventional equality.

The deterministic binary encoding is treated separately.  An arbitrary
forced original label is retained verbatim, while every free output is the
encoding of its actual binary response.  The displayed coordinatewise map
therefore transports a matched binary marginal to the original alphabet.
The complete private sweep then transports that marginal to the same fully
positive models used by `ValueRefinementCounterexample`.  No conditional
graph lemma or denominator agreement is silently assumed proved here.
-/

variable {S : ObservedSignature.{0}}

namespace ObservedValueRefinement
namespace Step

variable {rich : ObservedSignature.ValueRich S}

/-- The complete interventional law after one label refinement is its
actual common stochastic assignment map applied to the old interventional
law.  The independent fresh factor is integrated without conditioning on
a favourable input, including when the pivot itself is intervened on. -/
theorem interventionalValue (step : Step rich) (base : ExactModel S)
    (respects : RespectsParentBits base rich)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (event : Event S.Assignment) :
    QProb.Equiv ((step.apply base).interventionalValue target event)
      ((noise.product (base.interventionalDist target)).probVal
        (fun pair => event (step.assignment target pair.2 pair.1))) := by
  have pushed := (noise.product base.prior).map_probVal
    (fun pair => PrivateBooleanNoise.assignment base.latent pair.1 pair.2)
    (fun unit => event ((step.apply base).evalUnder target unit))
  have evaluated := (noise.product base.prior).probVal_congr _ _ (fun pair =>
    congrArg event (step.evalUnder base respects target pair.2 pair.1))
  have observed := noise.product_map_right_probVal base.prior (base.evalUnder target)
    (fun pair => event (step.assignment target pair.2 pair.1))
  exact QProb.equiv_trans ((step.apply base).interventionalValue_eq target event)
    (QProb.equiv_trans pushed (QProb.equiv_trans evaluated (QProb.equiv_symm observed)))

/-- A label step cannot make a selected-coordinate event inspect another
old coordinate.  The readout ignores parent labels; responding descendants
have already been handled by the exact full-assignment evaluation theorem. -/
theorem assignment_agreesOn (step : Step rich)
    (target : (node : Fin S.count) -> Option (S.Value node))
    (nodes : NodeSet S) (first second : S.Assignment)
    (agree : AssignmentsAgreeOn nodes first second) (fresh : Bool) :
    AssignmentsAgreeOn nodes (step.assignment target first fresh)
      (step.assignment target second fresh) := by
  intro child selected
  by_cases same : child = step.pivot
  · subst child
    cases forced : target step.pivot <;>
      simp only [assignment, forced, Option.isSome, Bool.false_eq_true, if_false, if_true,
        ObservedSignature.privateReadoutAssignment, ObservedSignature.replace, dite_true,
        readout, agree step.pivot selected]
  · rw [step.assignment_of_ne target first fresh child same,
      step.assignment_of_ne target second fresh child same]
    exact agree child selected

/-- Equality of all selected old event probabilities survives the same
actual refinement on both models.  Their latent supports and denominators
may differ; equality is compared one actual fresh-input slice at a time. -/
theorem interventionalMarginals_equivalent (step : Step rich) (left right : ExactModel S)
    (leftRespects : RespectsParentBits left rich) (rightRespects : RespectsParentBits right rich)
    (target : (node : Fin S.count) -> Option (S.Value node)) (nodes : NodeSet S)
    (equivalent : forall event : Event S.Assignment, EventDependsOnlyOn nodes event ->
      QProb.Equiv (left.interventionalValue target event) (right.interventionalValue target event))
    (event : Event S.Assignment) (localEvent : EventDependsOnlyOn nodes event) :
    QProb.Equiv ((step.apply left).interventionalValue target event)
      ((step.apply right).interventionalValue target event) := by
  have slices (fresh : Bool) : QProb.Equiv
      ((left.interventionalDist target).probVal (fun sample => event (step.assignment target sample fresh)))
      ((right.interventionalDist target).probVal (fun sample => event (step.assignment target sample fresh))) :=
    equivalent _ (fun first second agree =>
      localEvent _ _ (step.assignment_agreesOn target nodes first second agree fresh))
  exact QProb.equiv_trans (step.interventionalValue left leftRespects target event)
    (QProb.equiv_trans (noise.product_probVal_equiv_of_slices
      (left.interventionalDist target) (right.interventionalDist target)
      (fun pair => event (step.assignment target pair.2 pair.1))
      (fun pair => event (step.assignment target pair.2 pair.1)) slices)
      (QProb.equiv_symm (step.interventionalValue right rightRespects target event)))

end Step

/-- A complete supplied refinement plan preserves pairwise equality of
the selected interventional marginal.  Each induction step transports the
parent-bit invariant as well as the actual local-event comparison. -/
theorem applyPlan_interventionalMarginals_equivalent (rich : ObservedSignature.ValueRich S)
    (steps : List (Step rich)) (left right : ExactModel S)
    (leftRespects : RespectsParentBits left rich) (rightRespects : RespectsParentBits right rich)
    (target : (node : Fin S.count) -> Option (S.Value node)) (nodes : NodeSet S)
    (equivalent : forall event : Event S.Assignment, EventDependsOnlyOn nodes event ->
      QProb.Equiv (left.interventionalValue target event) (right.interventionalValue target event))
    (event : Event S.Assignment) (localEvent : EventDependsOnlyOn nodes event) :
    QProb.Equiv ((applyPlan rich left steps).interventionalValue target event)
      ((applyPlan rich right steps).interventionalValue target event) := by
  induction steps generalizing left right with
  | nil => exact equivalent event localEvent
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis (step.apply left) (step.apply right)
        (step.respectsParentBits left leftRespects) (step.respectsParentBits right rightRespects)
        (step.interventionalMarginals_equivalent left right leftRespects rightRespects target nodes equivalent)

/-- The actual full-alphabet label sweep preserves a matched marginal,
including events distinguishing labels inside the bit-zero fibre.  This is
pairwise preservation, not an assertion that either model's old full-label
probabilities remain unchanged by the sweep. -/
theorem refine_interventionalMarginals_equivalent (rich : ObservedSignature.ValueRich S)
    (left right : ExactModel S)
    (leftRespects : RespectsParentBits left rich) (rightRespects : RespectsParentBits right rich)
    (target : (node : Fin S.count) -> Option (S.Value node)) (nodes : NodeSet S)
    (equivalent : forall event : Event S.Assignment, EventDependsOnlyOn nodes event ->
      QProb.Equiv (left.interventionalValue target event) (right.interventionalValue target event))
    (event : Event S.Assignment) (localEvent : EventDependsOnlyOn nodes event) :
    QProb.Equiv ((refine rich left).interventionalValue target event)
      ((refine rich right).interventionalValue target event) :=
  applyPlan_interventionalMarginals_equivalent rich (allSteps rich) left right leftRespects rightRespects
    target nodes equivalent event localEvent

end ObservedValueRefinement

namespace BinaryEncoding

/-- Reconstruct a full original-label assignment under the original
intervention: free rows encode their actual binary output, while forced rows
retain their supplied label even when it is neither distinguished label. -/
def assignmentUnder (rich : ObservedSignature.ValueRich S)
    (target : (node : Fin S.count) -> Option (S.Value node)) (sample : S.binary.Assignment) :
    S.Assignment :=
  fun child => match target child with
    | some forced => forced
    | none => value rich child (sample child)

/-- Exact full-value evaluation of the encoded model under arbitrary
original-label interventions.  Decoding only the intervention would lose
the forced label; the explicit reconstruction map retains it. -/
theorem evalUnder_eq_assignmentUnder (rich : ObservedSignature.ValueRich S)
    (base : ExactModel S.binary) (target : (node : Fin S.count) -> Option (S.Value node))
    (unit : base.latent.Assignment) :
    (model rich base).evalUnder target unit =
      assignmentUnder rich target (base.evalUnder (intervention rich target) unit) := by
  funext child
  cases forced : target child with
  | some label =>
      change (model rich base).evalNodeUnder target unit child = _
      rw [FiniteLatentSCM.evalNodeUnder]
      simp only [FiniteLatentSCM.equationUnder, forced, assignmentUnder]
  | none =>
      change (model rich base).evalNodeUnder target unit child = _
      rw [FiniteLatentSCM.evalNodeUnder]
      simp only [FiniteLatentSCM.equationUnder, forced, model, assignmentUnder]
      have parents : (fun parent (_edge : S.directed parent child = true) => ObservedValueRefinement.bit rich parent
          ((model rich base).evalNodeUnder target unit parent)) =
          (fun parent (_edge : S.directed parent child = true) =>
            base.evalNodeUnder (intervention rich target) unit parent) := by
        funext parent edge
        exact evalNodeUnder_bit rich base target unit parent
      refine (congrArg (fun parents => value rich child
        (base.mechanism child parents (fun root _selected => unit root))) parents).trans ?_
      change value rich child (base.mechanism child _ _) =
        value rich child (base.evalNodeUnder (intervention rich target) unit child)
      rw [FiniteLatentSCM.evalNodeUnder]
      simp only [FiniteLatentSCM.equationUnder, intervention, forced, Option.map_none]
      rfl

/-- Every full-label interventional event in the encoded model is the
displayed event on the actual binary response.  This is stronger than
preservation only of decoded events, and is needed for full-value marginals. -/
theorem interventionalValue (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    (target : (node : Fin S.count) -> Option (S.Value node)) (event : Event S.Assignment) :
    QProb.Equiv ((model rich base).interventionalValue target event)
      (base.interventionalValue (intervention rich target)
        (fun sample => event (assignmentUnder rich target sample))) :=
  QProb.equiv_trans ((model rich base).interventionalValue_eq target event)
    (QProb.equiv_trans (base.prior.probVal_congr _ _
      (fun unit => congrArg event (evalUnder_eq_assignmentUnder rich base target unit)))
      (QProb.equiv_symm (base.interventionalValue_eq _ _)))

end BinaryEncoding

namespace ObservedValueRefinement

/-- A matched binary interventional marginal remains matched on the full
original alphabet after both encoding and the actual private label sweep.
The selected node set and the original intervention are unchanged, and the
final event need not factor through bits.  The binary agreement is an explicit
obligation of the graph-specific countermodel argument, not hidden here. -/
theorem refine_encoded_interventionalMarginals_equivalent (rich : ObservedSignature.ValueRich S)
    (left right : ExactModel S.binary)
    (target : (node : Fin S.count) -> Option (S.Value node)) (nodes : NodeSet S)
    (equivalent : forall event : Event S.binary.Assignment, EventDependsOnlyOn (S := S.binary) nodes event ->
      QProb.Equiv (left.interventionalValue (BinaryEncoding.intervention rich target) event)
        (right.interventionalValue (BinaryEncoding.intervention rich target) event))
    (event : Event S.Assignment) (localEvent : EventDependsOnlyOn nodes event) :
    QProb.Equiv ((refine rich (BinaryEncoding.model rich left)).interventionalValue target event)
      ((refine rich (BinaryEncoding.model rich right)).interventionalValue target event) := by
  apply refine_interventionalMarginals_equivalent rich _ _
    (BinaryEncoding.respectsParentBits rich left) (BinaryEncoding.respectsParentBits rich right)
    target nodes _ event localEvent
  intro oldEvent oldLocal
  have binaryLocal : EventDependsOnlyOn (S := S.binary) nodes
      (fun sample => oldEvent (BinaryEncoding.assignmentUnder rich target sample)) := by
    intro first second agree
    apply oldLocal
    intro child selected
    cases forced : target child <;>
      simp only [BinaryEncoding.assignmentUnder, forced, agree child selected]
  exact QProb.equiv_trans (BinaryEncoding.interventionalValue rich left target oldEvent)
    (QProb.equiv_trans (equivalent _ binaryLocal)
      (QProb.equiv_symm (BinaryEncoding.interventionalValue rich right target oldEvent)))

end ObservedValueRefinement

/-- Transport the complete original-value joint kernel of a selected
marginal through binary encoding and full-alphabet refinement.  The binary
premise concerns only interventions on the query's unchanged action set;
there is no unnecessary assumption of agreement under every possible cut.
The empty-action branch is covered by the same premise at the literal empty
intervention.  Neither model positivity nor soundness is used in this bridge. -/
theorem JointKernelQuery.refine_encoded_valueEquivalent_of_binaryMarginals
    (query : JointKernelQuery S) (rich : ObservedSignature.ValueRich S)
    (left right : ExactModel S.binary)
    (equivalent : forall (target : Fin S.count -> Option Bool),
      (forall child, (target child).isSome = query.action child) ->
      forall event : Event S.binary.Assignment, EventDependsOnlyOn (S := S.binary) query.outcome event ->
        QProb.Equiv (left.interventionalValue target event) (right.interventionalValue target event)) :
    query.ValueEquivalent (ObservedValueRefinement.refine rich (BinaryEncoding.model rich left))
      (ObservedValueRefinement.refine rich (BinaryEncoding.model rich right)) := by
  intro reference
  let finalLeft := ObservedValueRefinement.refine rich (BinaryEncoding.model rich left)
  let finalRight := ObservedValueRefinement.refine rich (BinaryEncoding.model rich right)
  let kernel := query.operationKernel
  let event := Kernel.agreesOn query.outcome reference
  have localEvent : EventDependsOnlyOn query.outcome event := Kernel.agreesOn_dependsOnlyOn _ _
  have compared (target : (node : Fin S.count) -> Option (S.Value node))
      (targets : forall child, (target child).isSome = query.action child) :
      QProb.Equiv (finalLeft.interventionalValue target event) (finalRight.interventionalValue target event) := by
    apply ObservedValueRefinement.refine_encoded_interventionalMarginals_equivalent rich left right
      target query.outcome _ event localEvent
    apply equivalent (BinaryEncoding.intervention rich target)
    intro child
    simpa only [BinaryEncoding.intervention, Option.isSome_map] using targets child
  have cylinderEqual : QProb.Equiv ((kernel.distribution finalLeft reference).probVal event)
      ((kernel.distribution finalRight reference).probVal event) := by
    unfold Kernel.distribution
    change QProb.Equiv
      ((if finAny S.count query.action then finalLeft.interventionalDist (kernel.intervention reference)
        else finalLeft.observationalDist).probVal event)
      ((if finAny S.count query.action then finalRight.interventionalDist (kernel.intervention reference)
        else finalRight.observationalDist).probVal event)
    cases active : finAny S.count query.action with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        apply compared (FiniteLatentSCM.noIntervention S)
        intro child
        exact ((finAny_eq_false_iff query.action).mp active child).symm
    | true =>
        simp only [if_true]
        apply compared (kernel.intervention reference)
        intro child
        cases selected : query.action child <;>
          simp only [kernel, JointKernelQuery.operationKernel, Kernel.intervention, selected,
            Bool.false_eq_true, if_false, if_true, Option.isSome]
  exact ⟨ProbabilityResult.trans (Kernel.unconditionalDenote finalLeft query.outcome query.action reference)
    (ProbabilityResult.trans (.value cylinderEqual)
      (ProbabilityResult.symm (Kernel.unconditionalDenote finalRight query.outcome query.action reference)))⟩

end Causality
end Thesis
