import Thesis.Causality.Semantics

namespace Thesis
namespace Causality

open Probability

/-!
# Observable local overlap supplies actual causal-kernel support

The SCM layer allows observational zeros.  A displayed conditional kernel
needs a positive conditioner, not a positive complete observed distribution.
For an intervention setting action variables to the reference values, positive
observational mass of the action-and-condition cylinder is sufficient.

The proof compares two Boolean events on the same finite latent prior.
Every unit matching that factual cylinder is unchanged by setting its action
coordinates to their already factual values.  SCM consistency therefore
places that unit in the intervened conditioning cylinder.  Finite event-mass
monotonicity supplies positivity without choosing a latent unit, assuming
do-calculus soundness, or requiring support of the outcome cell.

This is an observable, sufficient support boundary.  It is not claimed to be
necessary for every graph or query.  In particular, an unsupported observed
action may still be identifiable by a different graph-dependent reduction.
-/

/-- Positive observational mass of exactly one selected cylinder.  This is
assignment-local and is decidable from the finite observational record; it
does not require a positive outcome or a positive full joint distribution. -/
def ObservationalCylinderPositiveAt (model : FiniteLatentSCM S)
    (nodes : NodeSet S) (reference : S.Assignment) : Prop :=
  0 < (model.observationalDist.probVal (Kernel.agreesOn nodes reference)).num

/-- A positive cylinder remains positive after forgetting selected coordinates.
This is an event-inclusion statement on the same finite observed record, not
an assumption of positivity at every full assignment.  In particular a
positive action-and-parent cylinder supplies its parent conditioner even
when some outcome cells inside that cylinder have mass zero. -/
theorem ObservationalCylinderPositiveAt.of_subset
    {model : FiniteLatentSCM S} {smaller larger : NodeSet S}
    {reference : S.Assignment} (subset : NodeSet.Subset smaller larger)
    (positive : ObservationalCylinderPositiveAt model larger reference) :
    ObservationalCylinderPositiveAt model smaller reference := by
  have included : forall sample, Kernel.agreesOn larger reference sample = true →
      Kernel.agreesOn smaller reference sample = true := by
    intro sample selected
    apply (finAll_eq_true_iff _).mpr
    intro node
    cases kept : smaller node with
    | false => simp only [kept, Bool.false_eq_true, if_false]
    | true =>
        have present := subset node kept
        have agrees := (finAll_eq_true_iff _).mp selected node
        simpa only [kept, present, if_true] using agrees
  exact Nat.lt_of_lt_of_le positive
    (FiniteProbRecord.eventMass_mono model.observationalDist.atoms
      (Kernel.agreesOn larger reference) (Kernel.agreesOn smaller reference) included)

/-- Observational agreement preserves the local support condition.  The
finite rational numerator test is invariant under probability equivalence. -/
theorem ObservationalCylinderPositiveAt.transfer
    {left right : FiniteLatentSCM S}
    (observational : ProbabilityTerm.ObservationalAgreement left right)
    {nodes : NodeSet S} {reference : S.Assignment}
    (positive : ObservationalCylinderPositiveAt left nodes reference) :
    ObservationalCylinderPositiveAt right nodes reference :=
  (QProb.equiv_num_pos_iff
    (observational (Kernel.agreesOn nodes reference))).mp positive

/-- Construct the displayed conditional from its actual finite numerator and
positive conditioner.  Zero outcome mass is allowed, and no representative
is chosen from an existence proposition. -/
noncomputable def observationalConditional_supportedAt_of_positive
    (model : FiniteLatentSCM S) (outcome condition : NodeSet S)
    (reference : S.Assignment)
    (positive : ObservationalCylinderPositiveAt model condition reference) :
    (ProbabilityTerm.kernel ⟨outcome, NodeSet.empty, condition⟩).SupportedAt
      model reference := by
  let kernel : Kernel S := ⟨outcome, NodeSet.empty, condition⟩
  have noAction : kernel.hasAction = false :=
    ProbabilityTerm.actionFree_hasAction_false kernel (fun _ => rfl)
  have observational : kernel.distribution model reference = model.observationalDist := by
    simp only [Kernel.distribution, noAction, Bool.false_eq_true, if_false]
  let numerator := (kernel.distribution model reference).probVal
    (kernel.numeratorEvent reference)
  let denominator := (kernel.distribution model reference).probVal
    (kernel.conditionEvent reference)
  have denominatorPositive : 0 < denominator.num := by
    simpa only [denominator, observational, kernel, Kernel.conditionEvent] using positive
  refine ⟨QProb.div numerator denominator denominatorPositive, ?_⟩
  change ProbabilityResult.Equivalent
    (ProbabilityResult.divide (some numerator) (some denominator))
    (some (QProb.div numerator denominator denominatorPositive))
  simp only [ProbabilityResult.divide, dif_pos denominatorPositive]
  exact .value (QProb.equiv_refl _)

namespace Kernel

/-- Factual action-and-condition overlap forces the actual kernel conditioner
to have positive intervened mass.  This statement allows overlapping node
sets and arbitrary independent finite latent inputs; no graph-compatibility
or canonical pair-root assumption is needed. -/
theorem condition_positive_of_observational_overlap
    (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment)
    (overlap : ObservationalCylinderPositiveAt model
      (NodeSet.union kernel.action kernel.condition) reference) :
    0 < ((kernel.distribution model reference).probVal
      (kernel.conditionEvent reference)).num := by
  let factualEvent : Event model.latent.Assignment := fun unit =>
    agreesOn (NodeSet.union kernel.action kernel.condition) reference
      (model.eval unit)
  let intervenedEvent : Event model.latent.Assignment := fun unit =>
    kernel.conditionEvent reference
      (model.evalUnder (kernel.intervention reference) unit)
  have subset : forall unit, factualEvent unit = true ->
      intervenedEvent unit = true := by
    intro unit selected
    have cylinder : (agreesOn kernel.action reference (model.eval unit) &&
        agreesOn kernel.condition reference (model.eval unit)) = true := by
      simpa only [factualEvent, agreesOn_union] using selected
    have actionAgreement := (Bool.and_eq_true_iff.mp cylinder).1
    have conditionAgreement := (Bool.and_eq_true_iff.mp cylinder).2
    have consistent : model.evalUnder (kernel.intervention reference) unit =
        model.eval unit := by
      apply model.evalUnder_consistency
      intro node value forced
      cases selectedAction : kernel.action node with
      | false =>
          simp only [intervention, selectedAction, Bool.false_eq_true,
            if_false] at forced
          cases forced
      | true =>
          have component := (finAll_eq_true_iff _).mp actionAgreement node
          have factualValue : model.eval unit node = reference node := by
            apply of_decide_eq_true
            simpa only [selectedAction, if_true] using component
          have referenceValue : reference node = value := by
            simpa only [intervention, selectedAction, if_true,
              Option.some.injEq] using forced
          exact factualValue.trans referenceValue
    change agreesOn kernel.condition reference
      (model.evalUnder (kernel.intervention reference) unit) = true
    rw [consistent]
    exact conditionAgreement
  have factualPositive : 0 < (model.prior.probVal factualEvent).num := by
    exact (QProb.equiv_num_pos_iff
      (model.prior.map_probVal model.eval
        (agreesOn (NodeSet.union kernel.action kernel.condition) reference))).mp overlap
  have monotone : (model.prior.probVal factualEvent).num ≤
      (model.prior.probVal intervenedEvent).num :=
    FiniteProbRecord.eventMass_mono model.prior.atoms factualEvent
      intervenedEvent subset
  have intervenedPositive : 0 < (model.prior.probVal intervenedEvent).num :=
    Nat.lt_of_lt_of_le factualPositive monotone
  exact (QProb.equiv_num_pos_iff
    (Kernel.distribution_probVal model kernel reference
      (kernel.conditionEvent reference))).mpr intervenedPositive

/-- Construct the kernel's rational value from its actual finite numerator
and positive conditioner.  This low-level constructor does not assert that a
causal support condition is observable; the following constructor establishes
that separately using factual overlap. -/
noncomputable def supportedAt_of_condition_positive
    (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment)
    (positive : 0 < ((kernel.distribution model reference).probVal
      (kernel.conditionEvent reference)).num) :
    (ProbabilityTerm.kernel kernel).SupportedAt model reference := by
  let numerator := (kernel.distribution model reference).probVal
    (kernel.numeratorEvent reference)
  let denominator := (kernel.distribution model reference).probVal
    (kernel.conditionEvent reference)
  have denominatorPositive : 0 < denominator.num := positive
  refine ⟨QProb.div numerator denominator denominatorPositive, ?_⟩
  change ProbabilityResult.Equivalent
    (ProbabilityResult.divide (some numerator) (some denominator))
    (some (QProb.div numerator denominator denominatorPositive))
  simp only [ProbabilityResult.divide, dif_pos denominatorPositive]
  exact .value (QProb.equiv_refl _)

/-- Observable action-and-condition overlap supplies recursive support of
an actual causal kernel, even when its outcome numerator is zero.
The returned rational witness is computed from this kernel's record rather
than selected from a propositional existence statement. -/
noncomputable def supportedAt_of_observational_overlap
    (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment)
    (overlap : ObservationalCylinderPositiveAt model
      (NodeSet.union kernel.action kernel.condition) reference) :
    (ProbabilityTerm.kernel kernel).SupportedAt model reference :=
  supportedAt_of_condition_positive model kernel reference
    (condition_positive_of_observational_overlap model kernel reference overlap)

end Kernel
end Causality
end Thesis
