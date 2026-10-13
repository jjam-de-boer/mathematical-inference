import Thesis.Causality.ObservationalSupport
import Thesis.Causality.ConditionalIdentificationKernel

namespace Thesis
namespace Causality

open Probability

/-!
# Actual conditioning support under promotion and later interventions

Positive mass of a conditioner under one intervention is enough to support
the remaining conditioner after additionally fixing the promoted block to
its reference values.  Every latent unit in the original conditioner event
already has those values.  SCM composition therefore leaves that unit's
complete assignment unchanged, and finite event-mass monotonicity preserves
positive mass in the new conditioning event.

This is a one-model support theorem, not rule-2 equality and not support
transfer between observationally equal models.  No graph separation,
observational overlap, global positivity or chosen latent unit is used.
The outcome may have mass zero, and the promoted block may have any finite
size.  The converse is false in general: forcing an impossible observed
conditioner can create support that was absent before promotion.

A second intrinsic preservation theorem handles the later outside-component
actions used by ID.  Interventions agreeing before a topological boundary
produce exactly the same earlier coordinates, for each fixed latent unit.
Consequently adding actions after every conditioned coordinate preserves
the conditioner's probability, not merely its positivity.  These support
facts need neither do-calculus soundness nor factual action overlap.
-/

namespace FiniteLatentSCM

/-- Evaluation of an earlier node reads only earlier intervention entries.
This is direct finite SCM recursion, independent of graph separation and
probability support.  Later action values may have zero factual probability. -/
theorem evalNodeUnder_eq_of_agree_before (model : FiniteLatentSCM S)
    (first second : (node : Fin S.count) → Option (S.Value node))
    (unit : model.latent.Assignment) (boundary : Nat)
    (agree : forall node, node.val < boundary → first node = second node)
    (child : Fin S.count) (before : child.val < boundary) :
    model.evalNodeUnder first unit child = model.evalNodeUnder second unit child := by
  rw [evalNodeUnder, evalNodeUnder]
  unfold equationUnder
  rw [agree child before]
  cases second child with
  | some _value => rfl
  | none =>
      congr 1
      funext parent edge
      exact model.evalNodeUnder_eq_of_agree_before first second unit boundary agree parent
        (Nat.lt_trans (S.directed_earlier edge) before)
termination_by child.val
decreasing_by exact S.directed_earlier edge

/-- Assignment-level reading of the same intrinsic prefix-preservation law.
No equality of complete intervened assignments is asserted: later outcomes
may change, but they are irrelevant to the earlier conditioning cylinder. -/
theorem evalUnder_eq_of_agree_before (model : FiniteLatentSCM S)
    (first second : (node : Fin S.count) → Option (S.Value node))
    (unit : model.latent.Assignment) (boundary : Nat)
    (agree : forall node, node.val < boundary → first node = second node)
    (child : Fin S.count) (before : child.val < boundary) :
    model.evalUnder first unit child = model.evalUnder second unit child :=
  model.evalNodeUnder_eq_of_agree_before first second unit boundary agree child before

end FiniteLatentSCM

namespace Kernel

/-- Adding only later actions preserves the actual conditioner probability.
Both kernels are interpreted in the same finite SCM and at the same latent
prior.  Equality is proved unitwise before probabilities are compared, so
there is no assumption of observational positivity or action admissibility. -/
theorem condition_probability_add_later_actions
    (model : FiniteLatentSCM S) (action outcome later condition : NodeSet S)
    (reference : S.Assignment) (boundary : Nat)
    (earlier : forall node, condition node = true → node.val < boundary)
    (after : forall node, later node = true → boundary ≤ node.val) :
    QProb.Equiv
      ((distribution model ⟨outcome, action, condition⟩ reference).probVal
        (conditionEvent ⟨outcome, action, condition⟩ reference))
      ((distribution model ⟨outcome, NodeSet.union action later, condition⟩ reference).probVal
        (conditionEvent ⟨outcome, NodeSet.union action later, condition⟩ reference)) := by
  let original : Kernel S := ⟨outcome, action, condition⟩
  let updated : Kernel S := ⟨outcome, NodeSet.union action later, condition⟩
  have agree : forall node, node.val < boundary →
      original.intervention reference node = updated.intervention reference node := by
    intro node before
    have notLater : later node = false := by
      cases selected : later node with
      | false => rfl
      | true => exact False.elim (Nat.not_lt_of_ge (after node selected) before)
    simp only [original, updated, intervention, NodeSet.union, notLater, Bool.or_false]
  have events : forall unit,
      original.conditionEvent reference (model.evalUnder (original.intervention reference) unit) =
      updated.conditionEvent reference (model.evalUnder (updated.intervention reference) unit) := by
    intro unit
    apply agreesOn_sample_congr condition reference
    intro node selected
    exact model.evalUnder_eq_of_agree_before _ _ unit boundary agree node (earlier node selected)
  exact QProb.equiv_trans (distribution_probVal model original reference (original.conditionEvent reference))
    (QProb.equiv_trans (model.prior.probVal_congr _ _ events)
      (QProb.equiv_symm (distribution_probVal model updated reference (updated.conditionEvent reference))))

/-- Construct support after adding later actions from the original supported
conditioner.  The outcome may be zero, and the later action values need not
occur observationally.  Only their topological position is relevant. -/
noncomputable def supportedAt_addLaterActions
    (model : FiniteLatentSCM S) (action outcome later condition : NodeSet S)
    (reference : S.Assignment) (boundary : Nat)
    (earlier : forall node, condition node = true → node.val < boundary)
    (after : forall node, later node = true → boundary ≤ node.val)
    (supported : (ProbabilityTerm.kernel ⟨outcome, action, condition⟩).SupportedAt model reference) :
    (ProbabilityTerm.kernel ⟨outcome, NodeSet.union action later, condition⟩).SupportedAt model reference :=
  supportedAt_of_condition_positive model _ reference
    ((QProb.equiv_num_pos_iff (condition_probability_add_later_actions model action outcome later condition
      reference boundary earlier after)).mp (conditionPositive_of_supportedAt model _ reference supported))

/-- Promoting an already supported conditioner cannot destroy support of
the remaining given-set.  The proof compares events on the same finite prior
and constructs the new conditional from its actual positive denominator. -/
noncomputable def supportedAt_promoteCondition
    (model : FiniteLatentSCM S) (action outcome promoted condition : NodeSet S)
    (reference : S.Assignment)
    (supported : (ProbabilityTerm.kernel
      ⟨outcome, action, NodeSet.union promoted condition⟩).SupportedAt model reference) :
    (ProbabilityTerm.kernel ⟨outcome, NodeSet.union action promoted, condition⟩).SupportedAt model reference := by
  let original : Kernel S := ⟨outcome, action, NodeSet.union promoted condition⟩
  let updated : Kernel S := ⟨outcome, NodeSet.union action promoted, condition⟩
  let originalEvent : Event model.latent.Assignment := fun unit =>
    original.conditionEvent reference (model.evalUnder (original.intervention reference) unit)
  let updatedEvent : Event model.latent.Assignment := fun unit =>
    updated.conditionEvent reference (model.evalUnder (updated.intervention reference) unit)
  have included : forall unit, originalEvent unit = true → updatedEvent unit = true := by
    intro unit selected
    have both : (agreesOn promoted reference (model.evalUnder (original.intervention reference) unit) &&
        agreesOn condition reference (model.evalUnder (original.intervention reference) unit)) = true := by
      simpa only [originalEvent, original, conditionEvent, agreesOn_union] using selected
    have promotedAgreement := (Bool.and_eq_true_iff.mp both).1
    have remainingAgreement := (Bool.and_eq_true_iff.mp both).2
    have unchanged : model.evalUnder (updated.intervention reference) unit =
        model.evalUnder (original.intervention reference) unit := by
      apply model.evalUnder_composition
      · intro node notFixed
        cases wasFixed : action node with
        | false => simp only [original, intervention, wasFixed, Bool.false_eq_true, if_false]
        | true =>
            have forced : updated.intervention reference node = some (reference node) := by
              simp only [updated, intervention, NodeSet.union, wasFixed, Bool.true_or, if_true]
            rw [forced] at notFixed
            cases notFixed
      · intro node value fixed
        cases wasFixed : action node with
        | true =>
            have atReference : reference node = value := by
              simpa only [updated, intervention, NodeSet.union, wasFixed, Bool.true_or, if_true,
                Option.some.injEq] using fixed
            exact (model.evalUnder_effectiveness (original.intervention reference) unit node (reference node)
              (by simp only [original, intervention, wasFixed, if_true])).trans atReference
        | false =>
            cases nowFixed : promoted node with
            | false =>
                simp only [updated, intervention, NodeSet.union, wasFixed, nowFixed,
                  Bool.false_or, Bool.false_eq_true, if_false] at fixed
                cases fixed
            | true =>
                have component := (finAll_eq_true_iff _).mp promotedAgreement node
                have alreadyAtReference : model.evalUnder (original.intervention reference) unit node = reference node := by
                  apply of_decide_eq_true
                  simpa only [nowFixed, if_true] using component
                have atReference : reference node = value := by
                  simpa only [updated, intervention, NodeSet.union, wasFixed, nowFixed, Bool.false_or,
                    if_true, Option.some.injEq] using fixed
                exact alreadyAtReference.trans atReference
    change agreesOn condition reference (model.evalUnder (updated.intervention reference) unit) = true
    rw [unchanged]
    exact remainingAgreement
  have originalPositive := conditionPositive_of_supportedAt model original reference supported
  have priorPositive : 0 < (model.prior.probVal originalEvent).num :=
    (QProb.equiv_num_pos_iff (distribution_probVal model original reference (original.conditionEvent reference))).mp
      originalPositive
  have monotone := FiniteProbRecord.eventMass_mono model.prior.atoms originalEvent updatedEvent included
  have updatedPriorPositive : 0 < (model.prior.probVal updatedEvent).num :=
    Nat.lt_of_lt_of_le priorPositive monotone
  exact supportedAt_of_condition_positive model updated reference
    ((QProb.equiv_num_pos_iff (distribution_probVal model updated reference (updated.conditionEvent reference))).mpr
      updatedPriorPositive)

end Kernel

/-- IDC's actual singleton promotion is an instance of the block theorem.
The retained membership proof aligns the whole original conditioner with
the singleton and its complement; nonempty remaining conditioners are kept. -/
noncomputable def ConditionalKernelQuery.exchangeCondition_supportedAt
    (query : ConditionalKernelQuery S) (node : Fin S.count) (selected : query.condition node = true)
    (model : ExactModel S) (reference : S.Assignment)
    (supported : query.sourceTerm.SupportedAt model reference) :
    (query.exchangeCondition node selected).sourceTerm.SupportedAt model reference :=
  Kernel.supportedAt_promoteCondition model query.action query.outcome (NodeSet.singleton node)
    (NodeSet.diff query.condition (NodeSet.singleton node)) reference
    (by
      have partition := query.exchangeCondition_partition node selected
      change NodeSet.union (NodeSet.singleton node) (NodeSet.diff query.condition (NodeSet.singleton node)) =
        query.condition at partition
      rw [partition]
      exact supported)

end Causality
end Thesis
