import Thesis.Causality.BinaryEncoding
import Thesis.CausalTransport.Completeness

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# From a binary signal gap to full-alphabet positive countermodels

`ValueRefinement` supplies the actual private label sweep, its full-value
observational equality, full-alphabet positivity, and exact interventional
bit probabilities.  This one-way assembly module applies those theorems to
the original joint query.  It does not ask for positivity of the old full
label law: positive decoded atoms suffice.

The constructor retains the supplied observed signature and graph.  In
particular it never appends observed coordinates, enlarges a supplied value
domain, changes the action/outcome query, or uses a shared latent switch.
An unrestricted binary original-query hedge construction is still required
to discharge the general published completeness leaf.  The label sweep is
a general transport of such a construction, not a proof that it exists.
-/

namespace ObservedValueRefinement

/-- A local event may distinguish binary outcomes without distinguishing
the extra labels in their bit-zero fibres.  The empty-action branch uses
the actual observational law, as required by `InterventionalQuery.value`. -/
theorem refine_queryValue (rich : ObservedSignature.ValueRich S)
    (base : ExactModel S) (respects : RespectsParentBits base rich)
    (query : InterventionalQuery S) (event : Event (Fin S.count -> Bool))
    (factors : forall sample, query.event sample = event (bits rich sample)) :
    QProb.Equiv (query.value (refine rich base)) (query.value base) := by
  have same : query.event = fun sample => event (bits rich sample) := funext factors
  cases active : finAny S.count query.intervention.targets with
  | false =>
      simpa only [InterventionalQuery.value, InterventionalQuery.distribution, active,
        Bool.false_eq_true, if_false, FiniteLatentSCM.interventionalValue,
        FiniteLatentSCM.interventionalDist, FiniteLatentSCM.observationalDist,
        FiniteLatentSCM.eval, same] using
        refine_interventionalBitsValue rich base respects (FiniteLatentSCM.noIntervention S) event
  | true =>
      simpa only [InterventionalQuery.value, InterventionalQuery.distribution, active,
        if_true, FiniteLatentSCM.interventionalValue, same] using
        refine_interventionalBitsValue rich base respects query.intervention.value event

/-- Construct both final models before proving separation.  All model-class
fields concern these same two full-alphabet SCMs, and the result concerns
the original event query's complete outcome kernel, not merely a surrogate
root parity distribution.

The semantic gap and the decoded-support assumptions are obligations of the
binary core.  This adapter discharges label positivity and transports that
gap; it must not be used to hide a missing general countermodel argument. -/
noncomputable def positiveCounterexampleOfBitEvent
    (rich : ObservedSignature.ValueRich S) {graph : ObservedGraph S}
    (query : InterventionalQuery S) (left right : ExactModel S)
    (leftCompatible : Compatible left graph) (rightCompatible : Compatible right graph)
    (leftRespects : RespectsParentBits left rich) (rightRespects : RespectsParentBits right rich)
    (leftPositive : BitsPositive left rich) (rightPositive : BitsPositive right rich)
    (equivalent : ObservationallyEquivalent left right)
    (event : Event (Fin S.count -> Bool))
    (factors : forall sample, query.event sample = event (bits rich sample))
    (separated : Not (QProb.Equiv (query.value left) (query.value right))) :
    CounterexampleIn (GraphModelClass.positive graph) query.kernelQuery where
  left := refine rich left
  right := refine rich right
  left_mem := ⟨refine_compatible rich left leftCompatible, refine_positive rich left leftRespects leftPositive⟩
  right_mem := ⟨refine_compatible rich right rightCompatible, refine_positive rich right rightRespects rightPositive⟩
  observationally_equal := refine_observationally_equivalent rich left right leftRespects rightRespects equivalent
  query_separated := query.not_kernelValueEquivalent_of_not_value _ _ (by
    intro finalEqual
    exact separated (QProb.equiv_trans
      (QProb.equiv_symm (refine_queryValue rich left leftRespects query event factors))
      (QProb.equiv_trans finalEqual (refine_queryValue rich right rightRespects query event factors))))

/-! ## Accepting ordinary Boolean-valued models directly -/

/-- Interpret the unchanged action and outcome node sets on the ordinary
binary signature.  Event locality is inherited through the explicit value
encoding, and an action's supplied label is decoded rather than discarded. -/
def binaryQuery (rich : ObservedSignature.ValueRich S) (query : InterventionalQuery S)
    (event : Event S.binary.Assignment)
    (factors : forall sample, query.event sample = event (bits (S := S) rich sample)) :
    InterventionalQuery S.binary where
  intervention := ⟨BinaryEncoding.intervention rich query.intervention.value⟩
  outcomeNodes := query.outcomeNodes
  action_outcome_disjoint := by
    intro node selected
    have targets :
        (BinaryEncoding.intervention rich query.intervention.value node).isSome =
          (query.intervention.value node).isSome := by
      unfold BinaryEncoding.intervention
      cases query.intervention.value node <;> rfl
    exact query.action_outcome_disjoint node (targets.symm.trans selected)
  event := event
  event_local := by
    intro first second agree
    have encoded : AssignmentsAgreeOn query.outcomeNodes
        (BinaryEncoding.assignment rich first) (BinaryEncoding.assignment rich second) := by
      intro node selected
      exact congrArg (BinaryEncoding.value rich node) (agree node selected)
    have equal := query.event_local _ _ encoded
    have firstFactor := factors (BinaryEncoding.assignment rich first)
    have secondFactor := factors (BinaryEncoding.assignment rich second)
    rw [BinaryEncoding.bits_assignment] at firstFactor secondFactor
    exact firstFactor.symm.trans (equal.trans secondFactor)

/-- Deterministic encoding preserves the original event-query value exactly.
The binary query uses the same indices, not an enlarged graphical problem. -/
theorem encoded_binaryQueryValue (rich : ObservedSignature.ValueRich S)
    (base : ExactModel S.binary) (query : InterventionalQuery S)
    (event : Event S.binary.Assignment)
    (factors : forall sample, query.event sample = event (bits (S := S) rich sample)) :
    QProb.Equiv (query.value (BinaryEncoding.model rich base))
      ((binaryQuery rich query event factors).value base) := by
  have targetSets : (binaryQuery rich query event factors).intervention.targets = query.intervention.targets := by
    funext node
    cases selected : query.intervention.value node <;>
      simp only [binaryQuery, HardIntervention.targets, BinaryEncoding.intervention,
        selected, Option.map_none, Option.map_some, Option.isSome]
  have same : query.event = fun sample => event (bits (S := S) rich sample) := funext factors
  have sameActive : finAny S.binary.count (binaryQuery rich query event factors).intervention.targets =
      finAny S.count query.intervention.targets := congrArg (finAny S.count) targetSets
  simp only [InterventionalQuery.value, InterventionalQuery.distribution]
  rw [sameActive]
  cases active : finAny S.count query.intervention.targets with
  | false =>
      simp only [Bool.false_eq_true, if_false, same]
      change QProb.Equiv
        ((BinaryEncoding.model rich base).observationalValue (fun sample => event (bits (S := S) rich sample)))
        (base.observationalValue event)
      exact QProb.equiv_trans (BinaryEncoding.observationalValue rich base _)
        (base.observationalDist.probVal_congr _ event (fun sample =>
          congrArg event (BinaryEncoding.bits_assignment rich sample)))
  | true =>
      simp only [if_true, same]
      change QProb.Equiv
        ((BinaryEncoding.model rich base).interventionalValue query.intervention.value
          (fun sample => event (bits (S := S) rich sample)))
        (base.interventionalValue (BinaryEncoding.intervention rich query.intervention.value) event)
      exact BinaryEncoding.interventionalBitsValue rich base query.intervention.value event

/-- General full-alphabet countermodel transport from ordinary positive
binary SCMs.  Parent-bit irrelevance and decoded support are proved by
encoding, not supplied by the caller.  The private refinement then proves
positivity at *every* original label and preserves the original causal gap.

This is the precise reduction used by a future unrestricted binary hedge
argument.  It retains the general finite-alphabet target rather than replacing
it with a binary-only completeness theorem. -/
noncomputable def positiveCounterexampleOfBinaryEvent
    (rich : ObservedSignature.ValueRich S) {graph : ObservedGraph S}
    (query : InterventionalQuery S) (left right : ExactModel S.binary)
    (leftCompatible : Compatible left graph.binary) (rightCompatible : Compatible right graph.binary)
    (leftPositive : ObservationallyPositive left) (rightPositive : ObservationallyPositive right)
    (equivalent : ObservationallyEquivalent left right)
    (event : Event S.binary.Assignment)
    (factors : forall sample, query.event sample = event (bits (S := S) rich sample))
    (separated : Not (QProb.Equiv ((binaryQuery rich query event factors).value left)
      ((binaryQuery rich query event factors).value right))) :
    CounterexampleIn (GraphModelClass.positive graph) query.kernelQuery :=
  positiveCounterexampleOfBitEvent rich query (BinaryEncoding.model rich left) (BinaryEncoding.model rich right)
    (BinaryEncoding.compatible rich left leftCompatible) (BinaryEncoding.compatible rich right rightCompatible)
    (BinaryEncoding.respectsParentBits rich left) (BinaryEncoding.respectsParentBits rich right)
    (BinaryEncoding.bitsPositive rich left leftPositive) (BinaryEncoding.bitsPositive rich right rightPositive)
    (BinaryEncoding.observationally_equivalent rich left right equivalent) event factors (by
      intro encodedEqual
      exact separated (QProb.equiv_trans
        (QProb.equiv_symm (encoded_binaryQueryValue rich left query event factors))
        (QProb.equiv_trans encodedEqual (encoded_binaryQueryValue rich right query event factors))))

end ObservedValueRefinement
end Causality
end Thesis
