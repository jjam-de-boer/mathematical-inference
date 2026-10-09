import Thesis.CausalTransport.HedgeChannelProjection
import Thesis.Probability.FiniteBooleanTranslation

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Actual channel marginals balanced by an outcome-flow direction

The complete interventional right-minus-left likelihood is the permitted
full-small sum.  A conditioning marginal agrees only after that whole sum
has been proved zero on every conditioning event.  Individual zero cells,
the numerator's positive character, or observational equality do not supply
such a proof.

Here an explicitly supplied Boolean direction leaves the original action
and the inspected conditioning coordinates fixed.  Its routed small phase
is odd, while every outside-small row has even local source.  Thus every
permitted background mask is even in the same direction.  Translating an
assignment by that direction reverses every actual full-small integrand:
the forced-row coefficient is unchanged, the entire prior mass is retained,
and only the character sign changes.  The explicit involution permutes the
actual filtered signature enumeration, so each complete term sums to zero.
Interchanging the two finite sums then proves equality of the actual event
numerators and hence of the installed models' conditioning probabilities.

The direction is finite Type-level data, not a semantic marginal-equality
assumption.  A small-flow sink omitted by the conditioner supplies one
automatically by flipping its single coordinate.  More general directions
may flip whole routing paths.  Existence of a suitable direction is not
asserted for every irreducible conditional terminal; terminals requiring a
different channel signal or another normalization argument remain separate.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-- A concrete sign-reversing direction for the installed outcome-flow
pair and a selected conditioning marginal.  The first two fields protect
the actual intervention and event; the last two concern local routed bits,
not assumed equality or separation of any model probabilities. -/
structure OutcomeFlowBalanceDirection (w : HedgeWitness G q) (nodes : NodeSet S) where
  bits : S.binary.Assignment
  action_fixed : forall child, q.action child = true -> bits child = false
  inspected_fixed : forall child, nodes child = true -> bits child = false
  small_odd : signalPhase w.small (outcomeFlowSignal w) bits = true
  outside_even : forall child, w.small child = false ->
    hedgeRoutingLocalSource w.smallOutcomeFlowSuccessor bits child = false

namespace OutcomeFlowBalanceDirection

/-- Every permitted outside-small background phase is even in the supplied
direction.  This is derived row by row; a separate semantic cancellation
premise for every background mask is unnecessary. -/
theorem background_even {w : HedgeWitness G q} {nodes : NodeSet S}
    (direction : OutcomeFlowBalanceDirection w nodes)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) :
    signalPhase mask (outcomeFlowSignal w) direction.bits = false := by
  rw [outcomeFlowSignal, routingPhase_eq_localSource w.smallOutcomeFlowNodes mask
    w.smallOutcomeFlowSuccessor w.smallOutcomeFlowSuccessor_wellFormed]
  unfold hedgeNodeXor
  have folded := foldl_congr_of_mem
    (fun total child => Bool.xor total (hedgeRoutingLocalSource w.smallOutcomeFlowSuccessor direction.bits child))
    (fun total _child => total) false (NodeSet.members mask)
  refine (folded ?_).trans (foldl_unchanged _ false _ (fun _ _ => rfl))
  intro total child listed
  have selected := (NodeSet.mem_members_iff mask child).mp listed
  have outsideSmall : Bool.not (w.small child) = true := by
    simpa only [outside, NodeSet.diff, NodeSet.full, Bool.true_and] using subset child selected
  have off : w.small child = false := by
    cases inside : w.small child with
    | false => rfl
    | true => rw [inside] at outsideSmall; cases outsideSmall
  rw [direction.outside_even child off, Bool.xor_false]

/-- Translation fixes every coordinate read by a local conditioning
event, so it preserves that actual event on all assignments. -/
theorem event_preserved {w : HedgeWitness G q} {nodes : NodeSet S}
    (direction : OutcomeFlowBalanceDirection w nodes)
    (event : Event S.binary.Assignment) (localEvent : EventDependsOnlyOn (S := S.binary) nodes event)
    (sample : S.binary.Assignment) :
    event (FiniteProduct.xorAssignment S.count sample direction.bits) = event sample := by
  apply localEvent
  intro child selected
  simp only [FiniteProduct.xorAssignment, direction.inspected_fixed child selected, Bool.xor_false]

/-- The complete forced-row coefficient is unchanged by translation,
including on conflicting cells.  Every forced row is an original action
row; no other intervention or consistent-sample restriction is substituted. -/
theorem coefficient_preserved {w : HedgeWitness G q} {nodes : NodeSet S}
    (direction : OutcomeFlowBalanceDirection w nodes) (target : Fin S.count -> Option Bool)
    (targets : forall child, (target child).isSome = q.action child)
    (sample : S.binary.Assignment) (choice : Fin S.count -> Option (Fin (channelCount w))) :
    HedgeChannelTable.choiceCoefficient (rightTables w) target
      (FiniteProduct.xorAssignment S.count sample direction.bits) choice =
        HedgeChannelTable.choiceCoefficient (rightTables w) target sample choice := by
  apply HedgeChannelTable.choiceCoefficient_congr_on_forced
  intro child fixed forced
  have selected : q.action child = true := (targets child).symm.trans (by rw [forced]; rfl)
  simp only [FiniteProduct.xorAssignment, direction.action_fixed child selected, Bool.xor_false]

/-- The complete routed character of every legal full-small choice changes
sign under the same supplied translation.  Its pointwise sign before the
translation is unrestricted; both signs and zero coefficients are retained. -/
theorem character_reversed {w : HedgeWitness G q} {nodes : NodeSet S}
    (direction : OutcomeFlowBalanceDirection w nodes)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) (sample : S.binary.Assignment) :
    FiniteProbRecord.characterSign
        (Bool.xor (signalPhase w.small (outcomeFlowSignal w)
          (FiniteProduct.xorAssignment S.count sample direction.bits))
          (signalPhase mask (outcomeFlowSignal w)
            (FiniteProduct.xorAssignment S.count sample direction.bits))) =
      -(FiniteProbRecord.characterSign (Bool.xor (signalPhase w.small (outcomeFlowSignal w) sample)
        (signalPhase mask (outcomeFlowSignal w) sample))) := by
  have smallShift := routingPhase_xor w.smallOutcomeFlowNodes w.small w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed sample direction.bits
  have maskShift := routingPhase_xor w.smallOutcomeFlowNodes mask w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed sample direction.bits
  change signalPhase w.small (outcomeFlowSignal w) _ =
    Bool.xor (signalPhase w.small (outcomeFlowSignal w) sample)
      (signalPhase w.small (outcomeFlowSignal w) direction.bits) at smallShift
  change signalPhase mask (outcomeFlowSignal w) _ =
    Bool.xor (signalPhase mask (outcomeFlowSignal w) sample)
      (signalPhase mask (outcomeFlowSignal w) direction.bits) at maskShift
  rw [smallShift, maskShift, direction.small_odd, direction.background_even mask subset]
  cases signalPhase w.small (outcomeFlowSignal w) sample <;>
    cases signalPhase mask (outcomeFlowSignal w) sample <;> rfl

/-- Sign reversal of the actual complete monomial integral, not merely its
abstract character.  The full shared-prior mass and each forced-row
indicator are the same on both sides of the explicit translation. -/
theorem fullSmallTerm_reversed {w : HedgeWitness G q} {nodes : NodeSet S}
    (direction : OutcomeFlowBalanceDirection w nodes) (target : Fin S.count -> Option Bool)
    (targets : forall child, (target child).isSome = q.action child)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) (sample : S.binary.Assignment) :
    rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w) target
      (FiniteProduct.xorAssignment S.count sample direction.bits) (fullChoice w w.small (smallChannel w) mask) =
        -(rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w) target sample
          (fullChoice w w.small (smallChannel w) mask)) := by
  rw [right_fullTermIntegral_under w _ _ _ _ mask subset,
    right_fullTermIntegral_under w _ _ _ sample mask subset,
    direction.coefficient_preserved target targets sample,
    direction.character_reversed mask subset sample, Int.mul_neg]

/-- Each complete full-small contribution to every local conditioning
event is zero.  The actual filtered signature enumeration is permuted by
the displayed involution; no shortened or duplicated support is used. -/
theorem projectedFullSmallTerm_zero {w : HedgeWitness G q} {nodes : NodeSet S}
    (direction : OutcomeFlowBalanceDirection w nodes) (target : Fin S.count -> Option Bool)
    (targets : forall child, (target child).isSome = q.action child)
    (event : Event S.binary.Assignment) (localEvent : EventDependsOnlyOn (S := S.binary) nodes event)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) :
    ((S.binary.assignmentEnumeration.filter event).map (fun sample =>
      rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w) target sample
        (fullChoice w w.small (smallChannel w) mask))).sum = 0 :=
  FiniteProduct.filtered_sum_zero_of_xor S.count S.binary.assignmentEnumeration
    S.binary.assignmentEnumeration_nodup S.binary.assignmentEnumeration_complete direction.bits event
    (direction.event_preserved event localEvent) _
    (fun sample _selected => direction.fullSmallTerm_reversed target targets mask subset sample)

/-! ## Equality of the actual complete conditioning marginal -/

/-- Sum every actual allowed full-small choice before concluding that the
complete right-minus-left event numerator is zero.  The interchange keeps
both finite supports intact; every canonical choice is recovered from its
actual outside-small mask, not replaced by a proposed simplified support. -/
theorem eventNumerators_equal {w : HedgeWitness G q} {nodes : NodeSet S}
    (direction : OutcomeFlowBalanceDirection w nodes) (rich : ObservedSignature.ValueRich S)
    (target : Fin S.count -> Option Bool) (targets : forall child, (target child).isSome = q.action child)
    (event : Event S.binary.Assignment) (localEvent : EventDependsOnlyOn (S := S.binary) nodes event) :
    HedgeChannelTable.eventNumerator G (channelCount w) (leftTables w)
      (leftSignals w rich (outcomeFlowSignal w) (outcomeFlowSignal w)) target event =
    HedgeChannelTable.eventNumerator G (channelCount w) (rightTables w)
      (rightSignals w (outcomeFlowSignal w) (outcomeFlowSignal w)) target event := by
  let projected := fun choice : Fin S.count -> Option (Fin (channelCount w)) =>
    ((S.binary.assignmentEnumeration.filter event).map (fun sample =>
      rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w) target sample choice)).sum
  have eachZero : forall choice, choice ∈ rightFullChoicesUnder w target -> projected choice = 0 := by
    intro choice listed
    rcases List.mem_map.mp (List.mem_filter.mp listed).1 with ⟨mask, member, same⟩
    rw [← same]
    exact direction.projectedFullSmallTerm_zero target targets event localEvent mask
      ((masks_member_iff _ _).mp member)
  have completeZero := FiniteSupportedSum.sum_eq_zero (rightFullChoicesUnder w target) projected eachZero
  have swapped := FiniteSupportedSum.sum_swap (S.binary.assignmentEnumeration.filter event)
    (rightFullChoicesUnder w target)
    (fun sample choice => rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w) target sample choice)
  cases forced : target w.actionSeed with
  | none =>
      have impossible := targets w.actionSeed
      rw [forced, w.actionSeed_in_action] at impossible
      cases impossible
  | some fixed =>
      have difference := eventNumerators_difference_of_action w rich (outcomeFlowSignal w) (outcomeFlowSignal w)
        target fixed forced event
      rw [swapped] at difference
      change _ = _ + ((rightFullChoicesUnder w target).map projected).sum at difference
      rw [completeZero, Int.add_zero] at difference
      exact Int.ofNat_inj.mp difference.symm

/-- Equality of every actual local conditioning event in the installed
Boolean models, under every supplied full-original-action intervention.
The denominator bridge cancels only the common positive literal likelihood
denominator after the complete numerator equality has been proved. -/
theorem models_interventionalMarginals_equivalent {w : HedgeWitness G q} {nodes : NodeSet S}
    (direction : OutcomeFlowBalanceDirection w nodes) (rich : ObservedSignature.ValueRich S)
    (target : Fin S.count -> Option Bool) (targets : forall child, (target child).isSome = q.action child)
    (event : Event S.binary.Assignment) (localEvent : EventDependsOnlyOn (S := S.binary) nodes event) :
    QProb.Equiv
      ((leftModel w rich (outcomeFlowSignal w) (outcomeFlowSignal w)).interventionalValue target event)
      ((rightModel w (outcomeFlowSignal w) (outcomeFlowSignal w)).interventionalValue target event) :=
  (HedgeChannelTable.model_interventional_event_equiv_iff G (channelCount w) (leftTables w) (rightTables w)
    (leftSignals w rich (outcomeFlowSignal w) (outcomeFlowSignal w))
    (rightSignals w (outcomeFlowSignal w) (outcomeFlowSignal w)) (capacities_equal w) target event).mpr
      (direction.eventNumerators_equal rich target targets event localEvent)

/-- If the conditioner contains every actual outcome-flow sink, no
direction of this family exists.  Flow conservation makes its sink parity
equal to its odd small phase, because all outside-small sources are even.
But the direction fixes every inspected sink, making that same parity zero.
This is a general structural obstruction, not an exhausted finite search or
a claim that the conditional query itself is identifiable. -/
theorem impossible_of_inspected_contains_sinks {w : HedgeWitness G q} {nodes : NodeSet S}
    (direction : OutcomeFlowBalanceDirection w nodes)
    (containsSinks : NodeSet.Subset (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor) nodes) :
    False := by
  have conserved := outcomeFlow_phase_eq_sinkParity w direction.bits
  change Bool.xor (signalPhase w.small (outcomeFlowSignal w) direction.bits)
    (signalPhase (outcomeFlowBackground w) (outcomeFlowSignal w) direction.bits) = _ at conserved
  rw [direction.small_odd, direction.background_even (outcomeFlowBackground w)
    (outcomeFlowBackground_subset_outside w)] at conserved
  have sinkZero : hedgeNodeXor (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor)
      direction.bits = false := by
    unfold hedgeNodeXor
    have folded := foldl_congr_of_mem (fun total child => Bool.xor total (direction.bits child))
      (fun total _child => total) false
      (NodeSet.members (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor))
    refine (folded ?_).trans (foldl_unchanged _ false _ (fun _ _ => rfl))
    intro total child listed
    rw [direction.inspected_fixed child (containsSinks child ((NodeSet.mem_members_iff _ child).mp listed)),
      Bool.xor_false]
  have impossible := conserved.trans sinkZero
  cases impossible

/-- No balance direction can be selected when the entire flow boundary is
inspected.  Elimination of the supplied nonempty proposition is used only
to prove contradiction, never to choose Type-level data. -/
theorem not_nonempty_of_inspected_contains_sinks (w : HedgeWitness G q) (nodes : NodeSet S)
    (containsSinks : NodeSet.Subset (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor) nodes) :
    ¬ Nonempty (OutcomeFlowBalanceDirection w nodes) := by
  intro supplied
  rcases supplied with ⟨direction⟩
  exact direction.impossible_of_inspected_contains_sinks containsSinks

/-! ## A free small-flow sink supplies a direction without further search -/

private theorem localSource_singleSink (successor : ForestChild S) (balance : Fin S.count)
    (unused : successor balance = none) (child : Fin S.count) :
    hedgeRoutingLocalSource successor (fun node => decide (node = balance)) child = decide (child = balance) := by
  have incoming : hedgeRoutingIncomingBits successor (fun node => decide (node = balance)) child = false := by
    unfold hedgeRoutingIncomingBits
    apply foldl_unchanged
    intro total parent
    by_cases routed : successor parent = some child
    · have different : parent ≠ balance := by
        intro same
        subst parent
        rw [unused] at routed
        cases routed
      simp only [hedgeRoutingParentEntry, routed, if_true, decide_eq_false different, Bool.xor_false]
    · simp only [hedgeRoutingParentEntry, routed, if_false, Bool.xor_false]
  change Bool.xor (decide (child = balance)) _ = _
  rw [incoming, Bool.xor_false]

private theorem indicator_fixed (nodes : NodeSet S) (balance : Fin S.count)
    (off : nodes balance = false) (child : Fin S.count) (selected : nodes child = true) :
    decide (child = balance) = false := by
  apply decide_eq_false
  intro same
  subst child
  rw [off] at selected
  cases selected

/-- Flip an omitted small-flow sink.  The action and conditioner do not
inspect it, and its absent outgoing flow ensures no other routed row reads
the flipped coordinate.  Membership in the small forest supplies the sole
odd selected source.  No route-avoidance test, semantic marginal premise,
or choice of another model is required by this constructor. -/
def ofSmallSink (w : HedgeWitness G q) (nodes : NodeSet S) (balance : Fin S.count)
    (inside : w.small balance = true) (unused : w.smallOutcomeFlowSuccessor balance = none)
    (omitted : nodes balance = false) : OutcomeFlowBalanceDirection w nodes where
  bits := fun child => decide (child = balance)
  action_fixed := indicator_fixed q.action balance (w.small_avoids_intervention balance inside)
  inspected_fixed := indicator_fixed nodes balance omitted
  small_odd := by
    have source : @hedgeRoutingLocalSource S w.smallOutcomeFlowSuccessor
        (fun child => decide (child = balance)) = (fun child => decide (child = balance)) :=
      funext (localSource_singleSink w.smallOutcomeFlowSuccessor balance unused)
    exact (routingPhase_eq_localSource w.smallOutcomeFlowNodes w.small w.smallOutcomeFlowSuccessor
      w.smallOutcomeFlowSuccessor_wellFormed _).trans
      ((congrArg (hedgeNodeXor w.small) source).trans
        (foldl_xor_indicator_of_mem_nodup (NodeSet.members w.small) balance
          ((NodeSet.mem_members_iff w.small balance).mpr inside) (NodeSet.nodup_members w.small)))
  outside_even := by
    intro child off
    refine (@localSource_singleSink S w.smallOutcomeFlowSuccessor balance unused child).trans ?_
    apply decide_eq_false
    intro same
    subst child
    rw [inside] at off
    cases off

end OutcomeFlowBalanceDirection

end HedgeChannelInstallation
end Causality
end Thesis
