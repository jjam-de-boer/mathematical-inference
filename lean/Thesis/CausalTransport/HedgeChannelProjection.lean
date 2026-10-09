import Thesis.CausalTransport.HedgeChannelUnderCoefficients
import Thesis.CausalTransport.HedgeChannelRouting
import Thesis.CausalTransport.HedgeChannelInterventional

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Actual full-small contributions to the original outcome event

Character nonnegativity alone is not an interventional probability theorem.
Here each character is multiplied by its actual complete row scalar and the
entire literal shared-prior mass.  A sample conflicting with the all-false
original action has coefficient zero.  Removing precisely those zero terms
turns the original outcome projection into the action/outcome false cylinder;
it does not change the event asked by the query.

On that restricted support the scalar is constant.  The previous routed
character theorem therefore proves a nonnegative complete contribution for
every outside-small background mask.  For the distinguished outcome-flow
mask, all selected character signs are one, the scalar is strictly positive,
and the explicitly supplied all-false assignment is listed.  Its complete
original-outcome contribution is consequently strictly positive.

Every sum is over the actual signature enumeration and every term is an
actual installed monomial integral.  No hidden source, full-cell event,
readiness premise or changed original outcome replaces those objects.
Summing the permitted terms gives a strictly positive actual original-event
numerator gap and, through the common literal denominator, inequivalent
interventional probabilities for the installed pair on every supplied hedge.
The full-alphabet lift and conditional countermodel assembly are separate.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## The original hard cut and exact projected term -/

/-- Force every original action coordinate to false, retaining every other
row.  This target is not narrowed to the stored action seed. -/
def falseActionTarget (action : NodeSet S) : Fin S.count -> Option Bool :=
  fun child => if action child then some false else none

/-- The homogeneous typed parent signal of the existing outcome flow. -/
def outcomeFlowSignal (w : HedgeWitness G q) : ParentSignal S :=
  routingParentSignal w.smallOutcomeFlowSuccessor

/-- Exact contribution of one full-small/background monomial to the
unchanged original all-false outcome event under the full original action. -/
def projectedSmallTerm (w : HedgeWitness G q) (mask : NodeSet S) : Int :=
  ((S.binary.assignmentEnumeration.filter (FiniteProduct.falseCylinder S.count q.outcome)).map
    (fun sample => rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w)
      (falseActionTarget q.action) sample (fullChoice w w.small (smallChannel w) mask))).sum

private theorem target_consistent (action : NodeSet S) (sample : S.binary.Assignment)
    (selected : FiniteProduct.falseCylinder S.count action sample = true) :
    forall child fixed, falseActionTarget action child = some fixed -> sample child = fixed := by
  intro child fixed forced
  cases inside : action child with
  | false =>
      simp only [falseActionTarget, inside, Bool.false_eq_true, if_false] at forced
      cases forced
  | true =>
      have fixedFalse : false = fixed := Option.some.inj (by
        simpa only [falseActionTarget, inside, if_true] using forced)
      rw [← fixedFalse]
      exact (FiniteProduct.falseCylinder_eq_true_iff S.count action sample).mp selected child inside

private theorem action_of_combined (sample : S.binary.Assignment)
    (selected : FiniteProduct.falseCylinder S.count (NodeSet.union q.action q.outcome) sample = true) :
    FiniteProduct.falseCylinder S.count q.action sample = true := by
  apply (FiniteProduct.falseCylinder_eq_true_iff _ _ _).mpr
  intro child inside
  apply (FiniteProduct.falseCylinder_eq_true_iff _ _ _).mp selected child
  simp only [NodeSet.union, inside, Bool.true_or]

private theorem outcome_of_combined (sample : S.binary.Assignment)
    (selected : FiniteProduct.falseCylinder S.count (NodeSet.union q.action q.outcome) sample = true) :
    FiniteProduct.falseCylinder S.count q.outcome sample = true := by
  apply (FiniteProduct.falseCylinder_eq_true_iff _ _ _).mpr
  intro child inside
  apply (FiniteProduct.falseCylinder_eq_true_iff _ _ _).mp selected child
  simp only [NodeSet.union, inside, Bool.or_true]

private theorem fullSmallTerm_zero_of_action_conflict (w : HedgeWitness G q)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) (sample : S.binary.Assignment)
    (conflict : FiniteProduct.falseCylinder S.count q.action sample = false) :
    rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w) (falseActionTarget q.action)
      sample (fullChoice w w.small (smallChannel w) mask) = 0 := by
  rcases FiniteProduct.falseCylinder_conflict_of_false S.count q.action sample conflict with
    ⟨child, forced, value⟩
  have target : falseActionTarget q.action child = some false := by
    simp only [falseActionTarget, forced, if_true]
  have different : sample child ≠ false := by
    intro equal
    exact Bool.false_ne_true (equal.symm.trans value)
  rw [right_fullTermIntegral_under w _ _ _ sample mask subset,
    HedgeChannelTable.choiceCoefficient_zero_of_conflict (rightTables w) _ sample _ child false target different,
    Int.mul_zero, Int.zero_mul]

/-! ## The actual scalar times the complete routed-character projection -/

/-- Removing only conflicting zero cells and factoring the consistent
scalar gives the actual projected monomial, including its complete shared
prior mass.  The original outcome event has not been enlarged; the extra
action test here is justified solely by zero likelihood at conflicts. -/
theorem projectedSmallTerm_eq_weightedCharacterSum (w : HedgeWitness G q)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) :
    projectedSmallTerm w mask =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        (HedgeChannelTable.choiceScalarUnder (rightTables w) (falseActionTarget q.action)
          (fullChoice w w.small (smallChannel w) mask) : Int) *
        ((S.binary.assignmentEnumeration.filter
          (FiniteProduct.falseCylinder S.count (NodeSet.union q.action q.outcome))).map
          (fun sample => FiniteProbRecord.characterSign
            (Bool.xor (signalPhase w.small (outcomeFlowSignal w) sample)
              (signalPhase mask (outcomeFlowSignal w) sample)))).sum := by
  let term := fun sample : S.binary.Assignment =>
    rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w) (falseActionTarget q.action)
      sample (fullChoice w w.small (smallChannel w) mask)
  have restrict := FiniteSupportedSum.sum_eq_filter_of_zero
    (S.binary.assignmentEnumeration.filter (FiniteProduct.falseCylinder S.count q.outcome))
    (FiniteProduct.falseCylinder S.count q.action) term
    (fun sample _listed conflict => fullSmallTerm_zero_of_action_conflict w mask subset sample conflict)
  have eventEqual : (fun sample : S.binary.Assignment =>
      FiniteProduct.falseCylinder S.count q.action sample &&
        FiniteProduct.falseCylinder S.count q.outcome sample) =
      FiniteProduct.falseCylinder S.count (NodeSet.union q.action q.outcome) := by
    funext sample
    exact (FiniteProduct.falseCylinder_union S.count q.action q.outcome sample).symm
  rw [List.filter_filter] at restrict
  have restricted := restrict.trans (congrArg (fun event : S.binary.Assignment -> Bool =>
    ((S.binary.assignmentEnumeration.filter event).map term).sum) eventEqual)
  have rows := List.map_congr_left
    (l := S.binary.assignmentEnumeration.filter
      (FiniteProduct.falseCylinder S.count (NodeSet.union q.action q.outcome)))
    (fun sample listed => (right_fullTermIntegral_under w _ _ _ sample mask subset).trans
      (congrArg (fun coefficient : Int =>
        ((PairRootChannels.prior G.binary (channelCount w)).den : Int) * coefficient *
          FiniteProbRecord.characterSign
            (Bool.xor (signalPhase w.small (outcomeFlowSignal w) sample)
              (signalPhase mask (outcomeFlowSignal w) sample)))
        (HedgeChannelTable.choiceCoefficient_eq_scalar_of_consistent (rightTables w) _ sample _
          (target_consistent q.action sample (action_of_combined sample (List.mem_filter.mp listed).2)))))
  exact restricted.trans ((congrArg List.sum rows).trans (FiniteSupportedSum.sum_mul_left _ _ _))

/-- Every legal outside-small term has a nonnegative complete actual
original-outcome contribution.  Its pointwise sign need not be nonnegative;
the complete character sum and the literal natural scalar supply the proof. -/
theorem projectedSmallTerm_nonneg (w : HedgeWitness G q)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) : 0 <= projectedSmallTerm w mask := by
  rw [projectedSmallTerm_eq_weightedCharacterSum w mask subset]
  exact Int.mul_nonneg
    (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
    (smallBackground_characterSum_nonneg w mask subset)

/-! ## An explicitly listed strictly positive distinguished contribution -/

/-- The full-small choice is permitted when its selected backgrounds avoid
the original action.  Small-forest avoidance is already certified by the
hedge; no seed-only or composite-action readiness restriction is introduced. -/
theorem fullSmallChoice_allowed_of_avoids_action (w : HedgeWitness G q) (mask : NodeSet S)
    (avoids : forall child, mask child = true -> q.action child = false) :
    HedgeChannelTable.choiceAllowedUnder (falseActionTarget q.action)
      (fullChoice w w.small (smallChannel w) mask) = true := by
  apply List.all_eq_true.mpr
  intro child _listed
  cases forced : q.action child with
  | false => simp only [falseActionTarget, forced, Bool.false_eq_true, if_false]
  | true =>
      have smallOff : w.small child = false := by
        cases inside : w.small child with
        | false => rfl
        | true => exact False.elim (Bool.false_ne_true ((w.small_avoids_intervention child inside).symm.trans forced))
      have maskOff : mask child = false := by
        cases selected : mask child with
        | false => rfl
        | true => exact False.elim (Bool.false_ne_true ((avoids child selected).symm.trans forced))
      simp only [falseActionTarget, forced, if_true, fullChoice, smallOff, Bool.false_eq_true, if_false,
        backgroundChoice, maskOff]
      rfl

/-- The distinguished original-outcome term has a strictly positive
complete actual contribution.  The all-false assignment is supplied directly
as its positive listed point; no countermodel witness or positive cell is
chosen from an existential claim. -/
theorem projectedSmallTerm_outcomeFlow_positive (w : HedgeWitness G q) :
    0 < projectedSmallTerm w (outcomeFlowBackground w) := by
  let samples := S.binary.assignmentEnumeration.filter
    (FiniteProduct.falseCylinder S.count (NodeSet.union q.action q.outcome))
  let sign := fun sample : S.binary.Assignment => FiniteProbRecord.characterSign
    (Bool.xor (signalPhase w.small (outcomeFlowSignal w) sample)
      (signalPhase (outcomeFlowBackground w) (outcomeFlowSignal w) sample))
  have even : forall sample, sample ∈ samples -> sign sample = 1 := by
    intro sample listed
    have phase := outcomeFlow_phase_false_of_outcome w sample
      (outcome_of_combined sample (List.mem_filter.mp listed).2)
    change FiniteProbRecord.characterSign _ = 1
    exact congrArg FiniteProbRecord.characterSign phase
  let zeroSample : S.binary.Assignment := fun _ => false
  have zeroListed : zeroSample ∈ samples := List.mem_filter.mpr
    ⟨S.binary.assignmentEnumeration_complete zeroSample,
      (FiniteProduct.falseCylinder_eq_true_iff _ _ _).mpr (fun _ _selected => rfl)⟩
  have signSumPositive : 0 < (samples.map sign).sum :=
    FiniteSupportedSum.sum_pos_of_mem samples sign
      (fun sample listed => by rw [even sample listed]; decide) zeroSample zeroListed
      (by rw [even zeroSample zeroListed]; decide)
  have scalarPositive := HedgeChannelCoefficients.tables_choiceScalarUnder_positive
    (channelCount w) S.count (rightNodes w) (rightAnchors w) (rightDeficits w)
    (falseActionTarget q.action) (fullChoice w w.small (smallChannel w) (outcomeFlowBackground w))
    (fullSmallChoice_allowed_of_avoids_action w _ (outcomeFlowBackground_avoids_action w))
  rw [projectedSmallTerm_eq_weightedCharacterSum w _ (outcomeFlowBackground_subset_outside w)]
  exact Int.mul_pos
    (Int.mul_pos (Int.natCast_pos.mpr (PairRootChannels.prior G.binary (channelCount w)).den_pos)
      (Int.natCast_pos.mpr scalarPositive)) signSumPositive

/-! ## Complete surviving sum and the actual original-event gap -/

/-- Sum the actual original-event contribution of every permitted full-small
choice.  This is the exact canonical list from the intervention reduction,
not a sum over one selected mask or over an enlarged outcome event. -/
def projectedFullSmallSum (w : HedgeWitness G q) : Int :=
  ((rightFullChoicesUnder w (falseActionTarget q.action)).map (fun choice =>
    ((S.binary.assignmentEnumeration.filter (FiniteProduct.falseCylinder S.count q.outcome)).map
      (fun sample => rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w)
        (falseActionTarget q.action) sample choice)).sum)).sum

/-- Every actual listed full-small choice contributes nonnegatively and
the explicitly supplied outcome-flow choice is listed and positive.  Hence
the complete original-event contribution is positive, with every occurrence
of the real canonical enumeration retained. -/
theorem projectedFullSmallSum_positive (w : HedgeWitness G q) : 0 < projectedFullSmallSum w := by
  let term := fun choice : Fin S.count -> Option (Fin (channelCount w)) =>
    ((S.binary.assignmentEnumeration.filter (FiniteProduct.falseCylinder S.count q.outcome)).map
      (fun sample => rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w)
        (falseActionTarget q.action) sample choice)).sum
  have nonnegative : forall choice, choice ∈ rightFullChoicesUnder w (falseActionTarget q.action) -> 0 <= term choice := by
    intro choice listed
    rcases List.mem_map.mp (List.mem_filter.mp listed).1 with ⟨mask, member, same⟩
    rw [← same]
    exact projectedSmallTerm_nonneg w mask ((masks_member_iff _ _).mp member)
  have distinguished : fullChoice w w.small (smallChannel w) (outcomeFlowBackground w) ∈
      rightFullChoicesUnder w (falseActionTarget q.action) := List.mem_filter.mpr
    ⟨List.mem_map.mpr ⟨outcomeFlowBackground w,
      (masks_member_iff _ _).mpr (outcomeFlowBackground_subset_outside w), rfl⟩,
      fullSmallChoice_allowed_of_avoids_action w _ (outcomeFlowBackground_avoids_action w)⟩
  exact FiniteSupportedSum.sum_pos_of_mem _ term nonnegative _ distinguished
    (projectedSmallTerm_outcomeFlow_positive w)

/-- The complete actual right original-event numerator exceeds the left
one for the full original action.  This is a general supplied-hedge theorem,
not a fixture computation, single full-cell gap or restricted replay result. -/
theorem original_eventNumerators_lt (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    HedgeChannelTable.eventNumerator G (channelCount w) (leftTables w)
      (leftSignals w rich (outcomeFlowSignal w) (outcomeFlowSignal w)) (falseActionTarget q.action)
      (FiniteProduct.falseCylinder S.count q.outcome) <
    HedgeChannelTable.eventNumerator G (channelCount w) (rightTables w)
      (rightSignals w (outcomeFlowSignal w) (outcomeFlowSignal w)) (falseActionTarget q.action)
      (FiniteProduct.falseCylinder S.count q.outcome) := by
  have forced : falseActionTarget q.action w.actionSeed = some false := by
    simp only [falseActionTarget, w.actionSeed_in_action, if_true]
  have difference := eventNumerators_difference_of_action w rich (outcomeFlowSignal w) (outcomeFlowSignal w)
    (falseActionTarget q.action) false forced (FiniteProduct.falseCylinder S.count q.outcome)
  have swapped := FiniteSupportedSum.sum_swap
    (S.binary.assignmentEnumeration.filter (FiniteProduct.falseCylinder S.count q.outcome))
    (rightFullChoicesUnder w (falseActionTarget q.action))
    (fun sample choice => rightTermIntegralUnder w (outcomeFlowSignal w) (outcomeFlowSignal w)
      (falseActionTarget q.action) sample choice)
  have completeDifference := difference.trans (congrArg (fun total : Int =>
    (HedgeChannelTable.eventNumerator G (channelCount w) (leftTables w)
      (leftSignals w rich (outcomeFlowSignal w) (outcomeFlowSignal w)) (falseActionTarget q.action)
      (FiniteProduct.falseCylinder S.count q.outcome) : Int) + total) swapped)
  have positive := projectedFullSmallSum_positive w
  change _ = _ + projectedFullSmallSum w at completeDifference
  apply Int.ofNat_lt.mp
  omega

/-- Actual installed interventional probabilities differ on the unchanged
original all-false outcome event.  The denominator bridge uses equal actual
row capacities; numerator separation is supplied by the complete general
projection theorem, not assumed as a countermodel premise. -/
theorem models_original_event_not_equiv (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ¬ QProb.Equiv
      ((leftModel w rich (outcomeFlowSignal w) (outcomeFlowSignal w)).interventionalValue
        (falseActionTarget q.action) (FiniteProduct.falseCylinder S.count q.outcome))
      ((rightModel w (outcomeFlowSignal w) (outcomeFlowSignal w)).interventionalValue
        (falseActionTarget q.action) (FiniteProduct.falseCylinder S.count q.outcome)) :=
  HedgeChannelTable.model_interventional_event_not_equiv G (channelCount w) (leftTables w) (rightTables w)
    (leftSignals w rich (outcomeFlowSignal w) (outcomeFlowSignal w))
    (rightSignals w (outcomeFlowSignal w) (outcomeFlowSignal w)) (capacities_equal w)
    (falseActionTarget q.action) (FiniteProduct.falseCylinder S.count q.outcome)
    (Nat.ne_of_lt (original_eventNumerators_lt w rich))

end HedgeChannelInstallation
end Causality
end Thesis
