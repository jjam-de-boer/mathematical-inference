import Thesis.CausalTransport.HedgeChannelFullTerms

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Exact surviving likelihood difference under the original action cut

The factual survivor lists cannot simply be reused as an intervention
enumeration: a forced row admits only its consistency-indicator choice.
Here the finite support test removes precisely the canonical choices with
a channel at a forced row.  It does not discard a conflicting forced sample;
that sample is still represented by its actual zero coefficient.

Forcing the stored action seed cancels every left term selecting a large
channel, with arbitrary additional forced vertices retained.  The complete
left likelihood therefore contains only the permitted common backgrounds.
The right likelihood contains the same backgrounds and every permitted
full small-channel term.  The exact difference below is a sum of those
actual integrated terms on the original pair-root prior.

Each full-small term is also evaluated under the actual intervention: its
shared incidence cancels, leaving the entire literal prior mass, the actual
forced-indicator coefficient, and its observed/parent character.  A conflicting
forced sample therefore keeps coefficient zero instead of being assigned a
positive character contribution.

This is the intervention-side expansion needed for original-query
separation.  It does not assert that the difference is positive at every
full assignment: character signs can change.  A separating outcome event
must still prove that projection retains a nonzero total contribution.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## Actual permitted canonical choices and term integrals -/

/-- All common background interactions that do not select a channel at
a forced row.  Every unconsumed free row still has both ordinary choices. -/
def commonChoicesUnder (w : HedgeWitness G q) (target : Fin S.count -> Option Bool) :=
  (commonChoices w).filter (HedgeChannelTable.choiceAllowedUnder target)

/-- Every full small-channel choice permitted by the actual intervention.
If a small-forest row is forced, this block has no permitted full term. -/
def rightFullChoicesUnder (w : HedgeWitness G q) (target : Fin S.count -> Option Bool) :=
  (rightFullChoices w).filter (HedgeChannelTable.choiceAllowedUnder target)

/-- Complete right canonical support under an arbitrary hard intervention. -/
def rightSurvivorsUnder (w : HedgeWitness G q) (target : Fin S.count -> Option Bool) :=
  commonChoicesUnder w target ++ rightFullChoicesUnder w target

/-- One actual left monomial integral, retaining every forced indicator. -/
def leftTermIntegralUnder (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (choice : Fin S.count -> Option (Fin (channelCount w))) : Int :=
  (PairRootChannels.prior G.binary (channelCount w)).signedMass
    (HedgeChannelTable.choiceMonomial G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) target sample choice)

/-- The corresponding right monomial integral on the same actual prior. -/
def rightTermIntegralUnder (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal S)
    (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin (channelCount w))) : Int :=
  (PairRootChannels.prior G.binary (channelCount w)).signedMass
    (HedgeChannelTable.choiceMonomial G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) target sample choice)

/-- Exact full-small integral under any target, retaining every forced
consistency indicator in its scalar coefficient.  Even an unsupported
forced-channel choice remains zero; it is not rescued by the even shared
incidence of a full forest. -/
theorem right_fullTermIntegral_under (w : HedgeWitness G q)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) :
    rightTermIntegralUnder w smallSignal backgroundSignal target sample (fullChoice w w.small (smallChannel w) mask) =
      ((PairRootChannels.prior G.binary (channelCount w)).den : Int) *
        HedgeChannelTable.choiceCoefficient (rightTables w) target sample (fullChoice w w.small (smallChannel w) mask) *
        FiniteProbRecord.characterSign (Bool.xor (signalPhase w.small smallSignal sample)
          (signalPhase mask backgroundSignal sample)) := by
  have evaluated := fullChoice_signedMass_under w (rightTables w) (rightNodes w)
    (rightParentSignal w smallSignal backgroundSignal) backgroundSignal
    (by intro child; rw [rightNodes, role_backgroundChannel])
    (by intro child parents; rw [rightParentSignal, role_backgroundChannel])
    w.small (smallChannel w) (rightNodes_smallChannel w) mask subset target sample
  simpa only [signalPhase, rightParentSignal, role_smallChannel] using evaluated

private instance choiceDecidableEq (w : HedgeWitness G q) :
    DecidableEq (Fin S.count -> Option (Fin (channelCount w))) :=
  FiniteProduct.assignmentDecidableEq S.count (fun _ => Option (Fin (channelCount w))) (fun _ => inferInstance)

private theorem commonChoicesUnder_nodup (w : HedgeWitness G q) (target : Fin S.count -> Option Bool) :
    (commonChoicesUnder w target).Nodup :=
  List.Pairwise.filter _ (List.nodup_append.mp (leftSurvivors_nodup w)).1

private theorem rightSurvivorsUnder_nodup (w : HedgeWitness G q) (target : Fin S.count -> Option Bool) :
    (rightSurvivorsUnder w target).Nodup := by
  simpa only [rightSurvivorsUnder, commonChoicesUnder, rightFullChoicesUnder,
    rightSurvivors, List.filter_append] using
    List.Pairwise.filter (HedgeChannelTable.choiceAllowedUnder target) (rightSurvivors_nodup w)

private theorem commonChoicesUnder_left_member (w : HedgeWitness G q) (target : Fin S.count -> Option Bool)
    (choice : Fin S.count -> Option (Fin (channelCount w))) (member : choice ∈ commonChoicesUnder w target) :
    choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (leftTables w child).expansionChoicesUnder (target child)) := by
  have parts := List.mem_filter.mp member
  exact (HedgeChannelTable.choiceUnder_member_iff (leftTables w) target choice).mpr
    ⟨leftSurvivors_member w choice (List.mem_append.mpr (Or.inl parts.1)), parts.2⟩

private theorem rightSurvivorsUnder_member (w : HedgeWitness G q) (target : Fin S.count -> Option Bool)
    (choice : Fin S.count -> Option (Fin (channelCount w))) (member : choice ∈ rightSurvivorsUnder w target) :
    choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (rightTables w child).expansionChoicesUnder (target child)) := by
  have filtered : choice ∈ (rightSurvivors w).filter (HedgeChannelTable.choiceAllowedUnder target) := by
    simpa only [rightSurvivorsUnder, commonChoicesUnder, rightFullChoicesUnder,
      rightSurvivors, List.filter_append] using member
  have parts := List.mem_filter.mp filtered
  exact (HedgeChannelTable.choiceUnder_member_iff (rightTables w) target choice).mpr
    ⟨rightSurvivors_member w choice parts.1, parts.2⟩

/-! ## Actual integration eliminates every omitted term -/

private theorem leftTermIntegralUnder_zero_outside (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (fixed : Bool) (forced : target w.actionSeed = some fixed) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (leftTables w child).expansionChoicesUnder (target child)))
    (excluded : choice ∉ commonChoicesUnder w target) :
    leftTermIntegralUnder w rich smallSignal backgroundSignal target sample choice = 0 := by
  by_cases zero : leftTermIntegralUnder w rich smallSignal backgroundSignal target sample choice = 0
  · exact zero
  · have allowed := ((HedgeChannelTable.choiceUnder_member_iff (leftTables w) target choice).mp member).2
    rcases left_nonzero_choice_under w rich smallSignal backgroundSignal target sample choice member zero with common | main
    · apply False.elim
      apply excluded
      exact List.mem_filter.mpr ⟨List.mem_map.mpr
        ⟨backgroundMask w choice, (masks_member_iff _ _).mpr common.2, common.1.symm⟩, allowed⟩
    · rcases main with ⟨index, same, _subset⟩
      have picked : choice w.actionRoot = some (largeChannel w index) := by
        rw [same]
        simp only [fullChoice, w.actionRoot_in_large, if_true]
      exact False.elim (zero (left_large_term_zero_of_action w rich smallSignal backgroundSignal target sample
        choice member index fixed forced w.actionRoot picked))

private theorem rightTermIntegralUnder_zero_outside (w : HedgeWitness G q)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (rightTables w child).expansionChoicesUnder (target child)))
    (excluded : choice ∉ rightSurvivorsUnder w target) :
    rightTermIntegralUnder w smallSignal backgroundSignal target sample choice = 0 := by
  by_cases zero : rightTermIntegralUnder w smallSignal backgroundSignal target sample choice = 0
  · exact zero
  · apply False.elim
    apply excluded
    have allowed := ((HedgeChannelTable.choiceUnder_member_iff (rightTables w) target choice).mp member).2
    rcases right_nonzero_choice_under w smallSignal backgroundSignal target sample choice member zero with common | main
    · exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨List.mem_map.mpr
        ⟨backgroundMask w choice, (masks_member_iff _ _).mpr common.2, common.1.symm⟩, allowed⟩))
    · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨List.mem_map.mpr
        ⟨remainingBackgroundMask w w.small choice, (masks_member_iff _ _).mpr main.2, main.1.symm⟩, allowed⟩))

/-! ## Complete actual likelihoods under the action cut -/

/-- Forcing the stored action seed leaves precisely the permitted common
background sum on the left.  Other forced rows and conflicting sample
values remain present; no composite-action readiness premise is required. -/
theorem left_expandedIntegral_common_under (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (fixed : Bool) (forced : target w.actionSeed = some fixed) (sample : S.binary.Assignment) :
    HedgeChannelTable.expandedIntegral G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) target sample =
      ((commonChoicesUnder w target).map (leftTermIntegralUnder w rich smallSignal backgroundSignal target sample)).sum :=
  (HedgeChannelTable.expandedIntegral_eq_sum G (channelCount w) (leftTables w)
    (leftSignals w rich smallSignal backgroundSignal) target sample).trans
    (FiniteSupportedSum.sum_eq_of_zero_outside _ _
      (FiniteProduct.enumeration_nodup S.count (fun _ => Option (Fin (channelCount w))) _
        (fun _ => inferInstance) (fun child => HedgeChannelCoefficients.tables_expansionChoicesUnder_nodup
          (channelCount w) S.count (leftNodes w) (leftAnchors w) (leftDeficits w) child (target child)))
      (commonChoicesUnder_nodup w target) (commonChoicesUnder_left_member w target)
      (leftTermIntegralUnder w rich smallSignal backgroundSignal target sample)
      (leftTermIntegralUnder_zero_outside w rich smallSignal backgroundSignal target fixed forced sample))

/-- Exact right reduction for any intervention, not just the original
action cut.  The canonical support retains every eligible full-small term. -/
theorem right_expandedIntegral_survivors_under (w : HedgeWitness G q)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    HedgeChannelTable.expandedIntegral G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) target sample =
      ((rightSurvivorsUnder w target).map (rightTermIntegralUnder w smallSignal backgroundSignal target sample)).sum :=
  (HedgeChannelTable.expandedIntegral_eq_sum G (channelCount w) (rightTables w)
    (rightSignals w smallSignal backgroundSignal) target sample).trans
    (FiniteSupportedSum.sum_eq_of_zero_outside _ _
      (FiniteProduct.enumeration_nodup S.count (fun _ => Option (Fin (channelCount w))) _
        (fun _ => inferInstance) (fun child => HedgeChannelCoefficients.tables_expansionChoicesUnder_nodup
          (channelCount w) S.count (rightNodes w) (rightAnchors w) (rightDeficits w) child (target child)))
      (rightSurvivorsUnder_nodup w target) (rightSurvivorsUnder_member w target)
      (rightTermIntegralUnder w smallSignal backgroundSignal target sample)
      (rightTermIntegralUnder_zero_outside w smallSignal backgroundSignal target sample))

private theorem commonTermIntegrals_equal_under (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool) (sample : S.binary.Assignment) :
    ((commonChoicesUnder w target).map (leftTermIntegralUnder w rich smallSignal backgroundSignal target sample)).sum =
      ((commonChoicesUnder w target).map (rightTermIntegralUnder w smallSignal backgroundSignal target sample)).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro choice member
  rcases List.mem_map.mp (List.mem_filter.mp member).1 with ⟨mask, _listed, same⟩
  rw [← same]
  exact backgroundTermIntegrals_equal_under w rich smallSignal backgroundSignal target sample mask

/-- The exact complete expansion difference after forcing the stored
action seed is the full small-channel sum.  This is an equality of actual
integrated numerators, not an assertion of a positive projected gap yet. -/
theorem expandedIntegrals_difference_of_action (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (fixed : Bool) (forced : target w.actionSeed = some fixed) (sample : S.binary.Assignment) :
    HedgeChannelTable.expandedIntegral G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) target sample =
      HedgeChannelTable.expandedIntegral G (channelCount w) (leftTables w)
        (leftSignals w rich smallSignal backgroundSignal) target sample +
      ((rightFullChoicesUnder w target).map (rightTermIntegralUnder w smallSignal backgroundSignal target sample)).sum := by
  rw [left_expandedIntegral_common_under w rich smallSignal backgroundSignal target fixed forced sample,
    right_expandedIntegral_survivors_under w smallSignal backgroundSignal target sample]
  simp only [rightSurvivorsUnder, List.map_append, List.sum_append]
  rw [commonTermIntegrals_equal_under]

/-- The same difference at the actual nonnegative natural likelihood
numerators.  The signed term sum is kept as an integer embedding and is
not truncated to Nat or divided by a probability denominator. -/
theorem integratedNumerators_difference_of_action (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (fixed : Bool) (forced : target w.actionSeed = some fixed) (sample : S.binary.Assignment) :
    (HedgeChannelTable.integratedNumerator G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) target sample : Int) =
      (HedgeChannelTable.integratedNumerator G (channelCount w) (leftTables w)
        (leftSignals w rich smallSignal backgroundSignal) target sample : Int) +
      ((rightFullChoicesUnder w target).map (rightTermIntegralUnder w smallSignal backgroundSignal target sample)).sum := by
  rw [HedgeChannelTable.integratedNumerator_expansion, HedgeChannelTable.integratedNumerator_expansion]
  exact expandedIntegrals_difference_of_action w rich smallSignal backgroundSignal target fixed forced sample

private theorem natSum_cast {α : Type u} (values : List α) (term : α -> Nat) :
    ((values.map term).sum : Int) = (values.map (fun value => (term value : Int))).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, Int.natCast_add, inductionHypothesis]

private theorem intSum_add {α : Type u} (values : List α) (left right : α -> Int) :
    (values.map (fun value => left value + right value)).sum =
      (values.map left).sum + (values.map right).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, inductionHypothesis]
      ac_rfl

/-- Projection to any original observed event retains exactly the sum of
the full small-channel contributions over its selected factual samples.
The event can be the original query's outcome cylinder; neither a single
full cell nor a changed outcome set is substituted for that projection.
Nonzeroness of this complete event contribution remains a further theorem. -/
theorem eventNumerators_difference_of_action (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (fixed : Bool) (forced : target w.actionSeed = some fixed) (event : Event S.binary.Assignment) :
    (HedgeChannelTable.eventNumerator G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) target event : Int) =
      (HedgeChannelTable.eventNumerator G (channelCount w) (leftTables w)
        (leftSignals w rich smallSignal backgroundSignal) target event : Int) +
      ((S.binary.assignmentEnumeration.filter event).map (fun sample =>
        ((rightFullChoicesUnder w target).map (rightTermIntegralUnder w smallSignal backgroundSignal target sample)).sum)).sum := by
  unfold HedgeChannelTable.eventNumerator
  rw [natSum_cast, natSum_cast]
  have pointwise := List.map_congr_left (l := S.binary.assignmentEnumeration.filter event)
    (fun sample _selected => integratedNumerators_difference_of_action w rich smallSignal backgroundSignal target fixed forced sample)
  exact (congrArg List.sum pointwise).trans (intSum_add _ _ _)

end HedgeChannelInstallation
end Causality
end Thesis
