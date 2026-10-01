import Thesis.CausalTransport.HedgeInterventionalSupport

namespace Thesis
namespace Causality

open Probability

/-!
# Weighted interventional defect compensation

`HedgeInterventionalSupport` constructs an explicit pair-root translation
that compensates a defect flip in the large carrier's complete evaluation.
A pointwise coupling is not yet a probability theorem: the original prior
gives each inactive-defect assignment weight two and each active-defect
assignment weight one.  In particular, its two strata do not have equal mass.

This module connects that coupling to the *existing* weighted product prior.
The old latent enumeration is duplicate-free and exhaustive.  Translating
its pair coordinates is an explicit involution, so it permutes that same
enumeration while leaving every full-alphabet private background unchanged.
Singleton masses then give an exact slice formula.  Compensated event slices
have equal numbers of assignments, and hence a two-to-one mass ratio.  The
same ratio for the complete strata cancels on normalization: conditioning on
either defect gives the original observed event probability.

The final application retains arbitrary interventions fixing a large-forest
vertex, arbitrary Boolean events on complete observed assignments, and the
original biased prior.  It neither replaces that prior by a fair one nor
assumes an equality of interventional distributions.  It also does not compare
the large and small carrier models: that distinct conditional-countermodel
obligation remains open.
-/

/-! ## Explicit latent translations preserve the old enumeration -/

/-- Translate only the pair-root block of an old latent assignment.  The
canonical private indices are recovered and reassembled literally, including
indices of observed labels other than the two distinguished parity values. -/
def hedgeLatentPairTranslation (G : ObservedGraph S)
    (delta : Fin (pairRootCount G) -> Bool)
    (old : (hedgeLatentExtension G).Assignment) :
    (hedgeLatentExtension G).Assignment :=
  hedgeLatentOfCoordinates G (hedgePairBitsXor G (hedgePairBitsOf G old) delta)
    (hedgePrivateCoordinatesOf G old)

/-- The same translation is its own inverse.  No inverse is selected from
surjectivity; the two coordinate recovery laws compute it explicitly. -/
theorem hedgeLatentPairTranslation_involutive (G : ObservedGraph S)
    (delta : Fin (pairRootCount G) -> Bool)
    (old : (hedgeLatentExtension G).Assignment) :
    hedgeLatentPairTranslation G delta (hedgeLatentPairTranslation G delta old) = old := by
  simp only [hedgeLatentPairTranslation, hedgePairBitsOf_latentOfCoordinates,
    hedgePrivateCoordinatesOf_latentOfCoordinates, hedgePairBitsXor_self_right,
    hedgeLatentOfCoordinates_recover]

/-- Translation permutes the actual exhaustive old latent enumeration.  A
constructive duplicate-free-list argument uses the displayed involution in
both directions, without classical finite-cardinality or choice machinery. -/
theorem hedgeLatentAssignmentEnum_map_pairTranslation_perm (G : ObservedGraph S)
    (delta : Fin (pairRootCount G) -> Bool) :
    ((hedgeLatentAssignmentEnum G).map (hedgeLatentPairTranslation G delta)).Perm
      (hedgeLatentAssignmentEnum G) := by
  apply ConstructivePermutation.perm_of_nodup_mem_iff
  · apply nodup_map_of_injective
    · intro left right equal
      have inverse := congrArg (hedgeLatentPairTranslation G delta) equal
      simpa only [hedgeLatentPairTranslation_involutive] using inverse
    · exact hedgeLatentAssignmentEnum_nodup G
  · exact hedgeLatentAssignmentEnum_nodup G
  · intro old
    constructor
    · intro _listed
      exact hedgeLatentAssignmentEnum_complete G old
    · intro _listed
      exact List.mem_map.mpr
        ⟨hedgeLatentPairTranslation G delta old,
          hedgeLatentAssignmentEnum_complete G _,
          hedgeLatentPairTranslation_involutive G delta old⟩

/-! ## Exact weighted masses of arbitrary fixed-defect slices -/

/-- A Boolean event selecting one value of the distinguished private defect.
This is an event of the original augmented latent prior, not a new measure. -/
def hedgeDefectStratum (G : ObservedGraph S) (defect : Bool) :
    Event ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root) :=
  fun unit => hedgeDefectBitOf G unit == defect

private theorem sum_constant (values : List A) (weight : Nat) :
    (values.map fun _ => weight).sum = weight * values.length := by
  induction values with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.mul_zero]
  | cons head rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, inductionHypothesis,
        Nat.mul_succ]
      omega

/-- The natural numerator of any fixed-defect event is the number of its
old assignments times the declared defect weight.  Old coordinates may be
tested jointly and arbitrarily; no rectangular-event assumption is used.

The proof enumerates exactly the slice, maps its members to actual augmented
assignments, and sums their already proved singleton masses.  Keeping the
weights visible is essential: equinumerous slices are not equiprobable before
conditioning when their defect bits differ. -/
theorem hedgeDefectPrior_eventMass_stratum (G : ObservedGraph S)
    (defect : Bool)
    (event : Event ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root)) :
    FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
        (fun unit => hedgeDefectStratum G defect unit && event unit) =
      (if defect then 1 else 2) *
        ((hedgeLatentAssignmentEnum G).filter
          (fun old => event (hedgeDefectAssignment G old defect))).length := by
  let oldSupport := (hedgeLatentAssignmentEnum G).filter
    (fun old => event (hedgeDefectAssignment G old defect))
  let support := oldSupport.map (fun old => hedgeDefectAssignment G old defect)
  have supportNodup : support.Nodup := by
    apply nodup_map_of_injective
    · intro left right equal
      exact hedgeDefectAssignment_injective_old G defect equal
    · exact List.Sublist.nodup List.filter_sublist (hedgeLatentAssignmentEnum_nodup G)
  have supportSpec : forall unit, unit ∈ support ↔
      (hedgeDefectStratum G defect unit && event unit) = true := by
    intro unit
    constructor
    · intro listed
      rcases List.mem_map.mp listed with ⟨old, oldListed, equal⟩
      rw [← equal]
      simp only [hedgeDefectStratum, hedgeDefectBitOf_assignment, beq_self_eq_true,
        Bool.true_and]
      exact (List.mem_filter.mp oldListed).2
    · intro selected
      have parts := Bool.and_eq_true_iff.mp selected
      have sameDefect : hedgeDefectBitOf G unit = defect := eq_of_beq parts.1
      have recovered : hedgeDefectAssignment G (hedgeDefectOldAssignment G unit) defect = unit := by
        rw [← sameDefect]
        exact hedgeDefectAssignment_recover G unit
      apply List.mem_map.mpr
      refine ⟨hedgeDefectOldAssignment G unit, List.mem_filter.mpr ⟨?_, ?_⟩, recovered⟩
      · exact hedgeLatentAssignmentEnum_complete G _
      · rw [recovered]
        exact parts.2
  have eventEq : (fun unit => hedgeDefectStratum G defect unit && event unit) =
      FiniteProbRecord.membershipEvent support := by
    funext unit
    apply Bool.eq_iff_iff.mpr
    simpa only [FiniteProbRecord.membershipEvent, decide_eq_true_eq] using (supportSpec unit).symm
  rw [eventEq, FiniteProbRecord.eventMass_membership_eq_sum_singletons _ support supportNodup]
  simp only [support, List.map_map]
  have weights : (oldSupport.map fun old => FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
      (FiniteProbRecord.singletonEvent (hedgeDefectAssignment G old defect))) =
      oldSupport.map (fun _ => if defect then 1 else 2) := by
    apply List.map_congr_left
    intro old _listed
    exact hedgeDefectPrior_eventMass_assignment G old defect
  exact (congrArg List.sum weights).trans (sum_constant oldSupport _)

/-- An event coupled across the two defect values by a fixed pair-root
translation has twice as much inactive-defect mass as active-defect mass.
The premise is a pointwise equation on actual latent assignments, not an
assumed probability equality; the old enumeration permutation supplies the
missing finite counting step. -/
theorem hedgeDefectPrior_eventMass_strata_eq_of_pair_compensation
    (G : ObservedGraph S) (delta : Fin (pairRootCount G) -> Bool)
    (event : Event ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root))
    (compensates : forall old, event (hedgeDefectAssignment G old false) =
      event (hedgeDefectAssignment G (hedgeLatentPairTranslation G delta old) true)) :
    FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
        (fun unit => hedgeDefectStratum G false unit && event unit) =
      2 * FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
        (fun unit => hedgeDefectStratum G true unit && event unit) := by
  rw [hedgeDefectPrior_eventMass_stratum, hedgeDefectPrior_eventMass_stratum]
  simp only [Bool.false_eq_true, if_false, if_true, Nat.one_mul]
  congr 1
  have enumeration := hedgeLatentAssignmentEnum_map_pairTranslation_perm G delta
  have filtered := (enumeration.filter
    (fun old => event (hedgeDefectAssignment G old true))).length_eq
  rw [List.filter_map, List.length_map] at filtered
  have sliceEq : (fun old => event (hedgeDefectAssignment G old false)) =
      (fun old => event (hedgeDefectAssignment G old true)) ∘ hedgeLatentPairTranslation G delta := by
    funext old
    exact compensates old
  rw [sliceEq]
  exact filtered

/-! ## Normalization removes the defect bias, without changing the prior -/

/-- Both complete defect strata have positive prior mass.  An explicit old
default assignment supplies a positive singleton inside either event, so the
conditioning operations below do not need a chosen support witness. -/
theorem hedgeDefectPrior_stratum_positive (G : ObservedGraph S) (defect : Bool) :
    (hedgeDefectPrior G).EventPositive (hedgeDefectStratum G defect) := by
  let unit := hedgeDefectAssignment G (hedgeLatentDefault G) defect
  apply Nat.lt_of_lt_of_le (hedgeDefectPrior_singleton_mass_pos G unit)
  apply FiniteProbRecord.eventMass_mono
  intro candidate selected
  have equal : candidate = unit := of_decide_eq_true selected
  subst candidate
  simp only [unit, hedgeDefectStratum, hedgeDefectBitOf_assignment, beq_self_eq_true]

/-- Splitting an arbitrary event by the two defect values is an exact
disjoint partition.  This identity includes zero-mass events and needs no
factorization or support assumption on the observed event. -/
theorem hedgeDefectPrior_eventMass_eq_sum_strata (G : ObservedGraph S)
    (event : Event ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root)) :
    FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms event =
      FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
        (fun unit => hedgeDefectStratum G false unit && event unit) +
      FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
        (fun unit => hedgeDefectStratum G true unit && event unit) := by
  let left := fun unit => hedgeDefectStratum G false unit && event unit
  let right := fun unit => hedgeDefectStratum G true unit && event unit
  have partition : event = Probability.union left right := by
    funext unit
    dsimp only [Probability.union, left, right, hedgeDefectStratum]
    cases hedgeDefectBitOf G unit <;> cases event unit <;> rfl
  have disjoint : Probability.disjoint left right := by
    intro unit inLeft inRight
    cases bitAt : hedgeDefectBitOf G unit <;>
      simp [left, right, hedgeDefectStratum, bitAt] at inLeft inRight
  exact (congrArg (FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms) partition).trans
    (FiniteProbRecord.eventMass_union_disjoint _ left right disjoint)

/-- The complete stratum's numerator is its declared defect weight times
the number of old assignments.  This denominator count is shared with the
arbitrary-event numerator formula, which is why normalization can cancel the
two-to-one bias without pretending that the raw masses are equal. -/
theorem hedgeDefectPrior_eventMass_stratum_top (G : ObservedGraph S) (defect : Bool) :
    FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms (hedgeDefectStratum G defect) =
      (if defect then 1 else 2) * (hedgeLatentAssignmentEnum G).length := by
  have counted := hedgeDefectPrior_eventMass_stratum G defect Probability.topEvent
  have filterTop : forall values : List (hedgeLatentExtension G).Assignment,
      values.filter (fun _ => true) = values := by
    intro values
    induction values with
    | nil => rfl
    | cons head rest inductionHypothesis =>
        exact congrArg (List.cons head) inductionHypothesis
  simpa only [Probability.topEvent, Bool.and_true, filterTop] using counted

/-- Exact common denominator of the original biased product prior, derived
from its two strata rather than from a different product presentation. -/
theorem hedgeDefectPrior_den_eq_three_mul (G : ObservedGraph S) :
    (hedgeDefectPrior G).den = 3 * (hedgeLatentAssignmentEnum G).length := by
  have partition := hedgeDefectPrior_eventMass_eq_sum_strata G Probability.topEvent
  simp only [Probability.topEvent, Bool.and_true] at partition
  rw [FiniteProbRecord.eventMass_top, (hedgeDefectPrior G).total_mass,
    hedgeDefectPrior_eventMass_stratum_top, hedgeDefectPrior_eventMass_stratum_top] at partition
  simp only [Bool.false_eq_true, if_false, if_true, Nat.one_mul] at partition
  omega

/-- A compensated event has three units of total mass for every unit in
its active-defect slice.  This is an equality of natural numerators under
the original prior, before any division by a conditioning denominator. -/
theorem hedgeDefectPrior_eventMass_eq_three_mul_of_pair_compensation
    (G : ObservedGraph S) (delta : Fin (pairRootCount G) -> Bool)
    (event : Event ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root))
    (compensates : forall old, event (hedgeDefectAssignment G old false) =
      event (hedgeDefectAssignment G (hedgeLatentPairTranslation G delta old) true)) :
    FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms event =
      3 * FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
        (fun unit => hedgeDefectStratum G true unit && event unit) := by
  rw [hedgeDefectPrior_eventMass_eq_sum_strata,
    hedgeDefectPrior_eventMass_strata_eq_of_pair_compensation G delta event compensates]
  omega

/-- Conditional and unconditional probabilities agree for every event
preserved by the explicit pair-root compensation.  This is independence
from the defect for that event, not equality of the two raw stratum masses.

The support proof belongs to the actual original prior.  Both the conditioned
record and its unconditional comparison use that prior's literal atoms;
only their common-denominator rational representations are compared. -/
theorem hedgeDefectPrior_conditionOn_probVal_equiv_of_pair_compensation
    (G : ObservedGraph S) (delta : Fin (pairRootCount G) -> Bool)
    (event : Event ((root : Fin (hedgeDefectLatentCount G)) -> hedgeDefectLatentValue G root))
    (compensates : forall old, event (hedgeDefectAssignment G old false) =
      event (hedgeDefectAssignment G (hedgeLatentPairTranslation G delta old) true))
    (defect : Bool) :
    QProb.Equiv
      (((hedgeDefectPrior G).conditionOn (hedgeDefectStratum G defect)
        (hedgeDefectPrior_stratum_positive G defect)).probVal event)
      ((hedgeDefectPrior G).probVal event) := by
  simp only [QProb.Equiv, FiniteProbRecord.probVal, FiniteProbRecord.conditionOn,
    FiniteProbRecord.eventMass_filter_event]
  rw [hedgeDefectPrior_eventMass_eq_three_mul_of_pair_compensation G delta event compensates,
    hedgeDefectPrior_eventMass_stratum_top, hedgeDefectPrior_den_eq_three_mul]
  cases defect with
  | false =>
      rw [hedgeDefectPrior_eventMass_strata_eq_of_pair_compensation G delta event compensates]
      simp only [Bool.false_eq_true, if_false]
      ac_rfl
  | true =>
      simp only [if_true, Nat.one_mul]
      ac_rfl

/-! ## The large carrier under an intervention fixing a forest vertex -/

/-- Exact weighted event-slice comparison for the actual large carrier SCM.
The balancing vertex may be any intervened large-forest vertex.  All other
action coordinates and intervention values are retained, and `event` may
inspect the complete observed assignment, including nonbinary labels. -/
theorem HedgeWitness.largeCarrierDefectParityModel_interventional_eventMass_strata_eq
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (fixed : intervention balance ≠ none)
    (event : Event S.Assignment) :
    FiniteProbRecord.eventMass (w.largeCarrierDefectParityModel rich).prior.atoms
        (fun unit => hedgeDefectStratum G false unit &&
          event ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit)) =
      2 * FiniteProbRecord.eventMass (w.largeCarrierDefectParityModel rich).prior.atoms
        (fun unit => hedgeDefectStratum G true unit &&
          event ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit)) := by
  apply hedgeDefectPrior_eventMass_strata_eq_of_pair_compensation G
    (w.largeCarrierDefectCompensation balance inside)
  intro old
  have coupling := w.largeCarrierDefectParityModel_evalUnder_compensate_defect rich balance inside
    intervention fixed (hedgePairBitsOf G old) (hedgePrivateCoordinatesOf G old) false
  simpa only [hedgeLatentOfCoordinates_recover, Bool.not_false, hedgeLatentPairTranslation] using
    congrArg event coupling

/-- Every observed interventional event has the same probability after
conditioning on either private defect value as without that conditioning.
This universal event statement is the distribution-level consequence of the
pointwise SCM compensation, with the original two-to-one prior bias retained.

It includes singleton targets, marginal conditioning events, and parity
events over arbitrary full observed alphabets.  It concerns the large model
alone; equality with a small-model conditioning denominator must still be
proved separately for the same countermodel pair. -/
theorem HedgeWitness.largeCarrierDefectParityModel_interventional_conditionOn_probVal_equiv
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (balance : Fin S.count) (inside : w.large balance = true)
    (intervention : (node : Fin S.count) -> Option (S.Value node)) (fixed : intervention balance ≠ none)
    (event : Event S.Assignment) (defect : Bool) :
    QProb.Equiv
      (((w.largeCarrierDefectParityModel rich).prior.conditionOn (hedgeDefectStratum G defect)
        (hedgeDefectPrior_stratum_positive G defect)).probVal
        (fun unit => event ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit)))
      ((w.largeCarrierDefectParityModel rich).prior.probVal
        (fun unit => event ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit))) := by
  apply hedgeDefectPrior_conditionOn_probVal_equiv_of_pair_compensation G
    (w.largeCarrierDefectCompensation balance inside)
  intro old
  have coupling := w.largeCarrierDefectParityModel_evalUnder_compensate_defect rich balance inside
    intervention fixed (hedgePairBitsOf G old) (hedgePrivateCoordinatesOf G old) false
  simpa only [hedgeLatentOfCoordinates_recover, Bool.not_false, hedgeLatentPairTranslation] using
    congrArg event coupling

/-- The original hedge action already intervenes on its large-forest seed.
Consequently its whole observed distribution is independent of the private
defect without any caller-supplied balancing vertex or restriction to sinks,
singleton actions, binary alphabets, or selected outcome events. -/
theorem HedgeWitness.largeCarrierDefectParityModel_doSecond_conditionOn_probVal_equiv
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (event : Event S.Assignment) (defect : Bool) :
    QProb.Equiv
      (((w.largeCarrierDefectParityModel rich).prior.conditionOn (hedgeDefectStratum G defect)
        (hedgeDefectPrior_stratum_positive G defect)).probVal
        (fun unit => event ((w.largeCarrierDefectParityModel rich).evalUnder
          (hedgeDoSecond rich q.action) unit)))
      ((w.largeCarrierDefectParityModel rich).prior.probVal
        (fun unit => event ((w.largeCarrierDefectParityModel rich).evalUnder
          (hedgeDoSecond rich q.action) unit))) := by
  apply w.largeCarrierDefectParityModel_interventional_conditionOn_probVal_equiv rich
    w.actionSeed w.actionSeed_in_large
  rw [hedgeDoSecond_of_true rich q.action w.actionSeed_in_action]
  exact Option.some_ne_none _

end Causality
end Thesis
