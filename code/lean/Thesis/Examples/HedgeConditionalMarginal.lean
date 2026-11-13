import Thesis.CausalTransport.HedgeConditionalMarginal
import Thesis.Examples.HedgeInterventionalProbability

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalInsideForest

open Probability
open HedgeWeightedTernaryIntervention (signature graph rich outcome)

/-!
# A nonbinary irreducible conditional with an internal conditioner

All three vertices of `A → B → Y` belong to one bidirected component.
The original conditional is `P(Y | do(A), B)`.  IDC cannot exchange `B`, and
joint ID fails on its numerator with retained node sets `{A,B,Y}` and
`{B,Y}`.  On those exact sets we construct and check the closed kept chain,
whose single common root is `Y`.

Thus the conditioner `B` is not outside either forest.  The old pointwise
outside-forest denominator argument cannot be applied.  The new marginal
comparison omits `Y` instead and supplies the actual denominator equality
for the same positive carrier pair that separates the numerator.  No exchange
trace or denominator-identifiability premise is supplied to the constructor.

Every observed alphabet has three values.  In addition to the complete
conditional countermodel, a direct cylinder check fixes `A` to the third
label and tests that label at `B`; neither intervention nor event is confined
to the two distinguished parity values.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def actionNode : Fin signature.count := ⟨0, by decide⟩
def conditioner : Fin signature.count := ⟨1, by decide⟩

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton conditioner
  action_outcome_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel
  action_condition_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel
  outcome_condition_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

def freeNodes : NodeSet signature := fun node => decide (0 < node.val)

/-! ## Actual exhausted IDC and joint-ID failure -/

private def failureTest (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed fail => NodeSet.equal fail.remaining NodeSet.full && NodeSet.equal fail.free freeNodes
  | _ => false

private theorem failureOfTest (result : IdentificationOutcome signature)
    (checked : failureTest result = true) : result = .failed ⟨NodeSet.full, freeNodes⟩ := by
  cases result with
  | identified _ => cases checked
  | unfinished => cases checked
  | failed fail =>
      have coordinates := Bool.and_eq_true_iff.mp checked
      have large := (NodeSet.equal_eq_true_iff _ _).mp coordinates.1
      have small := (NodeSet.equal_eq_true_iff _ _).mp coordinates.2
      cases fail with
      | mk remaining free =>
          cases large
          cases small
          rfl

/-- The only conditioner cannot be promoted to the action.  This is the
actual search result on the original graph, not an assumed terminal status. -/
theorem query_no_exchange : conditionalExchangeStep? graph query = none := by
  have checked : (conditionalExchangeStep? graph query).isNone = true := by decide +kernel
  cases result : conditionalExchangeStep? graph query with
  | none => rfl
  | some step =>
      rw [result] at checked
      cases checked

theorem query_joint_failed : identifyJointKernel graph query.jointNumerator =
    .failed ⟨NodeSet.full, freeNodes⟩ := failureOfTest _ (by decide +kernel)

theorem query_conditional_failed : identifyConditionalKernel graph query =
    .failed ⟨NodeSet.full, freeNodes⟩ := failureOfTest _ (by decide +kernel)

noncomputable def extraction := identifyJointKernelFailedHedge query.jointNumerator query_joint_failed

/-! ## Checked forests on the actual failure coordinates

The general extractor supplies the exact large/small node sets.  For the
semantic regression we supply a directly checked kept chain on those sets,
rather than normalizing the proof-bearing fuel induction to recover its
particular child map.  A hedge is a subgraph witness, so either presentation
is legitimate; no equality of their selected child maps is asserted. -/

def child : ForestChild signature := closedForestChild NodeSet.full freeNodes
def roots : NodeSet signature := keptSinks NodeSet.full child

private theorem roots_selected : NodeSet.Subset roots query.outcome := by
  change forall node : Fin signature.count, roots node = true -> query.outcome node = true
  decide +kernel

private theorem large_forest : CForest graph NodeSet.full roots child :=
  cForest_of_child graph NodeSet.full child (by decide +kernel) (by decide +kernel)

private theorem small_forest : CForest graph freeNodes roots (restrictChild freeNodes child) := by
  have sameRoots : keptSinks freeNodes (restrictChild freeNodes child) = roots :=
    (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)
  rw [← sameRoots]
  exact cForest_of_child graph freeNodes (restrictChild freeNodes child)
    (by decide +kernel) (by decide +kernel)

noncomputable def witness : HedgeWitness graph query.jointNumerator :=
  HedgeWitness.ofForests query.jointNumerator NodeSet.full freeNodes roots child
    large_forest small_forest (fun _node _selected => rfl) (by decide +kernel)
    ((NodeSet.disjointBool_eq_true_iff _ _).mp (by decide +kernel))
    (fun root selected => ⟨root,
      NodeSet.subset_union_left query.outcome query.condition root (roots_selected root selected),
      DirectedReachableBy.refl root⟩)

/-- Both checked forests retain the exact coordinates of the actual joint
failure.  The semantic constructor does not change the failed query or host. -/
theorem witness_matches_failure : witness.large = extraction.witness.large ∧
    witness.small = extraction.witness.small :=
  ⟨extraction.large_eq.symm, extraction.small_eq.symm⟩

/-- The checked child map is the chain, even though both `B` and `Y` occur
in the numerator.  There is no extra root at the conditioner. -/
theorem witness_child : witness.child = closedForestChild NodeSet.full freeNodes := rfl

theorem roots_in_outcome : NodeSet.Subset witness.roots query.outcome := by
  intro node root
  have noChild := ((witness.large_forest.roots_exact node).mp root).2
  rw [witness_child] at noChild
  have sinksAreOutcomes : forall node : Fin signature.count,
      closedForestChild NodeSet.full freeNodes node = none -> query.outcome node = true := by
    decide +kernel
  exact sinksAreOutcomes node noChild

/-- Both old geometric exclusions genuinely fail: the conditioner belongs
to the large forest and to the small forest of this failure-aligned hedge. -/
theorem conditioner_inside_both :
    witness.large conditioner = true ∧ witness.small conditioner = true := by
  decide +kernel

theorem condition_not_outside_large :
    Not (NodeSet.Disjoint query.condition witness.large) := by
  intro outside
  have absent := outside conditioner (by decide +kernel)
  exact Bool.false_ne_true (absent.symm.trans conditioner_inside_both.1)

/-! ## The original conditional countermodel, with no outside hypothesis -/

noncomputable def counterexample :=
  witness.positiveConditionalCounterexampleOfRootsSubsetOutcome rich roots_in_outcome

theorem original_query_not_identifiable :
    Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

/-- Numerator separation and denominator equality are used in the very
same carrier pair; the conditional conversion does not replace either SCM. -/
theorem left_unchanged : counterexample.left =
    witness.largeCarrierDefectParityModel rich := rfl

theorem right_unchanged : counterexample.right =
    witness.smallCarrierDefectParityModel rich := rfl

/-! ## Actual nonbinary marginal under a nonbinary intervention -/

def target : signature.Assignment := fun _ => ⟨2, by decide⟩

def intervention (node : Fin signature.count) : Option (signature.Value node) :=
  if node = actionNode then some (target node) else none

private theorem outcome_root : witness.roots outcome = true := by
  apply (witness.large_forest.roots_exact outcome).mpr
  constructor
  · rfl
  · rw [witness_child]
    rfl

/-- Full agreement at the action and conditioner, omitting only the common
root, has identical actual natural mass on both sides.  The target at the
fixed action is consistent and is outside both distinguished parity labels. -/
theorem nonbinary_cylinder_mass_equal :
    FiniteProbRecord.eventMass (witness.largeCarrierDefectParityModel rich).prior.atoms
        (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes outcome) target
          ((witness.largeCarrierDefectParityModel rich).evalUnder intervention unit)) =
      FiniteProbRecord.eventMass (witness.smallCarrierDefectParityModel rich).prior.atoms
        (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes outcome) target
          ((witness.smallCarrierDefectParityModel rich).evalUnder intervention unit)) :=
  witness.carrierDefectParityModels_agreesOn_rootOmitted_eventMass_eq rich
    outcome outcome_root intervention target

/-- Equality above is not just equality of two impossible events.  A full
target in a specified defect stratum has positive mass, and its inclusion
in the root-omitted cylinder transfers that strict positivity by monotonicity.
The second model has the same positive mass by the proved comparison. -/
theorem nonbinary_cylinder_mass_positive :
    0 < FiniteProbRecord.eventMass (witness.largeCarrierDefectParityModel rich).prior.atoms
      (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes outcome) target
        ((witness.largeCarrierDefectParityModel rich).evalUnder intervention unit)) := by
  have fixed : intervention actionNode ≠ none := Option.some_ne_none _
  have consistent : forall node value, intervention node = some value -> target node = value := by
    intro node value atNode
    by_cases same : node = actionNode
    · simp only [intervention, if_pos same] at atNode
      exact Option.some.inj atNode
    · simp only [intervention, if_neg same] at atNode
      cases atNode
  have positive := witness.largeCarrierDefectParityModel_interventional_target_defect_positive rich
    actionNode (by rfl) intervention fixed target consistent false
  apply Nat.lt_of_lt_of_le positive
  apply FiniteProbRecord.eventMass_mono
  intro unit selected
  have full := (Bool.and_eq_true_iff.mp selected).2
  have equal : (witness.largeCarrierDefectParityModel rich).evalUnder intervention unit = target :=
    of_decide_eq_true full
  rw [equal]
  exact Kernel.agreesOn_refl _ _

/-- A target disagreeing with the actual fixed action remains impossible.
The common-root marginal theorem retains this effectiveness constraint;
it does not treat intervened rows as unconstrained output coordinates. -/
def inconsistentTarget : signature.Assignment :=
  fun node => if node = actionNode then ⟨0, by decide⟩ else target node

theorem inconsistent_cylinder_masses_zero :
    FiniteProbRecord.eventMass (witness.largeCarrierDefectParityModel rich).prior.atoms
        (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes outcome) inconsistentTarget
          ((witness.largeCarrierDefectParityModel rich).evalUnder intervention unit)) = 0 ∧
      FiniteProbRecord.eventMass (witness.smallCarrierDefectParityModel rich).prior.atoms
        (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes outcome) inconsistentTarget
          ((witness.smallCarrierDefectParityModel rich).evalUnder intervention unit)) = 0 := by
  have impossible (unit) : Kernel.agreesOn (hedgeRootOmittedNodes outcome) inconsistentTarget
      ((witness.largeCarrierDefectParityModel rich).evalUnder intervention unit) = false := by
    apply Bool.eq_false_iff.mpr
    intro selected
    have atAction := (finAll_eq_true_iff _).mp selected actionNode
    have different : actionNode ≠ outcome := by decide +kernel
    simp only [hedgeRootOmittedNodes, decide_eq_true different, if_true] at atAction
    have equal := of_decide_eq_true atAction
    have effective := (witness.largeCarrierDefectParityModel rich).evalUnder_effectiveness
      intervention unit actionNode (target actionNode) (by rfl)
    rw [effective] at equal
    exact (by decide +kernel : target actionNode ≠ inconsistentTarget actionNode) equal
  have leftZero : FiniteProbRecord.eventMass (witness.largeCarrierDefectParityModel rich).prior.atoms
      (fun unit => Kernel.agreesOn (hedgeRootOmittedNodes outcome) inconsistentTarget
        ((witness.largeCarrierDefectParityModel rich).evalUnder intervention unit)) = 0 :=
    (FiniteProbRecord.eventMass_congr _ _ (fun _ => false) impossible).trans
      (FiniteProbRecord.eventMass_false _)
  have equal := witness.carrierDefectParityModels_agreesOn_rootOmitted_eventMass_eq rich
    outcome outcome_root intervention inconsistentTarget
  exact ⟨leftZero, equal.symm.trans leftZero⟩

end HedgeConditionalInsideForest

namespace HedgeConditionalSplitRoots

open HedgeMergedReadout (signature graph rich actionNode firstRoot secondRoot rootMask forestHost)

/-!
## Some common roots may themselves be conditioners

Retain the merging fixture's actual two-root hedge, but query
`P(R₁ | do(X), R₂)`.  The old roots-in-outcome condition is false because
`R₂` is a conditioner.  Both roots are in the numerator and `R₁` is an
outcome, so the stronger constructor applies.  Retargeting preserves both
forests and the kept-child map; it needs only reflexive root-to-numerator
routes.  The actual IDC and joint-ID failures are checked independently.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton firstRoot
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton secondRoot
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide +kernel)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide +kernel)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide +kernel)

private def failureTest (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed fail => NodeSet.equal fail.remaining forestHost && NodeSet.equal fail.free rootMask
  | _ => false

private theorem failureOfTest (result : IdentificationOutcome signature)
    (checked : failureTest result = true) : result = .failed ⟨forestHost, rootMask⟩ := by
  cases result with
  | identified _ => cases checked
  | unfinished => cases checked
  | failed fail =>
      have coordinates := Bool.and_eq_true_iff.mp checked
      have large := (NodeSet.equal_eq_true_iff _ _).mp coordinates.1
      have small := (NodeSet.equal_eq_true_iff _ _).mp coordinates.2
      cases fail with
      | mk remaining free =>
          cases large
          cases small
          rfl

theorem query_joint_failed : identifyJointKernel graph query.jointNumerator =
    .failed ⟨forestHost, rootMask⟩ := failureOfTest _ (by decide +kernel)

theorem query_conditional_failed : identifyConditionalKernel graph query =
    .failed ⟨forestHost, rootMask⟩ := failureOfTest _ (by decide +kernel)

theorem query_no_exchange : conditionalExchangeStep? graph query = none := by
  have checked : (conditionalExchangeStep? graph query).isNone = true := by decide +kernel
  cases result : conditionalExchangeStep? graph query with
  | none => rfl
  | some step =>
      rw [result] at checked
      cases checked

private theorem original_roots_in_numerator :
    NodeSet.Subset HedgeMergedReadout.extraction.witness.roots query.jointNumerator.outcome := by
  rw [HedgeMergedReadout.extracted_roots]
  change forall node : Fin signature.count, rootMask node = true -> query.jointNumerator.outcome node = true
  decide +kernel

/-- No forest or child map is replaced.  The already extracted two-root
hedge is retargeted to this numerator by reflexive routes from both roots. -/
noncomputable def witness : HedgeWitness graph query.jointNumerator :=
  HedgeMergedReadout.extraction.witness.retargetQuery query.jointNumerator
    ((NodeSet.meetsBool_eq_true_iff _ _).mpr
      HedgeMergedReadout.extraction.witness.large_meets_intervention)
    HedgeMergedReadout.extraction.witness.small_avoids_intervention
    (fun root selected => ⟨root, original_roots_in_numerator root selected,
      DirectedReachableBy.refl root⟩)

theorem witness_matches_failure : witness.large = forestHost ∧ witness.small = rootMask :=
  ⟨HedgeMergedReadout.extraction.large_eq, HedgeMergedReadout.extraction.small_eq⟩

theorem witness_roots : witness.roots = rootMask := HedgeMergedReadout.extracted_roots

theorem roots_in_numerator : NodeSet.Subset witness.roots query.jointNumerator.outcome :=
  original_roots_in_numerator

theorem roots_meet_outcome : NodeSet.meetsBool witness.roots query.outcome = true := by
  apply (NodeSet.meetsBool_eq_true_iff _ _).mpr
  refine ⟨firstRoot, ?_, by decide +kernel⟩
  rw [witness_roots]
  decide +kernel

/-- This is a strict enlargement of the queried-root family, not just a
second example satisfying the older roots-in-outcome premise. -/
theorem roots_not_subset_outcome : Not (NodeSet.Subset witness.roots query.outcome) := by
  intro included
  have selected : witness.roots secondRoot = true := by rw [witness_roots]; decide +kernel
  have absent : query.outcome secondRoot = false := by decide +kernel
  exact Bool.false_ne_true (absent.symm.trans (included secondRoot selected))

noncomputable def counterexample :=
  witness.positiveConditionalCounterexampleOfRootsSubsetNumeratorOfRootsMeetOutcome rich
    roots_in_numerator roots_meet_outcome

theorem original_query_not_identifiable :
    Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

theorem left_unchanged : counterexample.left = witness.largeCarrierDefectParityModel rich := rfl
theorem right_unchanged : counterexample.right = witness.smallCarrierDefectParityModel rich := rfl

end HedgeConditionalSplitRoots
end Examples
end Causality
end Thesis
