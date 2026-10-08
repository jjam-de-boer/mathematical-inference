import Thesis.CausalTransport.HedgeConditionalLatentCollider
import Thesis.CausalTransport.ConditionalFailurePaths

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalLatentColliderRegression

open Probability

/-!
# Two conditioned roots with distinct queried shared-latent readouts

The topological order is `U,V,A,R₁,R₂,E`.  The only observed arrows are
`A -> R₁,R₂`.  The large forest `A,R₁,R₂` is bidirected-connected, the two
roots are bidirected-connected, and the additional edges are `U <-> R₁`
and `V <-> R₂`.  The extra queried outcome `E` is isolated.  Every observed
alphabet has three labels.  The original query is
`P(U,V,E | do(A), R₁,R₂)`.

There is no observed queried-parent arrow into either root and no queried
outside node sharing a latent pair with both roots.  Thus neither the earlier
observed-arrow collider nor a single common shared-parent wrapper explains
this countermodel.  Conditional uniqueness selects its own separated root,
and the root-specific finite meeting search supplies that root's eligible
shared-latent readout.  The construction keeps the other root's entire label
and restores every additional outcome by conditional marginalization.

The original query genuinely fails IDC with both conditioners retained.
Its terminal failure host is larger than the displayed hedge's large forest;
the manually checked hedge need not be the exact forest returned by failure
extraction.  All semantic fields nevertheless concern the original query and
are returned by the general countermodel constructor, not assumed here.
This checks a new conditional failure family, not universal completeness.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## Nonbinary signature and the actual projected graph -/

def signature : ObservedSignature where
  count := 6
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val = 2 ∧ 3 ≤ child.val ∧ child.val < 5)
  directed_earlier := by intro parent child edge; have selected := of_decide_eq_true edge; omega

/-- An oriented presentation of the intended undirected incidences.  The
graph symmetrizes this literal mask, without adding an observed arrow. -/
private def pairMask (left right : Fin signature.count) : Bool :=
  decide ((2 ≤ left.val ∧ left.val < 5 ∧ 2 ≤ right.val ∧ right.val < 5) ∨
    (left.val = 0 ∧ right.val = 3) ∨ (left.val = 1 ∧ right.val = 4))

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right) && (pairMask left right || pairMask right left)
  bidirected_symmetric := by
    intro left right edge
    simpa only [ne_comm, Bool.or_comm] using edge
  bidirected_irreflexive := by
    intro node
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_and]

def firstParent : Fin signature.count := ⟨0, by decide⟩
def secondParent : Fin signature.count := ⟨1, by decide⟩
def actionNode : Fin signature.count := ⟨2, by decide⟩
def firstRoot : Fin signature.count := ⟨3, by decide⟩
def secondRoot : Fin signature.count := ⟨4, by decide⟩
def extraOutcome : Fin signature.count := ⟨5, by decide⟩

def rootMask : NodeSet signature := NodeSet.union (NodeSet.singleton firstRoot) (NodeSet.singleton secondRoot)
def outcomeMask : NodeSet signature := NodeSet.union
  (NodeSet.union (NodeSet.singleton firstParent) (NodeSet.singleton secondParent)) (NodeSet.singleton extraOutcome)

def query : ConditionalKernelQuery signature where
  outcome := outcomeMask
  action := NodeSet.singleton actionNode
  condition := rootMask
  action_outcome_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  action_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel
  outcome_condition_disjoint := by unfold NodeSet.Disjoint; decide +kernel

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => ⟨0, by decide⟩
  second := fun _ => ⟨1, by decide⟩
  first_enumerated := fun _ => List.mem_finRange _
  second_enumerated := fun _ => List.mem_finRange _
  different := by intro _ same; have values := congrArg Fin.val same; cases values

def large : NodeSet signature := fun node => decide (2 ≤ node.val ∧ node.val < 5)
def child : ForestChild signature := fun node => if node = actionNode then some firstRoot else none
def selection : HedgeSelection signature := ⟨large, rootMask, child⟩

theorem hedge_tests : hedgeTestsHold graph query.jointNumerator selection = true := by decide +kernel

def witness : HedgeWitness graph query.jointNumerator :=
  hedgeWitness_of_sets graph query.jointNumerator selection hedge_tests

theorem roots_are_full_condition : witness.roots = query.condition :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

/-! ## The shared-neighbour searches have genuinely different answers -/

theorem parents_available (root : Fin signature.count) (selected : witness.roots root = true) :
    NodeSet.meetsBool query.outcome (HedgeConditionalRoot.sharedLatentParentMask witness root) = true := by
  have selectedRoot : rootMask root = true := (congrFun roots_are_full_condition root).symm.trans selected
  change (decide (root = firstRoot) || decide (root = secondRoot)) = true at selectedRoot
  rcases Bool.or_eq_true_iff.mp selectedRoot with first | second
  · have same := of_decide_eq_true first
    subst root
    decide +kernel
  · have same := of_decide_eq_true second
    subst root
    decide +kernel

theorem parent_searches :
    (HedgeConditionalRoot.sharedLatentParent witness firstRoot (by decide +kernel)).node = firstParent ∧
    (HedgeConditionalRoot.sharedLatentParent witness secondRoot (by decide +kernel)).node = secondParent := by decide +kernel

theorem no_shared_parent : NodeSet.meetsBool query.outcome
    (NodeSet.inter (HedgeConditionalRoot.sharedLatentParentMask witness firstRoot)
      (HedgeConditionalRoot.sharedLatentParentMask witness secondRoot)) = false := by decide +kernel

/-- The installed channel must read its mask from a real shared latent input;
it cannot reuse an observed incoming arrow between these readout coordinates. -/
theorem no_queried_incoming_arrows :
    finAny signature.count (fun parent => query.outcome parent &&
      (signature.directed parent firstRoot || signature.directed parent secondRoot)) = false := by decide +kernel

theorem full_query_sizes : query.outcome.members.length = 3 ∧ query.condition.members.length = 2 := by decide +kernel

/-! ## Actual failure of the unchanged conditional kernel -/

def failureHost : NodeSet signature := fun node => decide (node.val < 5)
def failureFree : NodeSet signature := NodeSet.diff failureHost (NodeSet.singleton actionNode)

private def failureTest (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed fail => NodeSet.equal fail.remaining failureHost && NodeSet.equal fail.free failureFree
  | _ => false

private theorem failureOfTest (result : IdentificationOutcome signature) (checked : failureTest result = true) :
    result = .failed ⟨failureHost, failureFree⟩ := by
  cases result with
  | identified _ => cases checked
  | unfinished => cases checked
  | failed fail =>
      have parts := Bool.and_eq_true_iff.mp checked
      have hostEq := (NodeSet.equal_eq_true_iff _ _).mp parts.1
      have freeEq := (NodeSet.equal_eq_true_iff _ _).mp parts.2
      cases fail with
      | mk remaining free => cases hostEq; cases freeEq; rfl

theorem no_exchange : conditionalExchangeStep? graph query = none := by decide +kernel

theorem original_query_failed : identifyConditionalKernel graph query = .failed ⟨failureHost, failureFree⟩ :=
  failureOfTest _ (by decide +kernel)

/-! ## Actual positive SCMs and full original-query separation -/

/-- The root, its other-root context, and its readout neighbour are not
hard-coded in this semantic construction.  Their finite selectors supply
actual data and the resulting pair refutes the whole displayed query. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveConditionalCounterexampleOfRootSpecificLatentParents rich roots_are_full_condition parents_available

theorem left_positive : ObservationallyPositive counterexample.left := counterexample.left_mem.2
theorem right_positive : ObservationallyPositive counterexample.right := counterexample.right_mem.2

theorem left_compatible : Compatible counterexample.left graph := counterexample.left_mem.1
theorem right_compatible : Compatible counterexample.right graph := counterexample.right_mem.1

def thirdReference : signature.Assignment := fun _ => ⟨2, by decide⟩

/-- Both real augmented latent models support a full assignment at the third
observed label.  A binary bit-gap proof alone would not establish this fact. -/
theorem third_label_cell_positive :
    0 < (counterexample.left.observationalDist.probVal (FiniteProbRecord.singletonEvent thirdReference)).num ∧
    0 < (counterexample.right.observationalDist.probVal (FiniteProbRecord.singletonEvent thirdReference)).num :=
  ⟨left_positive thirdReference, right_positive thirdReference⟩

theorem full_observational_equality : ObservationallyEquivalent counterexample.left counterexample.right :=
  counterexample.observationally_equal

theorem original_query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

end HedgeConditionalLatentColliderRegression
end Examples
end Causality
end Thesis
