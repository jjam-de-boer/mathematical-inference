import Thesis.CausalTransport.HedgeConditionalCollider
import Thesis.CausalTransport.ConditionalFailurePaths

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalColliderSelectionRegression

open Probability

/-!
# Root-specific queried parents, selected without choice

The topological order is `U,V,A,R₁,R₂`.  The roots have incoming arrows
`U -> R₁`, `V -> R₂`, and `A -> R₁,R₂`; the nodes `A,R₁,R₂` form one
bidirected component.  All observed alphabets have three labels.  The actual
query is `P(U,V | do(A), R₁,R₂)`.

There is deliberately no queried outside parent pointing to both roots.
Consequently the earlier shared-parent wrapper cannot cover this geometry.
The root-specific constructor selects the source root by conditional
uniqueness, then finds that root's own queried parent by a Boolean finite
search.  Its availability premises are literal graph tests.  They contain
neither a chosen parent nor a semantic kernel gap.

The regression checks both parent-search results, the absence of a shared
parent, the original query's exhausted exchange search and actual ID failure,
and all fields of the resulting positive countermodel.  This removes the
shared-parent restriction; it does not remove the direct incoming-edge and
outside-forest restrictions of the universal conditional countermodel leaf.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## Distinct incoming-parent geometry on the original graph -/

def signature : ObservedSignature where
  count := 5
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 3) ∨ (parent.val = 1 ∧ child.val = 4) ∨
      (parent.val = 2 ∧ 3 ≤ child.val))
  directed_earlier := by intro parent child edge; have selected := of_decide_eq_true edge; omega

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right ∧ 2 ≤ left.val ∧ 2 ≤ right.val)
  bidirected_symmetric := by
    intro left right edge
    have selected := of_decide_eq_true edge
    exact decide_eq_true ⟨Ne.symm selected.1, selected.2.2, selected.2.1⟩
  bidirected_irreflexive := by intro node; simp only [ne_eq, not_true_eq_false, false_and, decide_false]

def firstParent : Fin signature.count := ⟨0, by decide⟩
def secondParent : Fin signature.count := ⟨1, by decide⟩
def actionNode : Fin signature.count := ⟨2, by decide⟩
def firstRoot : Fin signature.count := ⟨3, by decide⟩
def secondRoot : Fin signature.count := ⟨4, by decide⟩

def rootMask : NodeSet signature := NodeSet.union (NodeSet.singleton firstRoot) (NodeSet.singleton secondRoot)
def outcomeMask : NodeSet signature := NodeSet.union (NodeSet.singleton firstParent) (NodeSet.singleton secondParent)

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

def large : NodeSet signature := fun node => decide (2 ≤ node.val)
def child : ForestChild signature := fun node => if node = actionNode then some firstRoot else none
def selection : HedgeSelection signature := ⟨large, rootMask, child⟩

theorem hedge_tests : hedgeTestsHold graph query.jointNumerator selection = true := by decide +kernel

def witness : HedgeWitness graph query.jointNumerator :=
  hedgeWitness_of_sets graph query.jointNumerator selection hedge_tests

theorem roots_are_full_condition : witness.roots = query.condition :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

/-- The parent availability proof merely inspects the two root coordinates.
Each resulting Boolean search test is evaluated in the original signature. -/
theorem parents_available (root : Fin signature.count) (selected : witness.roots root = true) :
    finAny signature.count (HedgeConditionalRoot.incomingParentTest witness root) = true := by
  have selectedRoot : rootMask root = true := (congrFun roots_are_full_condition root).symm.trans selected
  change (decide (root = firstRoot) || decide (root = secondRoot)) = true at selectedRoot
  rcases Bool.or_eq_true_iff.mp selectedRoot with first | second
  · have same := of_decide_eq_true first
    subst root
    decide +kernel
  · have same := of_decide_eq_true second
    subst root
    decide +kernel

/-- Both searches really return their own eligible observed node; neither
result is a propositional existence witness supplied by the caller. -/
theorem parent_searches :
    (HedgeConditionalRoot.incomingParent witness firstRoot (by decide +kernel)).node = firstParent ∧
    (HedgeConditionalRoot.incomingParent witness secondRoot (by decide +kernel)).node = secondParent := by decide +kernel

theorem no_shared_parent :
    finAny signature.count (fun parent =>
      HedgeConditionalRoot.incomingParentTest witness firstRoot parent &&
      HedgeConditionalRoot.incomingParentTest witness secondRoot parent) = false := by decide +kernel

/-! ## The same original conditional query actually fails IDC -/

private def failureTest (result : IdentificationOutcome signature) : Bool :=
  match result with
  | .failed fail => NodeSet.equal fail.remaining large && NodeSet.equal fail.free rootMask
  | _ => false

private theorem failureOfTest (result : IdentificationOutcome signature) (checked : failureTest result = true) :
    result = .failed ⟨large, rootMask⟩ := by
  cases result with
  | identified _ => cases checked
  | unfinished => cases checked
  | failed fail =>
      have parts := Bool.and_eq_true_iff.mp checked
      have largeEq := (NodeSet.equal_eq_true_iff _ _).mp parts.1
      have rootsEq := (NodeSet.equal_eq_true_iff _ _).mp parts.2
      cases fail with
      | mk remaining free => cases largeEq; cases rootsEq; rfl

theorem no_exchange : conditionalExchangeStep? graph query = none := by decide +kernel

theorem original_query_failed : identifyConditionalKernel graph query = .failed ⟨large, rootMask⟩ :=
  failureOfTest _ (by decide +kernel)

/-! ## Complete positive countermodel fields from the root-specific wrapper -/

noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveConditionalCounterexampleOfRootSpecificParents rich roots_are_full_condition parents_available

theorem left_positive : ObservationallyPositive counterexample.left := counterexample.left_mem.2
theorem right_positive : ObservationallyPositive counterexample.right := counterexample.right_mem.2

theorem full_observational_equality : ObservationallyEquivalent counterexample.left counterexample.right :=
  counterexample.observationally_equal

theorem original_query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

end HedgeConditionalColliderSelectionRegression
end Examples
end Causality
end Thesis
