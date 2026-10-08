import Thesis.CausalTransport.HedgeConditionalCollider
import Thesis.CausalTransport.ConditionalFailurePaths

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalColliderRegression

open Probability

/-!
# Original-query collider countermodels with two conditioned roots

The graph has topological order `U,A,R₁,R₂,E`.  Both roots have incoming
arrows from `U` and `A`, and `A,R₁,R₂` form one bidirected component.  The
extra outcome `E` is isolated.  The query is the actual conditional kernel
`P(U,E | do(A), R₁,R₂)`, not its singleton-outcome or singleton-conditioner
replacement.  Every observed node has three labels.

The hedge is supplied by its finite checked forest tests.  The semantic
constructor must select its own separated root and supported reference,
keep the other root's complete observed label as context, and restore the
extra outcome by conditional marginalization.  No modified-model kernel
gap, conditioning-marginal equality, or observational-law equality is
assumed.  The constructor returns all counterexample fields itself.

Both conditioners genuinely resist IDC exchange, so this is a conditional
failure fixture rather than an unrelated joint hedge.  Its incoming-parent
geometry is nevertheless only one covered terminal family, not a proof of
the universal conditional completeness leaf.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## The full nonbinary query and its two-root hedge -/

def signature : ObservedSignature where
  count := 5
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val < 2 ∧ 2 ≤ child.val ∧ child.val < 4)
  directed_earlier := by intro parent child edge; have selected := of_decide_eq_true edge; omega

def graph : ObservedGraph signature where
  bidirected := fun left right => decide
    (left ≠ right ∧ 1 ≤ left.val ∧ left.val < 4 ∧ 1 ≤ right.val ∧ right.val < 4)
  bidirected_symmetric := by
    intro left right edge
    have selected := of_decide_eq_true edge
    exact decide_eq_true ⟨Ne.symm selected.1, selected.2.2.2.1, selected.2.2.2.2,
      selected.2.1, selected.2.2.1⟩
  bidirected_irreflexive := by intro node; simp only [ne_eq, not_true_eq_false, false_and, decide_false]

def parent : Fin signature.count := ⟨0, by decide⟩
def actionNode : Fin signature.count := ⟨1, by decide⟩
def firstRoot : Fin signature.count := ⟨2, by decide⟩
def secondRoot : Fin signature.count := ⟨3, by decide⟩
def extraOutcome : Fin signature.count := ⟨4, by decide⟩

def rootMask : NodeSet signature := NodeSet.union (NodeSet.singleton firstRoot) (NodeSet.singleton secondRoot)
def outcomeMask : NodeSet signature := NodeSet.union (NodeSet.singleton parent) (NodeSet.singleton extraOutcome)

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

def large : NodeSet signature := fun node => decide (1 ≤ node.val ∧ node.val < 4)
def child : ForestChild signature := fun node => if node = actionNode then some firstRoot else none
def selection : HedgeSelection signature := ⟨large, rootMask, child⟩

theorem hedge_tests : hedgeTestsHold graph query.jointNumerator selection = true := by decide +kernel

def witness : HedgeWitness graph query.jointNumerator :=
  hedgeWitness_of_sets graph query.jointNumerator selection hedge_tests

theorem roots_are_full_condition : witness.roots = query.condition :=
  (NodeSet.equal_eq_true_iff _ _).mp (by decide +kernel)

theorem two_conditioned_roots : query.condition.members.length = 2 ∧
    query.condition firstRoot = true ∧ query.condition secondRoot = true := by decide +kernel

theorem additional_queried_outcome : query.outcome.members.length = 2 ∧
    query.outcome parent = true ∧ query.outcome extraOutcome = true := by decide +kernel

theorem roots_not_in_outcome : query.outcome firstRoot = false ∧ query.outcome secondRoot = false := by decide +kernel

theorem parent_outside : witness.large parent = false := by decide +kernel

theorem parent_edges (root : Fin signature.count) (selected : witness.roots root = true) :
    signature.directed parent root = true := by
  have selectedRoot : rootMask root = true := (congrFun roots_are_full_condition root).symm.trans selected
  have rootBounds : 2 ≤ root.val ∧ root.val < 4 := by
    change (decide (root = firstRoot) || decide (root = secondRoot)) = true at selectedRoot
    rcases Bool.or_eq_true_iff.mp selectedRoot with first | second
    · have same := of_decide_eq_true first
      subst root
      decide
    · have same := of_decide_eq_true second
      subst root
      decide
  exact decide_eq_true ⟨by decide, rootBounds⟩

/-! ## Failure of the original query, without changing its conditioner -/

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

/-! ## All semantic fields come from the arbitrary-root constructor -/

/-- The selected root is not named here.  The general finite selector and
context-aware collider bridge supply it, while the returned object still
refutes the complete two-outcome, two-conditioner query displayed above. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveConditionalCounterexampleOfRootCollider rich parent (by decide +kernel)
    roots_are_full_condition parent_outside parent_edges

theorem left_positive : ObservationallyPositive counterexample.left := counterexample.left_mem.2
theorem right_positive : ObservationallyPositive counterexample.right := counterexample.right_mem.2

/-- The unused third label is not merely declared in the signature: the
actual installed SCMs assign positive mass even to the complete all-third
cell.  This follows from the constructor's full-alphabet positivity theorem,
without reducing the augmented latent tables in this regression. -/
def thirdReference : signature.Assignment := fun _ => ⟨2, by decide⟩

theorem third_label_cell_positive :
    0 < (counterexample.left.observationalDist.probVal (FiniteProbRecord.singletonEvent thirdReference)).num ∧
    0 < (counterexample.right.observationalDist.probVal (FiniteProbRecord.singletonEvent thirdReference)).num :=
  ⟨left_positive thirdReference, right_positive thirdReference⟩

theorem full_observational_equality : ObservationallyEquivalent counterexample.left counterexample.right :=
  counterexample.observationally_equal

theorem original_query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

end HedgeConditionalColliderRegression
end Examples
end Causality
end Thesis
