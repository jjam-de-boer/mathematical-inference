import Thesis.CausalTransport.HedgeConditionalColliderEntry

namespace Thesis
namespace Causality
namespace Examples
namespace ConditionalColliderEntryRegression

/-!
# A two-root hedge requiring different collider entry kinds

The topological order is `U,V,A,R₁,R₂,Y`.  The observed arrows are
`U -> R₁`, `A -> R₁,R₂`, and `U,V -> Y`.  The large forest `A,R₁,R₂`
is bidirected-connected, the two common roots are bidirected-connected,
and the extra shared-latent edge is `V <-> R₂`.  All alphabets have three
labels.  The original query is `P(Y | do(A), R₁,R₂)`.

The first root admits only the observed-parent entry through unqueried `U`;
the second admits only the shared-latent entry through unqueried `V`.
Both sources have a directed tail to the original outcome `Y`.  Consequently
neither uniform entry family applies, but the combined root-specific test
does.  The separated root still comes from conditional uniqueness, not from
choosing a root for convenient graph geometry.

This module checks the genuine hedge and finite graph eligibility facts.
The companion `ConditionalColliderEntry` constructs and checks the actual
positive countermodels in a separate small compiler process.  No expanded
latent d-separation matrix or exact IDC failure record is reduced here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signature : ObservedSignature where
  count := 6
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 3) ∨
      (parent.val = 2 ∧ 3 ≤ child.val ∧ child.val < 5) ∨
      (parent.val < 2 ∧ child.val = 5))
  directed_earlier := by intro parent child edge; have selected := of_decide_eq_true edge; omega

/-- Symmetrize only the displayed incidences.  The outside shared entry
does not add an observed parent arrow into the second conditioned root. -/
private def pairMask (left right : Fin signature.count) : Bool :=
  decide ((2 ≤ left.val ∧ left.val < 5 ∧ 2 ≤ right.val ∧ right.val < 5) ∨
    (left.val = 1 ∧ right.val = 4))

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right) && (pairMask left right || pairMask right left)
  bidirected_symmetric := by
    intro left right edge
    simpa only [ne_comm, Bool.or_comm] using edge
  bidirected_irreflexive := by
    intro node
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_and]

def observedParent : Fin signature.count := ⟨0, by decide⟩
def sharedParent : Fin signature.count := ⟨1, by decide⟩
def actionNode : Fin signature.count := ⟨2, by decide⟩
def firstRoot : Fin signature.count := ⟨3, by decide⟩
def secondRoot : Fin signature.count := ⟨4, by decide⟩
def outcome : Fin signature.count := ⟨5, by decide⟩

def rootMask : NodeSet signature := NodeSet.union (NodeSet.singleton firstRoot) (NodeSet.singleton secondRoot)

def query : ConditionalKernelQuery signature where
  outcome := NodeSet.singleton outcome
  action := NodeSet.singleton actionNode
  condition := rootMask
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
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

/-! ## The combined availability test is genuinely necessary -/

/-- Neither source is in the original queried outcome.  Both entry
constructors must therefore create their auxiliary singleton query rather
than restrict the original outcome to a queried incoming parent. -/
theorem entry_sources_not_queried :
    query.outcome observedParent = false ∧ query.outcome sharedParent = false := by decide +kernel

/-- The first root has observed entry only, the second shared-latent entry
only.  All four facts concern the actual finite source-and-tail searches. -/
theorem entry_kinds :
    NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.incomingRouteParentMask witness firstRoot) = true ∧
    NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.sharedLatentRouteParentMask witness firstRoot) = false ∧
    NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.incomingRouteParentMask witness secondRoot) = false ∧
    NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.sharedLatentRouteParentMask witness secondRoot) = true := by
  decide +kernel

theorem entries_available (root : Fin signature.count) (selected : witness.roots root = true) :
    HedgeConditionalRoot.colliderEntryRouteAvailable witness root = true := by
  have selectedRoot : rootMask root = true := (congrFun roots_are_full_condition root).symm.trans selected
  change (decide (root = firstRoot) || decide (root = secondRoot)) = true at selectedRoot
  rcases Bool.or_eq_true_iff.mp selectedRoot with first | second
  · have same := of_decide_eq_true first
    subst root
    exact Bool.or_eq_true_iff.mpr (Or.inl entry_kinds.1)
  · have same := of_decide_eq_true second
    subst root
    exact Bool.or_eq_true_iff.mpr (Or.inr entry_kinds.2.2.2)

/-- The old all-observed and all-shared availability premises both fail.
The new theorem is thus used on a genuinely larger root-specific family. -/
theorem no_uniform_entry_family : Not
    ((forall root, witness.roots root = true ->
      NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.incomingRouteParentMask witness root) = true) ∨
    (forall root, witness.roots root = true ->
      NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.sharedLatentRouteParentMask witness root) = true)) := by
  intro uniform
  rcases uniform with observed | shared
  · have impossible := observed secondRoot (by decide +kernel)
    rw [entry_kinds.2.2.1] at impossible
    cases impossible
  · have impossible := shared firstRoot (by decide +kernel)
    rw [entry_kinds.2.1] at impossible
    cases impossible

end ConditionalColliderEntryRegression
end Examples
end Causality
end Thesis
