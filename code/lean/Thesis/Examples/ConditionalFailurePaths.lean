import Thesis.CausalTransport.ConditionalFailurePaths

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailurePaths

/-!
# Regression checks for constructive back-door path data

These fixtures test the graph ingredient, not a new completeness assumption.
The first query really fails conditional ID and retains a nonempty terminal
conditioner.  Its path avoids a nonempty action and starts at the conditioner
with an incoming observed arrow.  Further checks exercise a latent-pair first
edge, a collider activated by a conditioned descendant, singleton connections,
blocked noncolliders, and the empty-signature boundary.

An exhausted exchange search alone is not a countermodel: the action-free
latent-pair example is identifiable by ordinary conditioning.  It nevertheless
has the required back-door path.  This deliberately checks the distinction
between the new graph certificate and the still-open semantic existence lemma.

Path codes are compared instead of introducing a global decidable equality
instance for expanded vertices.  The shared code is already proved injective.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open PathSpecification

/-! ## An actual failure with a retained conditioner and a nonempty action -/

/-- `A(0) -> U(1)`, both `A,U -> Z(2),Y(3)`, and `A <-> U`.
The confounded effect on `U` is not adjustable by an unaffected observed
common cause.  Its two children give the back-door path `Z <- U -> Y`. -/
def forkSignature : ObservedSignature where
  count := 4
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 1) ∨ (parent.val < 2 ∧ 2 ≤ child.val))
  directed_earlier := by
    intro parent child edge
    have bounds := of_decide_eq_true edge
    omega

def forkGraph : ObservedGraph forkSignature where
  bidirected := fun left right => decide (left ≠ right ∧ left.val < 2 ∧ right.val < 2)
  bidirected_symmetric := by
    intro left right edge
    have parts := of_decide_eq_true edge
    exact decide_eq_true (show right ≠ left ∧ right.val < 2 ∧ left.val < 2 from
      ⟨Ne.symm parts.1, parts.2.2, parts.2.1⟩)
  bidirected_irreflexive := by intro node; simp

def actionNode : Fin forkSignature.count := ⟨0, by decide⟩
def commonCause : Fin forkSignature.count := ⟨1, by decide⟩
def conditioner : Fin forkSignature.count := ⟨2, by decide⟩
def outcomeNode : Fin forkSignature.count := ⟨3, by decide⟩

def forkQuery : ConditionalKernelQuery forkSignature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  condition := NodeSet.singleton conditioner
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  action_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

theorem fork_no_exchange : conditionalExchangeStep? forkGraph forkQuery = none := by decide +kernel

/-- The finite search returns the same observed fork in both side graphs.
The singleton outgoing cut never turns it into an outgoing first edge. -/
def forkBackdoor : ConditionalBackdoorPath forkGraph forkQuery conditioner :=
  .ofNoExchange forkGraph forkQuery fork_no_exchange conditioner (by decide +kernel)

theorem fork_path_codes : forkBackdoor.path.nodes.map SeparationNode.code = [2, 1, 3] := by
  decide +kernel

theorem fork_first_incoming : forkGraph.expandedMutilatedEdge
    (GraphMutilation.bar forkQuery.action) forkBackdoor.first (.observed conditioner) = true :=
  forkBackdoor.first_incoming

theorem fork_path_avoids_action (node : Fin forkSignature.count)
    (member : .observed node ∈ forkBackdoor.path.nodes) : forkQuery.action node = false :=
  forkBackdoor.action_false_of_mem node member

private def forkFailureTest (result : IdentificationOutcome forkSignature) : Bool :=
  match result with
  | .failed fail => NodeSet.equal fail.remaining (fun node => decide (node.val < 2)) &&
      NodeSet.equal fail.free (NodeSet.singleton commonCause)
  | _ => false

private theorem forkFailureOfTest (result : IdentificationOutcome forkSignature)
    (checked : forkFailureTest result = true) :
    result = .failed ⟨(fun node => decide (node.val < 2)), NodeSet.singleton commonCause⟩ := by
  cases result with
  | identified _ => cases checked
  | unfinished => cases checked
  | failed fail =>
      have parts := Bool.and_eq_true_iff.mp checked
      have large := (NodeSet.equal_eq_true_iff _ _).mp parts.1
      have small := (NodeSet.equal_eq_true_iff _ _).mp parts.2
      cases fail with
      | mk remaining free => cases large; cases small; rfl

theorem fork_failed : identifyConditionalKernel forkGraph forkQuery =
    .failed ⟨(fun node => decide (node.val < 2)), NodeSet.singleton commonCause⟩ :=
  forkFailureOfTest _ (by decide +kernel)

noncomputable def forkFailure := identifyConditionalKernelFailed forkQuery fork_failed

/-- This fixture does not test the terminal path API vacuously: the actual
extracted terminal still contains the queried conditioner. -/
theorem extracted_conditioner_retained : forkFailure.terminal.condition conditioner = true := by
  have terminal := identifyConditionalKernelFailed_terminal_of_no_exchange forkQuery
    fork_no_exchange fork_failed
  change (identifyConditionalKernelFailed forkQuery fork_failed).terminal.condition conditioner = true
  rw [terminal]
  decide +kernel

noncomputable def retainedBackdoor : ConditionalBackdoorPath forkGraph forkFailure.terminal conditioner :=
  forkFailure.backdoorPath conditioner extracted_conditioner_retained

/-- The public arbitrary-depth provenance API returns path data for every
conditioner of its own terminal, without a manually supplied graph witness. -/
noncomputable def extractedBackdoor (node : Fin forkSignature.count)
    (selected : forkFailure.terminal.condition node = true) :
    ConditionalBackdoorPath forkGraph forkFailure.terminal node :=
  forkFailure.backdoorPath node selected

/-! ## A bidirected first edge remains explicit latent data -/

def pairSignature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ edge; cases edge

def pairGraph : ObservedGraph pairSignature where
  bidirected := fun left right => decide (left ≠ right)
  bidirected_symmetric := by intro left right edge; simpa only [ne_comm] using edge
  bidirected_irreflexive := by intro node; simp

def pairConditioner : Fin pairSignature.count := ⟨0, by decide⟩
def pairOutcome : Fin pairSignature.count := ⟨1, by decide⟩

def pairQuery : ConditionalKernelQuery pairSignature where
  outcome := NodeSet.singleton pairOutcome
  action := NodeSet.empty
  condition := NodeSet.singleton pairConditioner
  action_outcome_disjoint := NodeSet.disjoint_empty_left _
  action_condition_disjoint := NodeSet.disjoint_empty_left _
  outcome_condition_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

theorem pair_no_exchange : conditionalExchangeStep? pairGraph pairQuery = none := by decide +kernel

def pairBackdoor : ConditionalBackdoorPath pairGraph pairQuery pairConditioner :=
  .ofNoExchange pairGraph pairQuery pair_no_exchange pairConditioner (by decide +kernel)

/-- Code `3` is the actual latent pair `(0,1)` in the two-node alphabet. -/
theorem pair_path_codes : pairBackdoor.path.nodes.map SeparationNode.code = [0, 3, 1] := by
  decide +kernel

/-- A back-door path by itself does not imply identification failure. -/
private def identifiedTest : IdentificationOutcome pairSignature -> Bool
  | .identified _ => true
  | _ => false

theorem pair_identified : identifiedTest (identifyConditionalKernel pairGraph pairQuery) = true := by
  decide +kernel

/-! ## Collider activation by a descendant, not by the collider itself -/

/-- `U(0) -> Z(1)`, `U -> C(3) <- Y(2)`, and `C -> D(4)`.
The remaining conditioner `D` activates `C` on the path from `Z` to `Y`. -/
def colliderSignature : ObservedSignature where
  count := 5
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ child.val = 1) ∨ (parent.val = 0 ∧ child.val = 3) ∨
      (parent.val = 2 ∧ child.val = 3) ∨ (parent.val = 3 ∧ child.val = 4))
  directed_earlier := by
    intro parent child edge
    have endpoints := of_decide_eq_true edge
    omega

def colliderGraph : ObservedGraph colliderSignature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ edge; cases edge
  bidirected_irreflexive := by intro _; rfl

def colliderConditioner : Fin colliderSignature.count := ⟨1, by decide⟩
def colliderOutcome : Fin colliderSignature.count := ⟨2, by decide⟩

def colliderQuery : ConditionalKernelQuery colliderSignature where
  outcome := NodeSet.singleton colliderOutcome
  action := NodeSet.empty
  condition := fun node => decide (node.val = 1 ∨ node.val = 4)
  action_outcome_disjoint := NodeSet.disjoint_empty_left _
  action_condition_disjoint := NodeSet.disjoint_empty_left _
  outcome_condition_disjoint := by
    apply (NodeSet.disjointBool_eq_true_iff _ _).mp
    decide +kernel

theorem collider_no_exchange : conditionalExchangeStep? colliderGraph colliderQuery = none := by
  decide +kernel

def colliderBackdoor : ConditionalBackdoorPath colliderGraph colliderQuery colliderConditioner :=
  .ofNoExchange colliderGraph colliderQuery collider_no_exchange colliderConditioner (by decide +kernel)

theorem collider_path_codes : colliderBackdoor.path.nodes.map SeparationNode.code = [1, 0, 3, 2] := by
  decide +kernel

/-- The path's collider is not itself among the given vertices; activation
really uses its conditioned descendant `D`, rather than a membership shortcut. -/
theorem collider_not_given : NodeSet.union colliderQuery.action
    (NodeSet.diff colliderQuery.condition (NodeSet.singleton colliderConditioner))
    ⟨3, by decide⟩ = false := by decide +kernel

/-! ## Rejected paths and finite boundary cases -/

/-- Conditioning the common cause blocks the observed fork. -/
theorem conditioned_fork_has_no_path : activeConnection? forkGraph
    (GraphMutilation.bar forkQuery.action) forkQuery.outcome forkQuery.condition
    (NodeSet.union forkQuery.action (NodeSet.singleton commonCause)) = none :=
  (activeConnection?_eq_none_iff_dSeparated _ _ _ _ _).mpr (by decide +kernel)

/-- Without `D` in the given set the same collider cannot be activated,
and the data search itself rejects every candidate path. -/
theorem inactive_collider_search_empty : (activeConnection? colliderGraph
    (GraphMutilation.none colliderSignature) (NodeSet.singleton colliderConditioner)
    (NodeSet.singleton colliderOutcome) NodeSet.empty).isNone = true := by decide +kernel

/-- Equal open endpoints have a genuine singleton path; simplicity does not
incorrectly force distinct endpoints in the general witness search. -/
theorem singleton_path_codes : (activeConnection? pairGraph (GraphMutilation.none pairSignature)
    (NodeSet.singleton pairOutcome) (NodeSet.singleton pairOutcome) NodeSet.empty).map
    (fun connection => connection.path.nodes.map SeparationNode.code) = some [1] := by
  decide +kernel

theorem conditioned_endpoint_search_empty : (activeConnection? pairGraph
    (GraphMutilation.none pairSignature) (NodeSet.singleton pairOutcome)
    (NodeSet.singleton pairOutcome) (NodeSet.singleton pairOutcome)).isNone = true := by
  decide +kernel

theorem empty_endpoint_has_no_path : activeConnection? pairGraph (GraphMutilation.none pairSignature)
    NodeSet.empty NodeSet.full NodeSet.empty = none := by decide +kernel

def emptySignature : ObservedSignature where
  count := 0
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ edge; cases edge

def emptyGraph : ObservedGraph emptySignature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ edge; cases edge
  bidirected_irreflexive := by intro _; rfl

theorem empty_signature_has_no_path : activeConnection? emptyGraph (GraphMutilation.none emptySignature)
    NodeSet.full NodeSet.full NodeSet.empty = none := rfl

end CurrentConditionalFailurePaths
end Examples
end Causality
end Thesis
