import Thesis.CausalTransport.ActivePathColliderRerouting

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentActivePathColliderRerouting

open PathSpecification

/-!
# Actual active detours at a conditioned return and an outcome endpoint

The old trail is `L(0) -> C(2) <- U(1) -> R(4) <- Y(3)`.
There is also a real directed edge `C -> R`, and `R -> Z(5)`.
With `R` conditioned, both original colliders are activated.  Replacing
`C <- U -> R` by `C -> R` removes `C`'s collider window, but retains
the conditioned collider at `R`.  Treating that return as an open
noncollider would be incorrect; the general constructor preserves its
incoming edge from `Y` and its activation certificate.

With only `Z` conditioned, `R` is an open endpoint of the truncated
trail `L -> C <- U -> R`.  The same constructor handles an empty
right suffix and returns `L -> C -> R` with no internal collider.

These are actual simple active paths and actual directed edges in a
three-valued observed signature, not countermodels or supplied completeness
assumptions.  Their score improvements test the graph-surgery stage which
will exclude returns to an optimal path.  Universal extraction of all local
detour certificates from a conditional activation forest remains separate.
-/

def signature : ObservedSignature where
  count := 6
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    (((parent.val = 0 ∨ parent.val = 1) ∧ child.val = 2) ∨
      ((parent.val = 1 ∨ parent.val = 2 ∨ parent.val = 3) ∧ child.val = 4) ∨
      (parent.val = 4 ∧ child.val = 5))
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def leftEndpoint : Fin signature.count := ⟨0, by decide⟩
def oldParent : Fin signature.count := ⟨1, by decide⟩
def sourceCollider : Fin signature.count := ⟨2, by decide⟩
def rightEndpoint : Fin signature.count := ⟨3, by decide⟩
def returned : Fin signature.count := ⟨4, by decide⟩
def evidence : Fin signature.count := ⟨5, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ edge; cases edge
  bidirected_irreflexive := fun _ => rfl

def mutilation : GraphMutilation signature := .none signature
def conditioned : NodeSet signature := NodeSet.singleton returned

/-- Only finite verified vertex equality is used to check displayed simple
lists.  This local instance does not introduce classical decidable equality. -/
private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if equal : SeparationNode.beq left right = true then
    isTrue ((SeparationNode.beq_eq_true_iff left right).mp equal)
  else isFalse (fun same => equal ((SeparationNode.beq_eq_true_iff left right).mpr same))

theorem return_activated : ColliderActivated graph mutilation conditioned (.observed returned) :=
  graph.ancestorOf_target mutilation conditioned (by decide +kernel)

theorem source_activated : ColliderActivated graph mutilation conditioned (.observed sourceCollider) :=
  graph.ancestorOf_prepend mutilation conditioned (by decide +kernel) return_activated

def oldPath : ActivePath graph mutilation conditioned (.observed leftEndpoint) (.observed rightEndpoint) where
  nodes := [.observed leftEndpoint, .observed sourceCollider, .observed oldParent,
    .observed returned, .observed rightEndpoint]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by
    refine ⟨Or.inl ?_, Or.inr ?_, Or.inl ?_, Or.inr ?_, True.intro⟩ <;> decide +kernel
  source_open := by decide +kernel
  target_open := by decide +kernel
  internal_active :=
    .step (Or.inl ⟨⟨by decide +kernel, by decide +kernel⟩, source_activated⟩)
      (.step (Or.inr ⟨graph.not_collider_of_outgoing mutilation (by decide +kernel), by unfold NonColliderOpen; decide +kernel⟩)
        (.step (Or.inl ⟨⟨by decide +kernel, by decide +kernel⟩, return_activated⟩)
          (.pair (.observed returned) (.observed rightEndpoint))))

theorem old_source_collider : colliderJoinBool graph mutilation [.observed leftEndpoint] (.observed sourceCollider)
    [.observed oldParent, .observed returned, .observed rightEndpoint] = true := by decide +kernel

theorem directed_bridge : Consecutive (fun parent child => graph.expandedMutilatedEdge mutilation parent child = true)
    [.observed sourceCollider, .observed returned] := by exact ⟨by decide +kernel, True.intro⟩

theorem bridge_simple : ([.observed sourceCollider, .observed returned] : List (SeparationNode signature)).Nodup :=
  by decide +kernel

theorem source_open : ObservedGraph.blockedBy conditioned (.observed sourceCollider) = false := by decide +kernel

private theorem empty_open (node : SeparationNode signature) (member : node ∈ ([] : List (SeparationNode signature))) :
    ObservedGraph.blockedBy conditioned node = false := False.elim (List.not_mem_nil member)

private theorem empty_avoids (node : SeparationNode signature)
    (member : node ∈ ([] : List (SeparationNode signature))) (_old : node ∈ oldPath.nodes) : False :=
  List.not_mem_nil member

def detour : ActivePath graph mutilation conditioned (.observed leftEndpoint) (.observed rightEndpoint) :=
  oldPath.ofDirectedColliderDetour [.observed leftEndpoint] [.observed oldParent] [] [.observed rightEndpoint]
    (.observed sourceCollider) (.observed returned) rfl old_source_collider directed_bridge bridge_simple
    source_open empty_open return_activated empty_avoids

theorem detour_nodes : detour.nodes =
    [.observed leftEndpoint, .observed sourceCollider, .observed returned, .observed rightEndpoint] :=
  oldPath.ofDirectedColliderDetour_nodes [.observed leftEndpoint] [.observed oldParent] [] [.observed rightEndpoint]
    (.observed sourceCollider) (.observed returned) rfl old_source_collider directed_bridge bridge_simple
    source_open empty_open return_activated empty_avoids

/-- `R` is genuinely conditioned, and remains a collider after the detour.
Its activity cannot be justified by an incorrect endpoint/noncollider opening. -/
theorem conditioned_return_retained :
    ObservedGraph.blockedBy conditioned (.observed returned) = true ∧
    IsCollider graph mutilation (.observed sourceCollider) (.observed returned) (.observed rightEndpoint) :=
  by unfold IsCollider; decide +kernel

theorem counts_and_ranks : colliderCount graph mutilation oldPath.nodes = 2 ∧
    colliderCount graph mutilation detour.nodes = 1 ∧ colliderRankSum graph mutilation oldPath.nodes = 6 ∧
    colliderRankSum graph mutilation detour.nodes = 4 := by
  rw [detour_nodes]
  decide +kernel

/-- Rank sum actually decreases in this fixture, but removing one collider
still strictly improves the primary objective, as the general theorem proves. -/
theorem detour_score_decreases :
    colliderNormalizationScore graph mutilation detour.nodes < colliderNormalizationScore graph mutilation oldPath.nodes :=
  oldPath.directedColliderDetour_score_lt [.observed leftEndpoint] [.observed oldParent] [] [.observed rightEndpoint]
    (.observed sourceCollider) (.observed returned) rfl old_source_collider directed_bridge bridge_simple
    source_open empty_open return_activated empty_avoids (by decide +kernel)

/-- The same actual surgery improves the reverse-oriented path.  Neither
its score nor its activity is selected by running a second optimization search. -/
theorem reverse_detour_score_decreases :
    colliderNormalizationScore graph mutilation detour.reverse.nodes <
      colliderNormalizationScore graph mutilation oldPath.reverse.nodes := by
  change colliderNormalizationScore graph mutilation detour.nodes.reverse <
    colliderNormalizationScore graph mutilation oldPath.nodes.reverse
  simpa only [colliderNormalizationScore_reverse] using detour_score_decreases

/-! ## A return at the open outcome endpoint -/

def endpointConditioned : NodeSet signature := NodeSet.singleton evidence

theorem endpoint_return_activated : ColliderActivated graph mutilation endpointConditioned (.observed returned) :=
  graph.ancestorOf_prepend mutilation endpointConditioned (middle := .observed evidence) (by decide +kernel)
    (graph.ancestorOf_target mutilation endpointConditioned (target := evidence) (by decide +kernel))

def endpointOldPath : ActivePath graph mutilation endpointConditioned (.observed leftEndpoint) (.observed returned) where
  nodes := [.observed leftEndpoint, .observed sourceCollider, .observed oldParent, .observed returned]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inl ?_, Or.inr ?_, Or.inl ?_, True.intro⟩ <;> decide +kernel
  source_open := by decide +kernel
  target_open := by decide +kernel
  internal_active := .step
    (Or.inl ⟨⟨by decide +kernel, by decide +kernel⟩,
      graph.ancestorOf_prepend mutilation endpointConditioned (by decide +kernel) endpoint_return_activated⟩)
    (.step (Or.inr ⟨graph.not_collider_of_outgoing mutilation (by decide +kernel), by unfold NonColliderOpen; decide +kernel⟩)
      (.pair (.observed oldParent) (.observed returned)))

def endpointDetour : ActivePath graph mutilation endpointConditioned (.observed leftEndpoint) (.observed returned) :=
  endpointOldPath.ofDirectedColliderDetour [.observed leftEndpoint] [.observed oldParent] [] []
    (.observed sourceCollider) (.observed returned) rfl (by decide +kernel) directed_bridge bridge_simple
    (by decide +kernel) (fun _ member => False.elim (List.not_mem_nil member)) endpoint_return_activated
    (fun _ member _old => List.not_mem_nil member)

/-- An empty right suffix is an actual outcome-endpoint case.  No return
window is invented at that endpoint, and both endpoint identities survive. -/
theorem endpoint_detour_codes : endpointDetour.nodes.map SeparationNode.code = [0, 2, 4] := by
  decide +kernel

theorem endpoint_detour_no_colliders : colliderCount graph mutilation endpointDetour.nodes = 0 := by
  decide +kernel

end CurrentActivePathColliderRerouting
end Examples
end Causality
end Thesis
