import Thesis.CausalTransport.HedgeChannelPathBoundary
import Thesis.Examples.HedgeChannelPathInputs

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentActivePathBoundary

open PathSpecification Probability FiniteBooleanInteraction
open HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# Actual endpoint/collider conservation for installed path signals

The existing reversed-pair and observed-fork paths now instantiate the new
general graph boundary theorem.  Their empty collider masks leave precisely
the two endpoint bits; no fixture-specific balance premise is supplied.

The new three-valued path is `Z <- U -> C <- Y`, where `U` is the original
reserved input of `Z <-> C` and `C` is genuinely conditioned.  Its stored
latent label is reversed.  Both incident arrows enter `C`, so the selected
heads are exactly `Z,C`, not the queried endpoint `Y`.  The actual installed
rows are `Z xor U` and `C xor U xor Y`; their complete phase is `Z xor Y xor C`.
On the false-`C` cylinder this is the endpoint character.  The displayed
direction flips the same original reserved bit and `Y`, leaving only `Z`'s
selected row odd.  `Y`'s unselected own row is odd, guarding against selecting
every observed path vertex.

This checks actual collider terms and conditional cancellation, not only
collider-free paths.  It does not assert arbitrary-depth collider activation
assembly or integration with every mandatory Small row.
-/

namespace ReversedPair

open CurrentActivePathPairRoots

theorem general_endpoint_collider_boundary :
    ActivePathInput.observedBoundary graph cut actualPath.nodes =
      ActivePathInput.endpointColliderBoundary graph cut actualPath.nodes leftNode outcome :=
  ActivePathInput.observedBoundary_eq_endpointColliderBoundary actualPath (by decide +kernel)

theorem no_collider_rows (child : Fin signature.count) : ActivePathInput.colliderRows graph cut actualPath.nodes child = false := by
  decide +kernel +revert

theorem general_installed_phase (point : Cube graph) :
    ((LinearSignal.ofActivePath actualPath).forestPhase (ActivePathInput.headRows graph cut actualPath.nodes)).value point =
      (maskPhase _ (cubeMask graph (ActivePathInput.endpointColliderBoundary graph cut actualPath.nodes leftNode outcome))).value point :=
  LinearSignal.ofActivePath_forestPhase_endpointCollider actualPath (by decide +kernel) point

end ReversedPair

namespace ObservedFork

open CurrentHedgeChannelPathInputs.ObservedFork

theorem general_endpoint_collider_boundary :
    ActivePathInput.observedBoundary graph cut actualPath.nodes =
      ActivePathInput.endpointColliderBoundary graph cut actualPath.nodes source outcome :=
  ActivePathInput.observedBoundary_eq_endpointColliderBoundary actualPath (by decide +kernel)

theorem no_collider_rows (child : Fin signature.count) : ActivePathInput.colliderRows graph cut actualPath.nodes child = false := by
  decide +kernel +revert

theorem general_installed_phase (point : Cube graph) :
    (constructedSignal.forestPhase heads).value point =
      (maskPhase _ (cubeMask graph (ActivePathInput.endpointColliderBoundary graph cut actualPath.nodes source outcome))).value point :=
  LinearSignal.ofActivePath_forestPhase_endpointCollider actualPath (by decide +kernel) point

end ObservedFork

namespace ConditionedCollider

def signature : ObservedSignature where
  count := 3
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val = 1 ∧ child.val = 2)
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def pivot : Fin signature.count := ⟨0, by decide⟩
def outcome : Fin signature.count := ⟨1, by decide⟩
def collider : Fin signature.count := ⟨2, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun left right => decide ((left.val = 0 ∧ right.val = 2) ∨ (left.val = 2 ∧ right.val = 0))
  bidirected_symmetric := by
    intro left right edge
    have parts := of_decide_eq_true edge
    apply decide_eq_true
    rcases parts with forward | backward
    · exact Or.inr ⟨forward.2, forward.1⟩
    · exact Or.inl ⟨backward.2, backward.1⟩
  bidirected_irreflexive := by intro node; apply decide_eq_false; intro edge; rcases edge with forward | backward <;> omega

private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if equal : SeparationNode.beq left right = true then isTrue ((SeparationNode.beq_eq_true_iff left right).mp equal)
  else isFalse (fun same => equal ((SeparationNode.beq_eq_true_iff left right).mpr same))

def cut : GraphMutilation signature := .none signature
def given : NodeSet signature := NodeSet.singleton collider
def reversedPair : SeparationNode signature := .latentPair collider pivot

def actualPath : ActivePath graph cut given (.observed pivot) (.observed outcome) where
  nodes := [.observed pivot, reversedPair, .observed collider, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inr ?_, Or.inl ?_, Or.inr ?_, True.intro⟩ <;> decide +kernel
  source_open := rfl
  target_open := rfl
  internal_active := .step
    (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), rfl⟩)
    (.step (Or.inl ⟨⟨by decide +kernel, by decide +kernel⟩,
        by unfold ColliderActivated; decide +kernel⟩)
      (.pair (.observed collider) (.observed outcome)))

def signalData : LinearSignal graph := .ofActivePath actualPath
def heads : NodeSet signature := ActivePathInput.headRows graph cut actualPath.nodes
def endpoints : NodeSet signature := NodeSet.union (NodeSet.singleton pivot) (NodeSet.singleton outcome)

theorem actual_head_rows : heads pivot = true ∧ heads collider = true ∧ heads outcome = false := by decide +kernel

theorem actual_collider_rows : ActivePathInput.colliderRows graph cut actualPath.nodes = NodeSet.singleton collider := by
  funext child
  decide +kernel +revert

/-- This includes the genuine collider term at every point, including
assignments outside the conditioning cylinder and every latent bit value. -/
theorem general_installed_phase (point : Cube graph) :
    (signalData.forestPhase heads).value point =
      (maskPhase _ (cubeMask graph (ActivePathInput.endpointColliderBoundary graph cut actualPath.nodes pivot outcome))).value point :=
  LinearSignal.ofActivePath_forestPhase_endpointCollider actualPath (by decide +kernel) point

/-- The real conditioned collider coordinate is zero, so its derived term
vanishes and the actual installed phase is the endpoint character. -/
theorem conditioned_endpoint_phase (point : Cube graph) (conditioned : cubeSample graph point collider = false) :
    (signalData.forestPhase heads).value point = (maskPhase _ (cubeMask graph endpoints)).value point := by
  apply HomogeneousPhase.value_eq_of_basis _ _ (cubeMask graph given) (sample := point)
  · decide +kernel
  · intro coordinate fixed
    by_cases earlier : coordinate.val < pairRootCount graph.binary
    · have impossible : cubeMask graph given coordinate = false := by
        unfold cubeMask FiniteProduct.BooleanBlocks.join
        rw [dif_pos earlier]
      rw [impossible] at fixed
      cases fixed
    · let child : Fin signature.count := ⟨coordinate.val - pairRootCount graph.binary, by have bound := coordinate.isLt; omega⟩
      have embedded : Fin.natAdd (pairRootCount graph.binary) child = coordinate := by
        apply Fin.ext
        dsimp only [child, Fin.natAdd]
        omega
      have selected : given child = true := by
        rw [← embedded] at fixed
        change FiniteProduct.BooleanBlocks.rightBlock _ _ (cubeMask graph given) child = true at fixed
        simpa only [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join] using fixed
      have same := (NodeSet.singleton_eq_true_iff collider child).mp selected
      rw [← embedded]
      change cubeSample graph point child = false
      exact (congrArg (cubeSample graph point) same).trans conditioned

theorem endpoints_not_internal_colliders :
    ActivePathInput.colliderRows graph cut actualPath.nodes pivot = false ∧
    ActivePathInput.colliderRows graph cut actualPath.nodes outcome = false :=
  ⟨ActivePathInput.colliderRows_source_false actualPath, ActivePathInput.colliderRows_target_false actualPath⟩

def direction : Cube graph := joinCube graph (fun _ => true) (fun child => decide (child = outcome))

theorem actual_direction_rows : (signalData.rowPhase pivot).value direction = true ∧
    (signalData.rowPhase collider).value direction = false ∧ (signalData.rowPhase outcome).value direction = true ∧
    cubeSample graph direction collider = false := by decide +kernel

end ConditionedCollider
end CurrentActivePathBoundary
end Examples
end Causality
end Thesis
