import Thesis.CausalTransport.HedgeChannelPathRows
import Thesis.Examples.ActivePathBoundary

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentHedgeChannelPathRows

open PathSpecification Probability FiniteBooleanInteraction
open HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# Whole-cube local-row tests, including two original reserved inputs

The existing observed-fork and conditioned-collider paths instantiate the
general local-row theorem at every cube point.  Thus the test checks a real
interpreter identity, not just parity at one finite assignment.  Omitted
fork and outgoing-endpoint rows are checked through the separate general
no-head theorem; they must not be forced even or added to the interaction.

The new path is `Z <- U₀ -> C <- U₁ -> Y`, with `C` conditioned and both
latent labels reversed.  The original graph reserves two distinct inputs,
one for each actual bidirected pair.  Its extra observed arrow `Y -> C`
is not consecutive on this path and is not read.  The actual collider row
reads both original inputs exactly once, which distinguishes the correct
local formula from duplicated aliases or an invented common switch.

All original observed alphabets have three values.  These regressions do
not supply the missing general activation/Small-forest countermodel family.
-/

namespace ObservedFork

open CurrentHedgeChannelPathInputs.ObservedFork

/-- The chain row reads its actual observed predecessor and its own bit;
its outgoing neighbour and ambient shortcut add no local contribution. -/
theorem internal_chain_row (point : Cube graph) :
    (constructedSignal.rowPhase middle).value point =
      Bool.xor (cubeSample graph point middle) (cubeSample graph point fork) := by
  calc
    _ = Bool.xor (cubeSample graph point middle)
        (Bool.xor (LinearSignal.incomingValue graph cut point (.observed fork) middle)
          (LinearSignal.incomingValue graph cut point (.observed outcome) middle)) :=
      LinearSignal.ofActivePath_rowPhase_internal_window actualPath [.observed source] []
        (.observed fork) (.observed outcome) middle rfl point
    _ = _ := by
      have incoming : graph.expandedMutilatedEdge cut (.observed fork) (.observed middle) = true := by decide +kernel
      have outgoing : graph.expandedMutilatedEdge cut (.observed outcome) (.observed middle) = false := by decide +kernel
      simp only [LinearSignal.incomingValue, LinearSignal.expandedInput, incoming, outgoing,
        Bool.true_and, Bool.false_and, Bool.xor_false]

/-- The omitted fork's own bit remains visible in its row.  The general
theorem, not a pointwise cube reduction, explains why this row may be odd. -/
theorem omitted_fork_row (point : Cube graph) :
    (constructedSignal.rowPhase fork).value point = cubeSample graph point fork :=
  LinearSignal.ofActivePath_rowPhase_of_not_head actualPath fork (by decide +kernel) point

end ObservedFork

namespace ConditionedCollider

open CurrentActivePathBoundary.ConditionedCollider

/-- One genuine reserved input and one observed parent enter the actual
conditioned collider.  The reversed label still reads its original root. -/
theorem mixed_collider_row (point : Cube graph) :
    (signalData.rowPhase collider).value point = Bool.xor (cubeSample graph point collider)
      (Bool.xor (cubeEnvironment graph point ⟨0, by decide +kernel⟩) (cubeSample graph point outcome)) := by
  calc
    _ = Bool.xor (cubeSample graph point collider)
        (Bool.xor (LinearSignal.incomingValue graph cut point reversedPair collider)
          (LinearSignal.incomingValue graph cut point (.observed outcome) collider)) :=
      LinearSignal.ofActivePath_rowPhase_internal_window actualPath [.observed pivot] []
        reversedPair (.observed outcome) collider rfl point
    _ = _ := rfl

/-- The endpoint with an outgoing path arrow is not selected.  Its own row
is not part of the collider interaction and is not asserted to be even. -/
theorem omitted_outcome_row (point : Cube graph) :
    (signalData.rowPhase outcome).value point = cubeSample graph point outcome :=
  LinearSignal.ofActivePath_rowPhase_of_not_head actualPath outcome (by decide +kernel) point

end ConditionedCollider

namespace DoubleLatentCollider

-- Reuse the genuinely three-valued signature and its legal arrow Y -> C.
-- Only the observed graph's reserved-pair classifier changes.  The added
-- observed arrow is deliberately off the path and must not be installed.
abbrev signature := CurrentActivePathBoundary.ConditionedCollider.signature
abbrev pivot := CurrentActivePathBoundary.ConditionedCollider.pivot
abbrev outcome := CurrentActivePathBoundary.ConditionedCollider.outcome
abbrev collider := CurrentActivePathBoundary.ConditionedCollider.collider

def graph : ObservedGraph signature where
  bidirected := fun left right => decide
    (((left.val = 0 ∨ left.val = 1) ∧ right.val = 2) ∨
      (left.val = 2 ∧ (right.val = 0 ∨ right.val = 1)))
  bidirected_symmetric := by
    intro left right edge
    have pairs := of_decide_eq_true edge
    apply decide_eq_true
    rcases pairs with forward | backward
    · exact Or.inr ⟨forward.2, forward.1⟩
    · exact Or.inl ⟨backward.2, backward.1⟩
  bidirected_irreflexive := by
    intro child
    apply decide_eq_false
    intro pair
    rcases pair with forward | backward
    · rcases forward.1 with zero | one <;> omega
    · rcases backward.2 with zero | one <;> omega

private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if equal : SeparationNode.beq left right = true then isTrue ((SeparationNode.beq_eq_true_iff left right).mp equal)
  else isFalse (fun same => equal ((SeparationNode.beq_eq_true_iff left right).mpr same))

def cut : GraphMutilation signature := .none signature
def given : NodeSet signature := NodeSet.singleton collider
def firstPair : SeparationNode signature := .latentPair collider pivot
def secondPair : SeparationNode signature := .latentPair collider outcome

def actualPath : ActivePath graph cut given (.observed pivot) (.observed outcome) where
  nodes := [.observed pivot, firstPair, .observed collider, secondPair, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inr ?_, Or.inl ?_, Or.inr ?_, Or.inl ?_, True.intro⟩ <;> decide +kernel
  source_open := rfl
  target_open := rfl
  internal_active := .step
    (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), rfl⟩)
    (.step (Or.inl ⟨⟨by decide +kernel, by decide +kernel⟩,
        by unfold ColliderActivated; decide +kernel⟩)
      (.step (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), rfl⟩)
        (.pair secondPair (.observed outcome))))

def signalData : LinearSignal graph := .ofActivePath actualPath
def heads : NodeSet signature := ActivePathInput.headRows graph cut actualPath.nodes
def firstRoot : Fin (pairRootCount graph.binary) := ⟨0, by decide +kernel⟩
def secondRoot : Fin (pairRootCount graph.binary) := ⟨1, by decide +kernel⟩

/-- The original enumeration, rather than a hypothetical path-position
enumeration, contains exactly the two distinct reserved coordinates. -/
theorem original_roots_are_distinct : pairRootCount graph.binary = 2 ∧ firstRoot ≠ secondRoot := by
  decide +kernel

/-- The actual collider uses both roots; the endpoint rows use their own
incident root only.  Its off-path observed parent is available but ignored. -/
theorem actual_local_masks : signalData.rootMask collider firstRoot = true ∧
    signalData.rootMask collider secondRoot = true ∧ signalData.rootMask pivot secondRoot = false ∧
    signalData.rootMask outcome firstRoot = false ∧ signature.directed outcome collider = true ∧
    signalData.parentMask collider outcome = false := by decide +kernel

/-- The general row theorem retains both original coordinates independently
at every assignment.  No common-switch equality is assumed in this identity. -/
theorem two_original_inputs_row (point : Cube graph) :
    (signalData.rowPhase collider).value point = Bool.xor (cubeSample graph point collider)
      (Bool.xor (cubeEnvironment graph point firstRoot) (cubeEnvironment graph point secondRoot)) := by
  calc
    _ = Bool.xor (cubeSample graph point collider)
        (Bool.xor (LinearSignal.incomingValue graph cut point firstPair collider)
          (LinearSignal.incomingValue graph cut point secondPair collider)) :=
      LinearSignal.ofActivePath_rowPhase_internal_window actualPath [.observed pivot] [.observed outcome]
        firstPair secondPair collider rfl point
    _ = _ := rfl

/-- Equal values of the two real reserved coordinates cancel at a false
collider bit.  This follows from the whole-cube row identity above. -/
theorem collider_even_on_equal_inputs (point : Cube graph)
    (ownZero : cubeSample graph point collider = false)
    (sameInputs : cubeEnvironment graph point firstRoot = cubeEnvironment graph point secondRoot) :
    (signalData.rowPhase collider).value point = false := by
  rw [two_original_inputs_row, ownZero, sameInputs, Bool.xor_self, Bool.false_xor]

def direction : Cube graph := joinCube graph (fun _ => true) (fun child => decide (child = outcome))

/-- In this concrete genuinely conditioned path all three rows are heads,
and the two distinct reserved bits leave exactly the source row odd.
This is a regression, not the still-open universal supported-direction proof. -/
theorem actual_direction_parity : heads pivot = true ∧ heads collider = true ∧ heads outcome = true ∧
    (signalData.rowPhase pivot).value direction = true ∧ (signalData.rowPhase collider).value direction = false ∧
    (signalData.rowPhase outcome).value direction = false ∧ cubeSample graph direction collider = false := by
  decide +kernel

end DoubleLatentCollider
end CurrentHedgeChannelPathRows
end Examples
end Causality
end Thesis
