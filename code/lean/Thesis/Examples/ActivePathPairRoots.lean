import Thesis.CausalTransport.ActivePathPairRoots
import Thesis.CausalTransport.HedgeChannelEnvironmentLinear

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentActivePathPairRoots

open Probability PathSpecification HedgeChannelInstallation
open HedgeChannelEnvironmentInstallation FiniteBooleanInteraction

/-!
# Reversed expanded labels still read one original reserved input

The three three-valued vertices are `L,R,Y`.  There is exactly one original
bidirected pair `L <-> R`, and the actual arrow is `R -> Y`.  The displayed
active path uses the *reversed* expanded label `latentPair R L` between `L`
and `R`.  The ordered-label companion has the same observed vertices.

Both actual path lookups select the same original root index.  The generic
alias-exclusion and canonical-label theorems certify that no path occurrence
is silently duplicated when the expanded label is mapped to that input.

The installed rows are `L xor U`, `R xor U`, and `Y xor R`, where `U` is
literally the input selected by the general path lookup.  Their full phase
is `L xor Y` at every cube point.  A direction flips that one reserved bit
and observed `R,Y`: only the source row is odd.  This checks actual shared
input cancellation and legal incident reads, rather than treating the two
expanded labels as independent latent coordinates or a new global switch.
-/

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

def leftNode : Fin signature.count := ⟨0, by decide⟩
def rightNode : Fin signature.count := ⟨1, by decide⟩
def outcome : Fin signature.count := ⟨2, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left.val + right.val = 1)
  bidirected_symmetric := by intro left right selected; simpa only [Nat.add_comm] using selected
  bidirected_irreflexive := by intro node; apply decide_eq_false; omega

private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if equal : SeparationNode.beq left right = true then isTrue ((SeparationNode.beq_eq_true_iff left right).mp equal)
  else isFalse (fun same => equal ((SeparationNode.beq_eq_true_iff left right).mpr same))

def cut : GraphMutilation signature := .none signature
def reversedPair : SeparationNode signature := .latentPair rightNode leftNode
def orderedPair : SeparationNode signature := .latentPair leftNode rightNode

def actualPath : ActivePath graph cut NodeSet.empty (.observed leftNode) (.observed outcome) where
  nodes := [.observed leftNode, reversedPair, .observed rightNode, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inr ?_, Or.inl ?_, Or.inl ?_, True.intro⟩ <;> decide +kernel
  source_open := rfl
  target_open := rfl
  internal_active := .step
    (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), rfl⟩)
    (.step (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), rfl⟩)
      (.pair (.observed rightNode) (.observed outcome)))

def orderedPath : ActivePath graph cut NodeSet.empty (.observed leftNode) (.observed outcome) where
  nodes := [.observed leftNode, orderedPair, .observed rightNode, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inr ?_, Or.inl ?_, Or.inl ?_, True.intro⟩ <;> decide +kernel
  source_open := rfl
  target_open := rfl
  internal_active := .step
    (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), rfl⟩)
    (.step (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), rfl⟩)
      (.pair (.observed rightNode) (.observed outcome)))

theorem actual_pair_member : .latentPair rightNode leftNode ∈ actualPath.nodes := by decide +kernel
theorem ordered_pair_member : .latentPair leftNode rightNode ∈ orderedPath.nodes := by decide +kernel

/-- The expanded reverse alias names one actual original input in `Type`. -/
def originalRoot : Fin (pairRootCount graph) := actualPath.pairRootOfLatent rightNode leftNode actual_pair_member
def orderedRoot : Fin (pairRootCount graph) := orderedPath.pairRootOfLatent leftNode rightNode ordered_pair_member

theorem both_labels_select_one_original_root : originalRoot = orderedRoot ∧ originalRoot.val = 0 := by decide +kernel

theorem reversed_label_cannot_duplicate_the_input : orderedPair ∉ actualPath.nodes :=
  actualPath.latentPair_swap_not_mem rightNode leftNode actual_pair_member

theorem actual_canonicalized_nodes_simple : (actualPath.nodes.map SeparationNode.canonicalPair).Nodup :=
  actualPath.canonicalPair_nodes_nodup

/-- The root is available at exactly its two original children, not at the
downstream queried outcome.  The positive incidences use the general adapter. -/
theorem actual_incident_reads :
    pairRootIncident graph originalRoot leftNode = true ∧ pairRootIncident graph originalRoot rightNode = true ∧
    pairRootIncident graph originalRoot outcome = false :=
  ⟨actualPath.pairRootOfLatent_incident_right rightNode leftNode actual_pair_member,
    actualPath.pairRootOfLatent_incident_left rightNode leftNode actual_pair_member, by decide +kernel⟩

def signalData : LinearSignal graph where
  parentMask := fun child parent => decide (child = outcome ∧ parent = rightNode)
  rootMask := fun child root => decide ((child = leftNode ∨ child = rightNode) ∧ root = originalRoot)

def endpoints : NodeSet signature := NodeSet.union (NodeSet.singleton leftNode) (NodeSet.singleton outcome)

/-- Whole-path phase conservation is checked on the tiny actual basis and
then proved for every cube point by homogeneity.  The two shared root reads
cancel because they are reads of the same original coordinate. -/
theorem complete_path_phase (point : Cube graph) :
    (signalData.forestPhase NodeSet.full).value point = (maskPhase _ (cubeMask graph endpoints)).value point :=
  HomogeneousPhase.value_eq_of_basis _ _ (fun _ => false) (by decide +kernel) point
    (by intro _ impossible; cases impossible)

def direction : Cube graph := joinCube graph (fun root => decide (root = originalRoot))
  (fun child => decide (child = rightNode ∨ child = outcome))

/-- The actual incident bit and downstream observed bits are flipped.
Only the source row is odd; both genuine later path rows are even. -/
theorem actual_direction_rows : (signalData.rowPhase leftNode).value direction = true ∧
    (signalData.rowPhase rightNode).value direction = false ∧ (signalData.rowPhase outcome).value direction = false := by
  decide +kernel

end CurrentActivePathPairRoots
end Examples
end Causality
end Thesis
