import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Probability.FiniteRecordPresentation
import Thesis.Probability.FiniteEnumerationBounds

namespace Thesis.Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Explicit finite domains for retained native trajectories

Enumerate every declared noise assignment and evaluate each supplied hard
intervention, always including the factual intervention. At a hidden vertex
keep only the values reached by these trajectories. At an observed vertex
keep the entire old value domain, including permitted but factually null
intervention values. Sampling support is never substituted for that domain.

An explicit first atom of the normalized joint prior supplies a factual noise
assignment. Its evaluated values give defaults already inside the new domains,
including when the requested intervention list is empty. The head atom need
not have positive individual weight: it is used only as a declared noise unit,
not as evidence for a supported conditional. No choice principle is involved.

The resulting finite coding is a retraction on each retained value domain,
not a bijection of an old hidden ambient type. Total encoding sends other old
hidden values to the explicit default. Later evaluator simulation must prove
that this fallback is never used along the retained trajectories; counting
and coding alone are not yet a model-representation theorem.
-/

namespace FiniteHiddenDAGSCM

private theorem prior_atoms_ne_nil (model : FiniteHiddenDAGSCM S P) : model.prior.atoms ≠ [] := by
  intro empty
  have normalized := model.prior.total_mass
  rw [empty] at normalized
  exact Nat.ne_of_gt model.prior.den_pos normalized.symm

/-- Explicit finite data, not an inhabitant selected from an existential. -/
def defaultNoise (model : FiniteHiddenDAGSCM S P) : model.NoiseAssignment :=
  (model.prior.atoms.head (prior_atoms_ne_nil model)).1

def factualNodeValue (model : FiniteHiddenDAGSCM S P) (node : Fin P.hiddenDAG.count) : model.NodeValue node :=
  model.evalNode (HardIntervention.empty S) model.defaultNoise node

def noiseAssignments (model : FiniteHiddenDAGSCM S P) : List model.NoiseAssignment :=
  FiniteProduct.enumeration P.hiddenDAG.count model.Noise model.noiseEnumeration

theorem noiseAssignments_complete (model : FiniteHiddenDAGSCM S P) (noise : model.NoiseAssignment) :
    noise ∈ model.noiseAssignments :=
  FiniteProduct.enumeration_complete _ _ _ model.noise_complete noise

/-- Include the factual trajectories even if no extra actions are supplied.
Lists may repeat interventions; no equality decision on their function fields
is needed, and the bound honestly counts those repeated list positions. -/
def reachableValues (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) : List (model.NodeValue node) :=
  (HardIntervention.empty S :: actions).flatMap (fun intervention =>
    model.noiseAssignments.map (fun noise => model.evalNode intervention noise node))

theorem evalNode_mem_reachableValues (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (intervention : HardIntervention S) (listed : intervention ∈ HardIntervention.empty S :: actions)
    (noise : model.NoiseAssignment) (node : Fin P.hiddenDAG.count) :
    model.evalNode intervention noise node ∈ model.reachableValues actions node :=
  List.mem_flatMap_of_mem listed (List.mem_map_of_mem (model.noiseAssignments_complete noise))

theorem reachableValues_length (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) :
    (model.reachableValues actions node).length =
      (actions.length + 1) * FiniteProduct.natProduct P.hiddenDAG.count (fun index => (model.noiseEnumeration index).length) := by
  rw [reachableValues, length_flatMap_of_length _ _ model.noiseAssignments.length (fun _ => List.length_map _)]
  rw [List.length_cons, noiseAssignments, FiniteProduct.enumeration_length]

/-- Only hidden values may be discarded. The model's complete observed-node
enumerations already include every value corresponding to the public signature. -/
def retainedNodeValues (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) : List (model.NodeValue node) :=
  if P.hiddenDAG.hidden node then model.reachableValues actions node else model.nodeEnumeration node

theorem factualNodeValue_mem (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) : model.factualNodeValue node ∈ model.retainedNodeValues actions node := by
  unfold retainedNodeValues
  cases P.hiddenDAG.hidden node
  · exact model.node_complete node _
  · exact model.evalNode_mem_reachableValues actions _ List.mem_cons_self model.defaultNoise node

theorem evalNode_mem_retainedNodeValues (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (intervention : HardIntervention S) (listed : intervention ∈ HardIntervention.empty S :: actions)
    (noise : model.NoiseAssignment) (node : Fin P.hiddenDAG.count) :
    model.evalNode intervention noise node ∈ model.retainedNodeValues actions node := by
  unfold retainedNodeValues
  cases P.hiddenDAG.hidden node
  · exact model.node_complete node _
  · exact model.evalNode_mem_reachableValues actions intervention listed noise node

theorem observedValue_mem_retainedNodeValues (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (index : Fin S.count) (value : model.NodeValue (P.hiddenDAG.observedNode index)) :
    value ∈ model.retainedNodeValues actions (P.hiddenDAG.observedNode index) := by
  rw [retainedNodeValues, P.hiddenDAG.observed_not_hidden index]
  exact model.node_complete _ value

def valueWitness (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) :=
  FiniteProbRecord.domainWitness (model.retainedNodeValues actions node)

abbrev ValueCode (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) := Fin (model.valueWitness actions node).card

def decodeValue (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) (code : model.ValueCode actions node) : model.NodeValue node :=
  ((model.valueWitness actions node).decode code).val

/-- This total map is the inverse of decoding on retained values only.
The other branch is a real default, whose unreachability is a later obligation. -/
def encodeValue (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) (value : model.NodeValue node) : model.ValueCode actions node :=
  if listed : value ∈ model.retainedNodeValues actions node then
    (model.valueWitness actions node).encode ⟨value, listed⟩
  else (model.valueWitness actions node).encode ⟨model.factualNodeValue node, model.factualNodeValue_mem actions node⟩

theorem decodeValue_encodeValue (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) (value : model.NodeValue node)
    (listed : value ∈ model.retainedNodeValues actions node) :
    model.decodeValue actions node (model.encodeValue actions node value) = value := by
  rw [encodeValue, dif_pos listed]
  exact congrArg Subtype.val ((model.valueWitness actions node).decode_encode ⟨value, listed⟩)

theorem encodeValue_decodeValue (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) (code : model.ValueCode actions node) :
    model.encodeValue actions node (model.decodeValue actions node code) = code := by
  have listed := ((model.valueWitness actions node).decode code).property
  rw [encodeValue, dif_pos listed]
  exact (model.valueWitness actions node).encode_decode code

/-- The stated bound concerns actual `Fin` code types, not positive support.
The factual action is counted as the extra one in `actions.length + 1`. -/
theorem valueWitness_card_bound (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (node : Fin P.hiddenDAG.count) (hidden : P.hiddenDAG.hidden node = true) :
    (model.valueWitness actions node).card ≤
      (actions.length + 1) * FiniteProduct.natProduct P.hiddenDAG.count (fun index => (model.noiseEnumeration index).length) := by
  have bound := deduplicate_length_le (model.retainedNodeValues actions node).attach
  rw [List.length_attach] at bound
  change (model.valueWitness actions node).card ≤ (model.retainedNodeValues actions node).length at bound
  rw [retainedNodeValues, hidden, if_true, model.reachableValues_length actions node] at bound
  exact bound

theorem valueWitness_card_bound_of_noise_bound (model : FiniteHiddenDAGSCM S P) (actions : List (HardIntervention S))
    (bound : Nat) (bounded : ∀ node, (model.noiseEnumeration node).length ≤ bound)
    (node : Fin P.hiddenDAG.count) (hidden : P.hiddenDAG.hidden node = true) :
    (model.valueWitness actions node).card ≤ (actions.length + 1) * bound ^ P.hiddenDAG.count :=
  Nat.le_trans (model.valueWitness_card_bound actions node hidden)
    (Nat.mul_le_mul_left _ (FiniteProduct.natProduct_le_pow _ _ bound bounded))

end FiniteHiddenDAGSCM
end Thesis.Causality
