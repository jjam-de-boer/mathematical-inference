import Thesis.CausalTransport.HiddenDAGModel
import Thesis.Causality.HiddenDAGObservedIndex
import Thesis.Causality.LatentRootProjection
import Thesis.Probability.FiniteProductGrouping

namespace Thesis.Causality.LatentRootNative

open Probability

/-!
# Actual native realization of finite latent-root structural data

Place each old latent factor at its hidden root in the full root DAG. Reuse
the proved independent grouping construction with one owner per old root;
the observed nodes' private blocks are empty and deterministic. No default
noise value is chosen, and the actual joint law is the constructed product
of the actual block factors. Different roots remain independent; a root's
several child inputs remain the very same shared value.

Hidden endogenous values are their root's private block values. Observed
endogenous values keep the entire original public domain through two-sided
conversions, including null intervention targets. The explicit finite-sum
presentation supplies all enumerations and equality decisions. Mechanisms
read only the declared observed parents and incident hidden roots.

This module constructs the native record, not a semantic transfer interface.
The separate evaluation module proves the unit and probability correspondence
with the original root model before projection-wide coverage uses the result.
-/

universe u
variable {S : ObservedSignature.{u}} (original : ExactModel S)

abbrev Node := Fin (original.latent.count + S.count)

def rootNode (root : Fin original.latent.count) : Node original := LatentRootDAG.rootNode S original.latent.count root

def observedNode (node : Fin S.count) : Node original := LatentRootDAG.observedNode S original.latent.count node

def owner : Fin original.latent.count → Node original := rootNode original

abbrev Noise (node : Node original) := FiniteProductGrouping.Block original.latent.Value (owner original) node

def noiseEnumeration (node : Node original) : List (Noise original node) :=
  FiniteProductGrouping.blockEnumeration (owner original) original.latent.valueEnumeration node

theorem noise_complete (node : Node original) (noise : Noise original node) : noise ∈ noiseEnumeration original node :=
  FiniteProductGrouping.blockEnumeration_complete (owner original) original.latent.valueEnumeration original.latent.value_complete node noise

def noiseDecidableEq (node : Node original) : DecidableEq (Noise original node) :=
  FiniteProductGrouping.blockDecidableEq (owner original) original.latent.valueDecidableEq node

/-- The finite sum selects types, not values from propositional existence. -/
def NodeValue : Node original → Type u :=
  Fin.addCases (fun root => Noise original (rootNode original root)) S.Value

theorem nodeValue_root (root : Fin original.latent.count) :
    NodeValue original (rootNode original root) = Noise original (rootNode original root) := by
  simp only [NodeValue, rootNode, LatentRootDAG.rootNode, Fin.addCases_left]

theorem nodeValue_observed (node : Fin S.count) : NodeValue original (observedNode original node) = S.Value node := by
  simp only [NodeValue, observedNode, LatentRootDAG.observedNode, Fin.addCases_right]

def rootEquivalence (root : Fin original.latent.count) :
    ValueEquivalence (NodeValue original (rootNode original root)) (Noise original (rootNode original root)) := by
  rw [nodeValue_root]
  exact ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def observedEquivalence (node : Fin S.count) : ValueEquivalence (NodeValue original (observedNode original node)) (S.Value node) := by
  rw [nodeValue_observed]
  exact ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def nodeEnumeration : (node : Node original) → List (NodeValue original node) :=
  Fin.addCases
    (fun root => (noiseEnumeration original (rootNode original root)).map (rootEquivalence original root).backward)
    (fun node => (S.valueEnumeration node).map (observedEquivalence original node).backward)

theorem node_complete (node : Node original) (value : NodeValue original node) : value ∈ nodeEnumeration original node := by
  revert value
  refine Fin.addCases (fun root => ?_) (fun observed => ?_) node
  · intro value
    rw [nodeEnumeration, Fin.addCases_left]
    exact List.mem_map.mpr ⟨(rootEquivalence original root).forward value,
      noise_complete original _ _, (rootEquivalence original root).backward_forward value⟩
  · intro value
    rw [nodeEnumeration, Fin.addCases_right]
    exact List.mem_map.mpr ⟨(observedEquivalence original observed).forward value,
      S.value_complete observed _, (observedEquivalence original observed).backward_forward value⟩

def nodeDecidableEq : (node : Node original) → DecidableEq (NodeValue original node) :=
  Fin.addCases
    (fun root => by rw [nodeValue_root]; exact noiseDecidableEq original _)
    (fun observed => by rw [nodeValue_observed]; exact S.valueDecidableEq observed)

/-- Root incidence is retained, not replaced by a pair-root approximation. -/
def root_edge (root : Fin original.latent.count) (child : Fin S.count)
    (incident : original.latent.incident root child = true) :
    original.latent.rootProjection.hiddenDAG.edge (rootNode original root) (observedNode original child) = true := by
  change (LatentRootDAG.graph S original.latent.count original.latent.incident).edge
    (LatentRootDAG.rootNode S original.latent.count root) (LatentRootDAG.observedNode S original.latent.count child) = true
  rw [LatentRootDAG.graph_root_observed_edge]
  exact incident

def observed_edge (parent child : Fin S.count) (edge : S.directed parent child = true) :
    original.latent.rootProjection.hiddenDAG.edge (observedNode original parent) (observedNode original child) = true := by
  change (LatentRootDAG.graph S original.latent.count original.latent.incident).edge
    (LatentRootDAG.observedNode S original.latent.count parent) (LatentRootDAG.observedNode S original.latent.count child) = true
  rw [LatentRootDAG.graph_observed_edge]
  exact edge

def observedMechanism (child : Fin S.count)
    (parents : original.latent.rootProjection.hiddenDAG.ParentValues (NodeValue original) (observedNode original child)) :
    NodeValue original (observedNode original child) :=
  (observedEquivalence original child).backward
    (original.mechanism child
      (fun parent edge => (observedEquivalence original parent).forward
        (parents (observedNode original parent) (observed_edge original parent child edge)))
      (fun root incident => ((rootEquivalence original root).forward
        (parents (rootNode original root) (root_edge original root child incident))) root rfl))

def mechanism : (node : Node original) →
    original.latent.rootProjection.hiddenDAG.ParentValues (NodeValue original) node → Noise original node → NodeValue original node :=
  Fin.addCases
    (fun root _parents noise => (rootEquivalence original root).backward noise)
    (fun child parents _noise => observedMechanism original child parents)

/-- Every record field is constructed from the input root model and the
fixed root graph. No soundness or semantic preservation premise is requested. -/
def model : FiniteHiddenDAGSCM S original.latent.rootProjection where
  NodeValue := NodeValue original
  nodeEnumeration := nodeEnumeration original
  node_complete := node_complete original
  nodeDecidableEq := nodeDecidableEq original
  observedEquiv := observedEquivalence original
  observedIndex := original.latent.rootProjection.hiddenDAG.observedIndex
  observedIndex_observed := original.latent.rootProjection.hiddenDAG.observedIndex_observed
  observedIndex_sound := original.latent.rootProjection.hiddenDAG.observedIndex_sound
  hidden_has_no_observed_index := original.latent.rootProjection.hiddenDAG.observedIndex_hidden
  Noise := Noise original
  noiseEnumeration := noiseEnumeration original
  noise_complete := noise_complete original
  noiseDecidableEq := noiseDecidableEq original
  factor := FiniteProductGrouping.factor (owner original) original.factor
  prior := FiniteProductGrouping.prior (owner original) original.factor
  product_law := FiniteProductGrouping.product_law (owner original) original.factor
  mechanism := mechanism original

def decodeNoise (noise : (model original).NoiseAssignment) : original.latent.Assignment :=
  FiniteProductGrouping.decode (owner original) noise

end Thesis.Causality.LatentRootNative
