import Thesis.CausalTransport.HiddenDAGMechanismTableModels
import Thesis.Probability.FiniteProductSupport

namespace Thesis.Causality

open Probability

/-!
# A finite code-mechanism catalogue covering bounded representatives

Enumerate every bounded node/source cardinality vector, then every compatible
mechanism table at each shape. The list depends only on the fixed full graph,
public observed domains and target-list length. It does not depend on the
original model's hidden alphabets, equations, source denominators or weights.
The deliberately generous uniform node bound adds the public domain-size sum
to the hidden-value bound; no model-dependent observed-index choice is needed.

For every original model, the existing constructive bounded representation
provides an explicit entry in this list. The native table adapter reconstructs
that representative exactly, so its original observational and selected-target
preservation proofs still apply. This is finite coverage of alphabet shapes
and graph-compatible equations, not yet an exhaustive native-template checker:
the adapter still retains the base model's observed conversions and source law.
Enumerating/normalizing the finite observed conversions and connecting source
laws to independent rational-weight parameters are subsequent obligations.

The catalogue may include shapes with no compatible observed conversion or
normalized source law. Such extra raw entries do not invalidate coverage;
they must not be advertised as native causal models without those witnesses.
Finiteness is not a practical runtime guarantee or a bound on rational weights.
-/

namespace FiniteHiddenDAG

variable {S : ObservedSignature.{0}}

structure CodeAlphabetShape (H : FiniteHiddenDAG S) where
  nodeCard : Fin H.count → Nat
  sourceCard : Fin H.count → Nat

def cardinalityVectors (count bound : Nat) : List (Fin count → Nat) :=
  FiniteProduct.enumeration count (fun _ => Nat) (fun _ => List.range (bound + 1))

theorem cardinalityVectors_complete (count bound : Nat) (cards : Fin count → Nat)
    (bounded : ∀ node, cards node ≤ bound) : cards ∈ cardinalityVectors count bound :=
  FiniteProduct.enumeration_mem_of_coordinate_mem _ _ _ cards
    (fun node => List.mem_range.mpr (Nat.lt_succ_of_le (bounded node)))

def codeAlphabetShapes (H : FiniteHiddenDAG S) (nodeBound sourceBound : Nat) : List H.CodeAlphabetShape :=
  (cardinalityVectors H.count nodeBound).flatMap (fun nodes =>
    (cardinalityVectors H.count sourceBound).map (fun sources => ⟨nodes, sources⟩))

theorem codeAlphabetShapes_complete (H : FiniteHiddenDAG S) (nodeBound sourceBound : Nat) (shape : H.CodeAlphabetShape)
    (nodes : ∀ node, shape.nodeCard node ≤ nodeBound) (sources : ∀ node, shape.sourceCard node ≤ sourceBound) :
    shape ∈ H.codeAlphabetShapes nodeBound sourceBound := by
  cases shape with
  | mk nodeCard sourceCard =>
      exact List.mem_flatMap_of_mem (cardinalityVectors_complete _ _ nodeCard nodes)
        (List.mem_map_of_mem (f := fun sources => (⟨nodeCard, sources⟩ : H.CodeAlphabetShape))
          (cardinalityVectors_complete _ _ sourceCard sources))

structure CodeMechanismEntry (H : FiniteHiddenDAG S) where
  shape : H.CodeAlphabetShape
  tables : H.CodeMechanismTables shape.nodeCard shape.sourceCard

/-- Flatten the finite dependent family of table lists. No model-specific
equation, observational table or semantic certificate is an input. -/
def boundedMechanismCatalogue (H : FiniteHiddenDAG S) (nodeBound sourceBound : Nat) : List H.CodeMechanismEntry :=
  (H.codeAlphabetShapes nodeBound sourceBound).flatMap (fun shape =>
    (H.codeMechanismCatalogue shape.nodeCard shape.sourceCard).map (fun tables => ⟨shape, tables⟩))

theorem boundedMechanismCatalogue_complete (H : FiniteHiddenDAG S) (nodeBound sourceBound : Nat) (entry : H.CodeMechanismEntry)
    (nodes : ∀ node, entry.shape.nodeCard node ≤ nodeBound) (sources : ∀ node, entry.shape.sourceCard node ≤ sourceBound) :
    entry ∈ H.boundedMechanismCatalogue nodeBound sourceBound := by
  cases entry with
  | mk shape tables =>
      exact List.mem_flatMap_of_mem (H.codeAlphabetShapes_complete nodeBound sourceBound shape nodes sources)
        (List.mem_map_of_mem (f := fun listed => (⟨shape, listed⟩ : H.CodeMechanismEntry))
          (H.codeMechanismCatalogue_complete shape.nodeCard shape.sourceCard tables))

end FiniteHiddenDAG

namespace ObservedSignature

def cardinalityBudget (S : ObservedSignature) : Nat :=
  ((List.finRange S.count).map (fun index => (S.valueEnumeration index).length)).sum

private theorem member_le_natSum (values : List Nat) (value : Nat) (listed : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => cases listed
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp listed with equal | member
      · subst value
        exact Nat.le_add_right _ _
      · exact Nat.le_trans (inductionHypothesis member) (Nat.le_add_left _ _)

theorem valueCard_le_budget (S : ObservedSignature) (index : Fin S.count) :
    (S.valueEnumeration index).length ≤ S.cardinalityBudget :=
  member_le_natSum _ _ (List.mem_map_of_mem (f := fun index => (S.valueEnumeration index).length) (List.mem_finRange index))

end ObservedSignature

namespace FiniteHiddenDAGSCM

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

def representationSourceBound (S : ObservedSignature) (targets : Nat) : Nat :=
  S.assignmentEnumeration.length + targets + 1

def representationNodeBound (P : FiniteLatentProjection S) (targets : Nat) : Nat :=
  (targets + 1) * (representationSourceBound S targets) ^ P.hiddenDAG.count + S.cardinalityBudget

namespace BoundedRepresentation

variable {original : FiniteHiddenDAGSCM S P} {targets : List (NativeProbabilityQuery S)}

theorem nodeCard_bounded_uniformly (represented : BoundedRepresentation original targets) (node : Fin P.hiddenDAG.count) :
    represented.nodeCard node ≤ representationNodeBound P targets.length := by
  rcases P.hiddenDAG.node_classified node with hidden | ⟨index, same⟩
  · exact Nat.le_trans (represented.hidden_bounded node hidden) (Nat.le_add_right _ _)
  · rw [← same, represented.observed_card]
    exact Nat.le_trans (S.valueCard_le_budget index) (Nat.le_add_left _ _)

def catalogueEntry (represented : BoundedRepresentation original targets) : P.hiddenDAG.CodeMechanismEntry :=
  ⟨⟨represented.nodeCard, represented.sourceCard⟩, represented.mechanismTables⟩

/-- The list is fixed by the graph, public domains and target count. The
entry is constructed explicitly from the represented equations; it is not
selected from a proposition asserting that some representative must exist. -/
theorem catalogueEntry_mem (represented : BoundedRepresentation original targets) :
    represented.catalogueEntry ∈ P.hiddenDAG.boundedMechanismCatalogue
      (representationNodeBound P targets.length) (representationSourceBound S targets.length) :=
  P.hiddenDAG.boundedMechanismCatalogue_complete _ _ represented.catalogueEntry
    represented.nodeCard_bounded_uniformly represented.source_bounded

end BoundedRepresentation
end FiniteHiddenDAGSCM
end Thesis.Causality
