import Thesis.CausalTransport.HiddenDAGMechanismCatalogue
import Thesis.CausalTransport.FiniteValueEquivalenceCatalogue
import Thesis.Causality.HiddenDAGObservedIndex

namespace Thesis.Causality

open Probability

/-!
# Standalone finite native templates with independent rational source laws

A template contains a bounded alphabet/mechanism entry and genuine two-sided
observed-value conversions. Both pieces are enumerated from the fixed graph
and public signature, independently of an original model. Given normalized
finite rational factors on its private code types, `CodeNativeTemplate.model`
constructs the complete native SCM directly: canonical independent product
prior, graph-derived observed lookup, finite enumerations and table equations.
There is no base model or supplied semantic-transfer theorem in this input.

The factor records allow zero probabilities and arbitrary rational denominators.
They are parameters of a finite structural family, not elements of a finite
probability search. A zero-cardinality source has no normalized factor record;
such raw cardinality shapes cannot be instantiated by inventing a default law.
Observed conversions are checked on all declared values, retaining null action
targets. The separate native-law coverage proof connects original models to
this structural family; enumeration alone does not supply that correspondence.
-/

namespace FiniteHiddenDAG

variable {S : ObservedSignature.{0}}

abbrev CodeObservedConversions (H : FiniteHiddenDAG S) (nodeCard : Fin H.count → Nat) :=
  (index : Fin S.count) → ValueEquivalence (Fin (nodeCard (H.observedNode index))) (S.Value index)

def codeObservedConversionsCatalogue (H : FiniteHiddenDAG S) (nodeCard : Fin H.count → Nat) :
    List (H.CodeObservedConversions nodeCard) :=
  FiniteProduct.enumeration S.count
    (fun index => ValueEquivalence (Fin (nodeCard (H.observedNode index))) (S.Value index))
    (fun index => ValueEquivalenceCatalogue.catalogue _ (S.valueEnumeration index) (S.value_complete index))

theorem codeObservedConversionsCatalogue_complete (H : FiniteHiddenDAG S) (nodeCard : Fin H.count → Nat)
    (conversions : H.CodeObservedConversions nodeCard) : conversions ∈ H.codeObservedConversionsCatalogue nodeCard :=
  FiniteProduct.enumeration_complete _ _ _
    (fun index => ValueEquivalenceCatalogue.catalogue_complete _ _ (S.value_complete index)) conversions

structure CodeNativeTemplate (H : FiniteHiddenDAG S) where
  entry : H.CodeMechanismEntry
  observed : H.CodeObservedConversions entry.shape.nodeCard

def nativeTemplateCatalogue (H : FiniteHiddenDAG S) (nodeBound sourceBound : Nat) : List H.CodeNativeTemplate :=
  (H.boundedMechanismCatalogue nodeBound sourceBound).flatMap (fun entry =>
    (H.codeObservedConversionsCatalogue entry.shape.nodeCard).map (fun observed => ⟨entry, observed⟩))

theorem nativeTemplateCatalogue_complete (H : FiniteHiddenDAG S) (nodeBound sourceBound : Nat) (template : H.CodeNativeTemplate)
    (nodes : ∀ node, template.entry.shape.nodeCard node ≤ nodeBound)
    (sources : ∀ node, template.entry.shape.sourceCard node ≤ sourceBound) :
    template ∈ H.nativeTemplateCatalogue nodeBound sourceBound := by
  cases template with
  | mk entry observed =>
      exact List.mem_flatMap_of_mem (H.boundedMechanismCatalogue_complete nodeBound sourceBound entry nodes sources)
        (List.mem_map_of_mem (f := fun conversions => (⟨entry, conversions⟩ : H.CodeNativeTemplate))
          (H.codeObservedConversionsCatalogue_complete entry.shape.nodeCard observed))

namespace CodeNativeTemplate

variable {P : FiniteLatentProjection S}

/-- Instantiate a structural template from its actual rational source factors.
The independent joint prior is constructed, not provided as a semantic premise. -/
def model (template : P.hiddenDAG.CodeNativeTemplate)
    (factors : (node : Fin P.hiddenDAG.count) → FiniteProbRecord (Fin (template.entry.shape.sourceCard node))) :
    FiniteHiddenDAGSCM S P where
  NodeValue := P.hiddenDAG.CodeValues template.entry.shape.nodeCard
  nodeEnumeration := fun node => List.finRange (template.entry.shape.nodeCard node)
  node_complete := fun _ value => List.mem_finRange value
  nodeDecidableEq := fun _ => inferInstance
  observedEquiv := template.observed
  observedIndex := P.hiddenDAG.observedIndex
  observedIndex_observed := P.hiddenDAG.observedIndex_observed
  observedIndex_sound := P.hiddenDAG.observedIndex_sound
  hidden_has_no_observed_index := P.hiddenDAG.observedIndex_hidden
  Noise := fun node => Fin (template.entry.shape.sourceCard node)
  noiseEnumeration := fun node => List.finRange (template.entry.shape.sourceCard node)
  noise_complete := fun _ value => List.mem_finRange value
  noiseDecidableEq := fun _ => inferInstance
  factor := factors
  prior := FiniteProduct.record P.hiddenDAG.count _ factors
  product_law := FiniteProduct.record_rectangular_probVal P.hiddenDAG.count _ factors
  mechanism := P.hiddenDAG.lookupCodeMechanisms template.entry.shape.nodeCard template.entry.shape.sourceCard template.entry.tables

end CodeNativeTemplate
end FiniteHiddenDAG
end Thesis.Causality
