import Thesis.CausalTransport.HiddenDAGNativeTemplateCoverage
import Thesis.Probability.FiniteRecordCatalogue

namespace Thesis.Causality

open Probability

/-!
# A finite native-model catalogue with explicit rational denominator bounds

The structural catalogue already ranges over bounded alphabet shapes,
graph-compatible mechanism tables and complete observed-value conversions.
For each entry, enumerate every independent source law below a supplied
denominator bound using the actual finite-record catalogue. Every instance
constructs an actual native SCM, not a list of unverified numerical tables.

Coverage is semantic rather than literal record equality: arbitrary factor
records may repeat labels or contain zero-weight occurrences. Aggregating
their singleton masses yields a listed factor choice with the same original
denominators and the same whole product law. Structural evaluation is
unchanged, so every intervention and observed event is preserved.

The bounds here are explicit restrictions on the searched model class. The
earlier projection-wide compression theorem does not preserve a prescribed
denominator bound and must not be used to erase this restriction. This finite
catalogue does not decide unrestricted rational compatibility or search over
all denominator bounds with a proved stopping rule.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

structure NativeTemplateInstance (P : FiniteLatentProjection S) where
  template : P.hiddenDAG.CodeNativeTemplate
  factors : (node : Fin P.hiddenDAG.count) → FiniteProbRecord (Fin (template.entry.shape.sourceCard node))

namespace NativeTemplateInstance

def model (entry : NativeTemplateInstance P) : FiniteHiddenDAGSCM S P := entry.template.model entry.factors

def canonical (entry : NativeTemplateInstance P) : NativeTemplateInstance P :=
  ⟨entry.template, fun node => FiniteRecordCatalogue.canonical (entry.factors node)⟩

theorem canonical_factor_den (entry : NativeTemplateInstance P) (node : Fin P.hiddenDAG.count) :
    (entry.canonical.factors node).den = (entry.factors node).den := FiniteRecordCatalogue.canonical_den _

/-- Only the source records change; the native equations and public value
conversions are identical on every noise unit, including zero-mass units. -/
theorem canonical_evalObserved (entry : NativeTemplateInstance P) (intervention : HardIntervention S)
    (noise : entry.model.NoiseAssignment) :
    entry.canonical.model.evalObserved intervention noise = entry.model.evalObserved intervention noise := by
  let law : FiniteProduct.IndependentLaw entry.model.Noise :=
    ⟨entry.canonical.factors, entry.canonical.model.prior, entry.canonical.model.product_law⟩
  exact entry.model.withSourceLaw_evalObserved law intervention noise

theorem canonical_interventionalValue (entry : NativeTemplateInstance P) (intervention : HardIntervention S)
    (event : Event S.Assignment) :
    QProb.Equiv (entry.canonical.model.interventionalValue intervention event) (entry.model.interventionalValue intervention event) := by
  have units := entry.canonical.model.prior.probVal_congr _ _
    (fun noise => congrArg event (entry.canonical_evalObserved intervention noise))
  exact QProb.equiv_trans (entry.canonical.model.prior.map_probVal _ event)
    (QProb.equiv_trans units (QProb.equiv_trans
      (FiniteRecordCatalogue.canonicalProduct_probVal P.hiddenDAG.count entry.template.entry.shape.sourceCard entry.factors
        (fun noise => event (entry.model.evalObserved intervention noise)))
      (QProb.equiv_symm (entry.model.prior.map_probVal _ event))))

theorem canonical_observationalValue (entry : NativeTemplateInstance P) (event : Event S.Assignment) :
    QProb.Equiv (entry.canonical.model.observationalValue event) (entry.model.observationalValue event) :=
  entry.canonical_interventionalValue (HardIntervention.empty S) event

end NativeTemplateInstance

namespace FiniteLatentProjection

/-- Enumerate actual standalone instances, with no original model as an
input. Impossible empty source alphabets contribute no normalized choices. -/
def boundedNativeCatalogue (P : FiniteLatentProjection S) (nodeBound sourceBound denominatorBound : Nat) :
    List (NativeTemplateInstance P) :=
  (P.hiddenDAG.nativeTemplateCatalogue nodeBound sourceBound).flatMap (fun template =>
    (FiniteRecordCatalogue.factorCatalogue P.hiddenDAG.count template.entry.shape.sourceCard denominatorBound).map
      (fun factors => ⟨template, factors⟩))

theorem boundedNativeCatalogue_template_mem (P : FiniteLatentProjection S) (nodeBound sourceBound denominatorBound : Nat)
    (entry : NativeTemplateInstance P) (listed : entry ∈ P.boundedNativeCatalogue nodeBound sourceBound denominatorBound) :
    entry.template ∈ P.hiddenDAG.nativeTemplateCatalogue nodeBound sourceBound := by
  rcases List.mem_flatMap.mp listed with ⟨template, templateListed, factorListed⟩
  rcases List.mem_map.mp factorListed with ⟨factors, _, same⟩
  cases same
  exact templateListed

theorem boundedNativeCatalogue_factor_den (P : FiniteLatentProjection S) (nodeBound sourceBound denominatorBound : Nat)
    (entry : NativeTemplateInstance P) (listed : entry ∈ P.boundedNativeCatalogue nodeBound sourceBound denominatorBound)
    (node : Fin P.hiddenDAG.count) : (entry.factors node).den ≤ denominatorBound := by
  rcases List.mem_flatMap.mp listed with ⟨template, _, factorListed⟩
  rcases List.mem_map.mp factorListed with ⟨factors, factorsListed, same⟩
  cases same
  exact FiniteRecordCatalogue.factorCatalogue_den_le _ _ factors denominatorBound factorsListed node

/-- Every bounded factor choice on every listed template has a listed
canonical instance. All of its native causal probabilities are preserved by
`NativeTemplateInstance.canonical_interventionalValue`, independently of the
particular observational law later used to filter this catalogue. -/
theorem canonical_mem_boundedNativeCatalogue (P : FiniteLatentProjection S) (nodeBound sourceBound denominatorBound : Nat)
    (entry : NativeTemplateInstance P)
    (templateListed : entry.template ∈ P.hiddenDAG.nativeTemplateCatalogue nodeBound sourceBound)
    (denominators : ∀ node, (entry.factors node).den ≤ denominatorBound) :
    entry.canonical ∈ P.boundedNativeCatalogue nodeBound sourceBound denominatorBound :=
  List.mem_flatMap_of_mem templateListed
    (List.mem_map_of_mem (f := fun factors => (⟨entry.template, factors⟩ : NativeTemplateInstance P))
      (FiniteRecordCatalogue.canonicalFactors_mem _ _ entry.factors denominatorBound denominators))

/-- Numeric alphabet bounds cover every compatible mechanism and observed
conversion, not merely a selected collection of hand-written templates. -/
theorem canonical_mem_boundedNativeCatalogue_of_bounds (P : FiniteLatentProjection S)
    (nodeBound sourceBound denominatorBound : Nat) (entry : NativeTemplateInstance P)
    (nodes : ∀ node, entry.template.entry.shape.nodeCard node ≤ nodeBound)
    (sources : ∀ node, entry.template.entry.shape.sourceCard node ≤ sourceBound)
    (denominators : ∀ node, (entry.factors node).den ≤ denominatorBound) :
    entry.canonical ∈ P.boundedNativeCatalogue nodeBound sourceBound denominatorBound :=
  P.canonical_mem_boundedNativeCatalogue _ _ _ entry
    (P.hiddenDAG.nativeTemplateCatalogue_complete _ _ entry.template nodes sources) denominators

end FiniteLatentProjection
end Thesis.Causality
