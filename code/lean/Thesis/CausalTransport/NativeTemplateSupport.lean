import Thesis.CausalTransport.BoundedNativeCatalogue
import Thesis.CausalTransport.NativeSupportSemantics
import Thesis.Probability.FiniteSupportCatalogue
import Thesis.Probability.FiniteProductSupportLaw

namespace Thesis.Causality

open Probability

/-!
# Support-preserving reweighting of actual native structural templates

Keep a standalone template's equations, observed conversions and complete
code alphabets fixed. Replacing its independent factors by any records with
the same source supports preserves every interventional event's positivity.
The evaluator proof retains even the zero-mass noise units; the product-law
proof then identifies exactly which units can contribute positive event mass.

Uniform support factors give actual listed native models in a finite support
catalogue. This uses the existing native-instance data type but *not* the
bounded numerical catalogue's denominator restriction. Only zero/positivity
and partial-expression support are retained, not numerical probabilities.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

namespace FiniteHiddenDAG.CodeNativeTemplate

theorem reweight_evalObserved (template : P.hiddenDAG.CodeNativeTemplate)
    (left right : (source : Fin P.hiddenDAG.count) → FiniteProbRecord (Fin (template.entry.shape.sourceCard source)))
    (intervention : HardIntervention S) (noise : (template.model left).NoiseAssignment) :
    (template.model left).evalObserved intervention noise = (template.model right).evalObserved intervention noise := by
  let law : FiniteProduct.IndependentLaw (template.model right).Noise :=
    ⟨left, (template.model left).prior, (template.model left).product_law⟩
  exact (template.model right).withSourceLaw_evalObserved law intervention noise

/-- All hard interventions and all observed events, not merely rectangles
or the factual marginal, retain exactly the same positive support. -/
theorem supportAgreement_of_factor_support_eq (template : P.hiddenDAG.CodeNativeTemplate)
    (left right : (source : Fin P.hiddenDAG.count) → FiniteProbRecord (Fin (template.entry.shape.sourceCard source)))
    (same : ∀ source, (left source).support = (right source).support) :
    CausalSupportAgreement (template.model left) (template.model right) := by
  intro intervention event
  change (((template.model left).prior).map ((template.model left).evalObserved intervention)).EventPositive event ↔
    (((template.model right).prior).map ((template.model right).evalObserved intervention)).EventPositive event
  rw [FiniteProbRecord.map_eventPositive_iff, FiniteProbRecord.map_eventPositive_iff]
  have sameEvent :
      (fun noise => event ((template.model left).evalObserved intervention noise)) =
        (fun noise => event ((template.model right).evalObserved intervention noise)) :=
    funext (fun noise => congrArg event (template.reweight_evalObserved left right intervention noise))
  rw [sameEvent]
  exact FiniteProduct.record_eventPositive_iff_of_factor_support_eq left right same _

end FiniteHiddenDAG.CodeNativeTemplate

namespace NativeTemplateInstance

def uniformSupport (entry : NativeTemplateInstance P) : NativeTemplateInstance P :=
  ⟨entry.template, fun source => FiniteSupportCatalogue.uniformSupport (entry.factors source)⟩

theorem uniformSupport_agreement (entry : NativeTemplateInstance P) :
    CausalSupportAgreement entry.uniformSupport.model entry.model :=
  entry.template.supportAgreement_of_factor_support_eq _ _
    (fun source => FiniteSupportCatalogue.uniformSupport_support (entry.factors source))

end NativeTemplateInstance

namespace FiniteLatentProjection

/-- Enumerate actual native models, one per structural template and tuple of
nonempty source-support masks. There is no external bound on the original
source denominators. Empty source families keep their single empty tuple. -/
def supportCatalogue (projection : FiniteLatentProjection S) (nodeBound sourceBound : Nat) :
    List (NativeTemplateInstance projection) :=
  (projection.hiddenDAG.nativeTemplateCatalogue nodeBound sourceBound).flatMap (fun template =>
    (FiniteSupportCatalogue.factorCatalogue projection.hiddenDAG.count template.entry.shape.sourceCard).map
      (fun factors => ⟨template, factors⟩))

theorem uniformSupport_mem_supportCatalogue (projection : FiniteLatentProjection S)
    (nodeBound sourceBound : Nat) (entry : NativeTemplateInstance projection)
    (listed : entry.template ∈ projection.hiddenDAG.nativeTemplateCatalogue nodeBound sourceBound) :
    entry.uniformSupport ∈ projection.supportCatalogue nodeBound sourceBound := by
  apply List.mem_flatMap_of_mem listed
  exact List.mem_map_of_mem (f := fun factors => (⟨entry.template, factors⟩ : NativeTemplateInstance projection))
    (FiniteSupportCatalogue.uniformFactors_mem projection.hiddenDAG.count entry.template.entry.shape.sourceCard entry.factors)

end FiniteLatentProjection
end Thesis.Causality
