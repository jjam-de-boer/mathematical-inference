import Thesis.CausalTransport.NativeRewritePathSupport
import Thesis.CausalTransport.HiddenDAGSoundness

namespace Thesis.Causality

open Probability
open DoCalculusRewritePath

/-!
# Support-preserving linearization in original finite hidden-DAG models

The path is fixed by the original proof's syntax, not chosen separately for
different models or support profiles. Every original supported application
gives actual values at *all* vertices of this same path. Endpoints are unchanged
in the type. The elementary-path support theorem then reconstructs a supported
old-language derivation, so the transformation adds no causal equation.

The key induction carries equivalence to the original source at every vertex,
not merely its three-valued support status. In a weighted congruence the
weight path runs first. Its factor path is interpreted only under a positive
original weight; equivalent weights select the same zero/positive branch.
Marginalization retains every finite substituted reference. All witnesses are
data in Type, assembled by functions and finite products without choice.

This establishes a proof-presentation bridge, not an unbounded path search,
an effective universal catalogue, or semantic completeness for arbitrary
formulas. Its semantic theorem uses the model's actual projected graph;
unrelated graph/profile combinations are deliberately not covered.
-/

variable {S : ObservedSignature} {P : FiniteLatentProjection S}

namespace DoCalculusRewritePath

private noncomputable def single_equivalentVertices {left right : ProbabilityTerm S}
    (step : DoCalculusRewriteStep P.observedGraph left right) (model : FiniteHiddenDAGSCM S P)
    (reference : S.Assignment)
    (supported : HiddenDAGLocalDerivationSupport model reference step.toDerivation) :
    (single step).AllVertices (fun term => model.TermEquivalentAt left term reference) :=
  ⟨ProbabilityResult.refl _, step.toDerivation.hiddenDAG_denotational_soundAt supported⟩

end DoCalculusRewritePath

namespace DoCalculusDerivation

/-- All intermediate values agree with the original source, on each original
supported application. This stronger data-valued invariant avoids confusing
equal support patterns with equal rational probabilities. -/
noncomputable def linearize_equivalentVertices {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation P.observedGraph left right)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (supported : HiddenDAGLocalDerivationSupport model reference derivation) :
    derivation.linearize.AllVertices (fun term => model.TermEquivalentAt left term reference) := by
  induction derivation generalizing reference with
  | refl term => exact ProbabilityResult.refl _
  | symm inner ih =>
      exact AllVertices.reverse _ (AllVertices.map _
        (fun _ same => ProbabilityResult.trans
          (ProbabilityResult.symm (inner.hiddenDAG_denotational_soundAt supported.2.2)) same)
        (ih reference supported.2.2))
  | trans first second firstIH secondIH =>
      exact AllVertices.append _ _ (firstIH reference supported.2.2.1)
        (AllVertices.map _ (fun _ same => ProbabilityResult.trans
          (first.hiddenDAG_denotational_soundAt supported.2.2.1) same)
          (secondIH reference supported.2.2.2))
  | doRule application => exact single_equivalentVertices (.atom (.doRule application)) model reference supported
  | marginalization x y z w disjoint => exact single_equivalentVertices (.atom (.marginalization x y z w disjoint)) model reference supported
  | conditioning x y z w disjoint => exact single_equivalentVertices (.atom (.conditioning x y z w disjoint)) model reference supported
  | chain x y z w disjoint => exact single_equivalentVertices (.atom (.chain x y z w disjoint)) model reference supported
  | weightedChain x y z w disjoint => exact single_equivalentVertices (.atom (.weightedChain x y z w disjoint)) model reference supported
  | multiplyComm first second => exact single_equivalentVertices (.atom (.multiplyComm first second)) model reference supported
  | multiplyAssoc first second third => exact single_equivalentVertices (.atom (.multiplyAssoc first second third)) model reference supported
  | marginalizeCongr nodes inner ih =>
      let variants := ProbabilityTerm.marginalAssignments S nodes reference
      let values := AllVertices.pi (A := { variant : S.Assignment // variant ∈ variants }) inner.linearize
        (fun variant => ih variant.val (supported.2.2 variant.val variant.property))
      exact AllVertices.mapFrame (.marginalize nodes) _
        (AllVertices.map _ (fun _ same => ProbabilityResult.sum_map_congr_mem variants _ _
          (fun variant member => same ⟨variant, member⟩)) values)
  | evaluateAtCongr fixed inner ih =>
      exact AllVertices.mapFrame (.evaluateAt fixed) _ (ih fixed supported.2.2)
  | @addCongr left left' right right' first second firstIH secondIH =>
      exact AllVertices.append _ _
        (AllVertices.mapFrame (.addLeft right) _ (AllVertices.map _
          (fun _ same => ProbabilityResult.add_congr same (ProbabilityResult.refl _))
          (firstIH reference supported.2.2.1)))
        (AllVertices.mapFrame (.addRight left') _ (AllVertices.map _
          (fun _ same => ProbabilityResult.add_congr
            (first.hiddenDAG_denotational_soundAt supported.2.2.1) same)
          (secondIH reference supported.2.2.2)))
  | @multiplyCongr left left' right right' first second firstIH secondIH =>
      exact AllVertices.append _ _
        (AllVertices.mapFrame (.multiplyLeft right) _ (AllVertices.map _
          (fun _ same => ProbabilityResult.multiply_congr same (ProbabilityResult.refl _))
          (firstIH reference supported.2.2.1)))
        (AllVertices.mapFrame (.multiplyRight left') _ (AllVertices.map _
          (fun _ same => ProbabilityResult.multiply_congr
            (first.hiddenDAG_denotational_soundAt supported.2.2.1) same)
          (secondIH reference supported.2.2.2)))
  | @weightedMultiplyCongr weight weight' factor factor' first second firstIH secondIH =>
      let factorValues := AllVertices.pi (A := ProbabilityResult.PositiveSupportedValue (model.termDenote weight reference))
        second.linearize (fun positive => secondIH reference (supported.2.2.2 positive))
      exact AllVertices.append _ _
        (AllVertices.mapFrame (.weightedLeft factor) _ (AllVertices.map _
          (fun _ same => ProbabilityResult.weightedMultiply_congr same (ProbabilityResult.refl _))
          (firstIH reference supported.2.2.1)))
        (AllVertices.mapFrame (.weightedRight weight') _ (AllVertices.map _
          (fun _ same => ProbabilityResult.weightedMultiply_congr_on_positive
            (first.hiddenDAG_denotational_soundAt supported.2.2.1) same) factorValues))
  | @divideCongr left left' right right' first second firstIH secondIH =>
      exact AllVertices.append _ _
        (AllVertices.mapFrame (.divideLeft right) _ (AllVertices.map _
          (fun _ same => ProbabilityResult.divide_congr same (ProbabilityResult.refl _))
          (firstIH reference supported.2.2.1)))
        (AllVertices.mapFrame (.divideRight left') _ (AllVertices.map _
          (fun _ same => ProbabilityResult.divide_congr
            (first.hiddenDAG_denotational_soundAt supported.2.2.1) same)
          (secondIH reference supported.2.2.2)))
  | eqCongr sameLeft sameRight inner ih =>
      cases sameLeft
      cases sameRight
      exact ih reference supported.2.2

/-- Preserve actual support at every vertex of one model-independent path.
The source value is transported through genuine rational equivalences. -/
noncomputable def linearize_supportedVertices {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation P.observedGraph left right)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (supported : HiddenDAGLocalDerivationSupport model reference derivation) :
    derivation.linearize.AllVertices (fun term => model.TermSupportedAt term reference) :=
  AllVertices.map _ (fun _ same => ProbabilityResult.Supported.transport same
    (HiddenDAGLocalDerivationSupport.endpoints model reference derivation supported).1)
    (derivation.linearize_equivalentVertices model reference supported)

theorem linearize_checkVertices {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation P.observedGraph left right)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (accepted : HiddenDAGLocalDerivationSupport.check model reference derivation = true) :
    derivation.linearize.checkVertices model reference = true :=
  derivation.linearize.checkVertices_of_supported model reference
    (derivation.linearize_supportedVertices model reference
      (HiddenDAGLocalDerivationSupport.ofCheck model reference derivation accepted))

/-- Reinterpret the linear presentation in the old checker without losing
an accepted application. No converse or universal stopping claim is needed. -/
theorem linearize_toDerivation_check {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation P.observedGraph left right)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (accepted : HiddenDAGLocalDerivationSupport.check model reference derivation = true) :
    HiddenDAGLocalDerivationSupport.check model reference derivation.linearize.toDerivation = true :=
  HiddenDAGLocalDerivationSupport.check_of_supported model reference _
    (derivation.linearize.toDerivation_support model reference
      (derivation.linearize_supportedVertices model reference
        (HiddenDAGLocalDerivationSupport.ofCheck model reference derivation accepted)))

end DoCalculusDerivation
end Thesis.Causality
