import Thesis.CausalTransport.HiddenDAGObservationalCompression
import Thesis.Examples.HiddenDAGCollapse

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGSourceCompression

open Probability HiddenDAGCollapse

/-!
# Native compression retains a factual zero and an intervened relay query

Reuse the unchanged five-node hidden DAG `U, X, V, Y, Z`, including its shared
three-child root and hidden relay.  Give every noise source four positive
atom occurrences (two false and two true).  The two requested probabilities
are observational `Y = true`, which is null, and `Y = true` after forcing
`X = false`.  Every source is bounded by three occurrences in the constructed
native model while both actual query probabilities are preserved.

These native statements use the general symbolic theorem, without expanding
the full noise cube in the kernel.  Small product-level regressions separately
execute the compression algorithm.  No canonical projected-root assumption,
observed positivity premise or external source-replacement interface is used.
-/

def redundant : FiniteProbRecord Bool := ⟨[(false, 1), (false, 1), (true, 1), (true, 1)], 4, by decide, rfl⟩
def redundantLaw : FiniteProduct.IndependentLaw (fun _ : Fin fullGraph.count => Bool) :=
  ⟨(fun _ => redundant), FiniteProduct.record 5 (fun _ => Bool) (fun _ => redundant),
    FiniteProduct.record_rectangular_probVal 5 (fun _ => Bool) (fun _ => redundant)⟩
def original := model.withSourceLaw redundantLaw
def queries : Fin 2 → NativeProbabilityQuery signature := fun index =>
  ⟨if index.val = 0 then HardIntervention.empty signature else forceXFalse, fun assignment => assignment y⟩
def compressed := original.compressSources queries

theorem original_source_larger (node : Fin fullGraph.count) : (original.factor node).atoms.length = 4 := rfl
theorem every_source_bounded (node : Fin fullGraph.count) : (compressed.model.factor node).atoms.length ≤ 3 := compressed.bounded node
theorem every_weight_positive (node : Fin fullGraph.count) (atom : Bool × Nat)
    (member : atom ∈ (compressed.model.factor node).atoms) : 0 < atom.2 := compressed.positive node atom member
theorem observational_query_preserved : QProb.Equiv
    (compressed.model.observationalValue (fun assignment => assignment y))
    (original.observationalValue (fun assignment => assignment y)) := compressed.preserved 0
theorem interventional_query_preserved : QProb.Equiv
    (compressed.model.interventionalValue forceXFalse (fun assignment => assignment y))
    (original.interventionalValue forceXFalse (fun assignment => assignment y)) := compressed.preserved 1
theorem support_preserved (index : Fin 2) :
    0 < (compressed.model.interventionalValue (queries index).intervention (queries index).event).num ↔
      0 < (original.interventionalValue (queries index).intervention (queries index).event).num :=
  compressed.query_positive_iff index
theorem every_structural_readout_unchanged (intervention : HardIntervention signature) (noise : original.NoiseAssignment) :
    compressed.model.evalObserved intervention noise = original.evalObserved intervention noise :=
  original.withSourceLaw_evalObserved compressed.law intervention noise
theorem all_sources_still_independent (events : (node : Fin fullGraph.count) → Bool → Bool) :
    QProb.Equiv (compressed.model.prior.probVal (FiniteProduct.rectangularEvent 5 (fun _ => Bool) events))
      (FiniteProduct.qProduct 5 (fun node => (compressed.model.factor node).probVal (events node))) := compressed.model.product_law events

/-! The fixed-law adapter retains every observed event automatically, not
only the factual event that happened to appear in the earlier query pair. -/

def target : NativeProbabilityQuery signature := ⟨forceXFalse, fun assignment => assignment y⟩
def withObservation := original.compressSourcesPreservingObservation [target]
theorem entire_observed_law_preserved (event : Event signature.Assignment) :
    QProb.Equiv (withObservation.model.observationalValue event) (original.observationalValue event) :=
  withObservation.observational event
theorem selected_effect_preserved : QProb.Equiv
    (withObservation.model.interventionalValue target.intervention target.event)
    (original.interventionalValue target.intervention target.event) :=
  withObservation.preserved target (List.mem_cons.mpr (Or.inl rfl))
theorem observed_law_source_bound (node : Fin fullGraph.count) :
    (withObservation.model.factor node).atoms.length ≤ signature.assignmentEnumeration.length + 1 + 1 := withObservation.bounded node

end HiddenDAGSourceCompression
end Examples
end Causality
end Thesis
