import Thesis.CausalTransport.BoundedNativeCatalogue

namespace Thesis.Causality

open Probability

/-!
# Bounded native coverage without preselected finite code types

The bounded catalogue consists of code models, but the original native model
need not use codes as its endogenous or private-noise values. Deduplicate its
supplied complete enumerations and construct actual two-sided witnesses.
Native template encoding preserves every intervention, not just selected
queries. Source singleton aggregation retains the original denominators.

Thus bounds on the original supplied enumeration lengths and denominators
give a listed representative of the original model in the exact searched
catalogue. The input is the actual model and its explicit numerical bounds,
not an assumed simulation, a selected structural family or a choice of a
code presentation. Repeated enumeration entries are counted honestly in
those input bounds and removed constructively in the representation.

No projection-wide compression is invoked: such compression is not known to
preserve a prescribed denominator bound. This adapter retains the original
full hidden graph and the complete declared observed domains, including null
intervention values. It does not settle unbounded rational feasibility.
-/

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

namespace FiniteHiddenDAGSCM

def enumeratedNodeWitness (original : FiniteHiddenDAGSCM S P) (node : Fin P.hiddenDAG.count) :
    FiniteWitness (original.NodeValue node) :=
  .ofList (deduplicate (original.nodeEnumeration node))
    (fun value => (mem_deduplicate _ _).mpr (original.node_complete node value))
    (deduplicate_nodup _)

def enumeratedNoiseWitness (original : FiniteHiddenDAGSCM S P) (node : Fin P.hiddenDAG.count) :
    FiniteWitness (original.Noise node) :=
  .ofList (deduplicate (original.noiseEnumeration node))
    (fun value => (mem_deduplicate _ _).mpr (original.noise_complete node value))
    (deduplicate_nodup _)

def enumeratedNodeCodes (original : FiniteHiddenDAGSCM S P) (node : Fin P.hiddenDAG.count) :
    ValueEquivalence (original.NodeValue node) (Fin (original.enumeratedNodeWitness node).card) :=
  let witness := original.enumeratedNodeWitness node
  ⟨witness.encode, witness.decode, witness.encode_decode, witness.decode_encode⟩

def enumeratedNoiseCodes (original : FiniteHiddenDAGSCM S P) (node : Fin P.hiddenDAG.count) :
    ValueEquivalence (original.Noise node) (Fin (original.enumeratedNoiseWitness node).card) :=
  let witness := original.enumeratedNoiseWitness node
  ⟨witness.encode, witness.decode, witness.encode_decode, witness.decode_encode⟩

def enumeratedInstance (original : FiniteHiddenDAGSCM S P) : NativeTemplateInstance P :=
  ⟨original.nativeTemplate (fun node => (original.enumeratedNodeWitness node).card)
      (fun node => (original.enumeratedNoiseWitness node).card) original.enumeratedNodeCodes original.enumeratedNoiseCodes,
    original.nativeTemplateFactors (fun node => (original.enumeratedNoiseWitness node).card) original.enumeratedNoiseCodes⟩

def boundedSearchRepresentative (original : FiniteHiddenDAGSCM S P) : NativeTemplateInstance P := original.enumeratedInstance.canonical

theorem boundedSearchRepresentative_interventionalValue (original : FiniteHiddenDAGSCM S P)
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv (original.boundedSearchRepresentative.model.interventionalValue intervention event)
      (original.interventionalValue intervention event) :=
  QProb.equiv_trans (original.enumeratedInstance.canonical_interventionalValue intervention event)
    (original.nativeTemplateModel_interventionalValue (fun node => (original.enumeratedNodeWitness node).card)
      (fun node => (original.enumeratedNoiseWitness node).card) original.enumeratedNodeCodes original.enumeratedNoiseCodes intervention event)

theorem boundedSearchRepresentative_observationalValue (original : FiniteHiddenDAGSCM S P) (event : Event S.Assignment) :
    QProb.Equiv (original.boundedSearchRepresentative.model.observationalValue event) (original.observationalValue event) :=
  original.boundedSearchRepresentative_interventionalValue (HardIntervention.empty S) event

theorem boundedSearchRepresentative_den (original : FiniteHiddenDAGSCM S P) (node : Fin P.hiddenDAG.count) :
    (original.boundedSearchRepresentative.factors node).den = (original.factor node).den :=
  original.enumeratedInstance.canonical_factor_den node

theorem enumeratedNodeWitness_card_le (original : FiniteHiddenDAGSCM S P) (node : Fin P.hiddenDAG.count) :
    (original.enumeratedNodeWitness node).card ≤ (original.nodeEnumeration node).length :=
  deduplicate_length_le (original.nodeEnumeration node)

theorem enumeratedNoiseWitness_card_le (original : FiniteHiddenDAGSCM S P) (node : Fin P.hiddenDAG.count) :
    (original.enumeratedNoiseWitness node).card ≤ (original.noiseEnumeration node).length :=
  deduplicate_length_le (original.noiseEnumeration node)

/-- Complete bounded-class membership is derived from the unchanged native
record. No preservation or membership field is requested from the caller. -/
theorem boundedSearchRepresentative_mem (original : FiniteHiddenDAGSCM S P)
    (nodeBound sourceBound denominatorBound : Nat)
    (nodes : ∀ node, (original.nodeEnumeration node).length ≤ nodeBound)
    (sources : ∀ node, (original.noiseEnumeration node).length ≤ sourceBound)
    (denominators : ∀ node, (original.factor node).den ≤ denominatorBound) :
    original.boundedSearchRepresentative ∈ P.boundedNativeCatalogue nodeBound sourceBound denominatorBound :=
  P.canonical_mem_boundedNativeCatalogue_of_bounds _ _ _ original.enumeratedInstance
    (fun node => Nat.le_trans (original.enumeratedNodeWitness_card_le node) (nodes node))
    (fun node => Nat.le_trans (original.enumeratedNoiseWitness_card_le node) (sources node)) denominators

end FiniteHiddenDAGSCM
end Thesis.Causality
