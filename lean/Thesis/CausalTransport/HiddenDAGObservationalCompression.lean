import Thesis.CausalTransport.HiddenDAGSourceCompression

namespace Thesis
namespace Causality

open Probability

/-!
# Source compression retaining the whole observed law and selected effects

Fixed-law identification and causal bounds require the entire observational
distribution to remain unchanged, not just a few chosen factual events.  This
adapter automatically adds all observational singleton queries to a supplied
finite target list, applies native source compression once to the combined
family, and derives equality of every observed event by finite extensionality.

The bound for each source is the number of observed assignments plus the
number of requested targets plus one.  It is a sufficient constructive bound,
not a claim of minimal support.  Duplicate target queries are allowed and no
equality decision for function-valued query events is required.

The original hidden DAG, structural mechanisms and ambient node/noise value
types remain unchanged.  This theorem supplies an actual independent native
replacement with the same full observed law; it does not select among causal
models, enumerate mechanisms or decide general rational feasibility.
-/

def NativeProbabilityQuery.observationalCells (S : ObservedSignature) : List (NativeProbabilityQuery S) :=
  S.assignmentEnumeration.map (fun assignment =>
    ⟨HardIntervention.empty S, FiniteProbRecord.singletonEvent assignment⟩)

namespace FiniteHiddenDAGSCM

structure ObservationalSourceCompression (original : FiniteHiddenDAGSCM S projection)
    (targets : List (NativeProbabilityQuery S)) where
  law : FiniteProduct.IndependentLaw original.Noise
  bounded : forall node, (law.factor node).atoms.length ≤ S.assignmentEnumeration.length + targets.length + 1
  positive : forall node atom, atom ∈ (law.factor node).atoms → 0 < atom.2
  observational : forall event, QProb.Equiv ((original.withSourceLaw law).observationalValue event) (original.observationalValue event)
  preserved : forall query, query ∈ targets → QProb.Equiv
    ((original.withSourceLaw law).interventionalValue query.intervention query.event)
    (original.interventionalValue query.intervention query.event)

def ObservationalSourceCompression.model {original : FiniteHiddenDAGSCM S projection} {targets : List (NativeProbabilityQuery S)}
    (compressed : ObservationalSourceCompression original targets) : FiniteHiddenDAGSCM S projection :=
  original.withSourceLaw compressed.law

/-- Include the complete observed table automatically, so preserving one
effect cannot accidentally be used as a same-observation countermodel or
fixed-law bounding theorem without its factual-law requirement. -/
def compressSourcesPreservingObservation (original : FiniteHiddenDAGSCM S projection)
    (targets : List (NativeProbabilityQuery S)) : ObservationalSourceCompression original targets := by
  let catalogue := NativeProbabilityQuery.observationalCells S ++ targets
  let queries := fun index : Fin catalogue.length => catalogue[index.val]
  let made := original.compressSources queries
  have retained (query : NativeProbabilityQuery S) (listed : query ∈ catalogue) : QProb.Equiv
      ((original.withSourceLaw made.law).interventionalValue query.intervention query.event)
      (original.interventionalValue query.intervention query.event) := by
    rcases List.mem_iff_get.mp listed with ⟨index, same⟩
    have preserved := made.preserved index
    change QProb.Equiv
      ((original.withSourceLaw made.law).interventionalValue (catalogue.get index).intervention (catalogue.get index).event)
      (original.interventionalValue (catalogue.get index).intervention (catalogue.get index).event) at preserved
    rw [same] at preserved
    exact preserved
  refine ⟨made.law, ?_, made.positive, ?_, ?_⟩
  · intro node
    simpa only [catalogue, NativeProbabilityQuery.observationalCells, List.length_append, List.length_map] using made.bounded node
  · intro event
    apply FiniteProbRecord.probVal_extensional_of_singletons _ _ S.assignmentEnumeration
      S.assignmentEnumeration_nodup S.assignmentEnumeration_complete (fun assignment => ?_) event
    apply retained ⟨HardIntervention.empty S, FiniteProbRecord.singletonEvent assignment⟩
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨assignment, S.assignmentEnumeration_complete assignment, rfl⟩))
  · intro query listed
    exact retained query (List.mem_append.mpr (Or.inr listed))

end FiniteHiddenDAGSCM
end Causality
end Thesis
