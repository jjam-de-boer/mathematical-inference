import Thesis.CausalTransport.HiddenDAGCompactSources
import Thesis.CausalTransport.HiddenDAGValuePresentation

namespace Thesis.Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Simultaneously bounded sources and hidden values on a fixed full DAG

Compose observational source compression, actual finite source coding, and
retained-trajectory value coding. The resulting native model keeps its full
hidden DAG and public observed signature. Its private sources and endogenous
values are literal finite code types. All factual events and each requested
target probability agree with the original model, including zeros.

For t target list positions and A declared observed assignments, every source
has at most K = A + t + 1 codes, and every hidden node has at most
`(t + 1) * K ^ N` codes, where N is the original full graph's node count.
The extra action position is the factual intervention. Observed codes have
exactly the cardinality of their declared public domains, even when the old
native enumerations repeated values or included null observed cells.

This constructs bounded native representatives; it does not yet enumerate
all mechanisms on those types. Source probabilities remain arbitrary finite
rationals, so even finite mechanism coverage would not by itself give a
terminating unrestricted rational feasibility or identification procedure.
Nor does a fixed-full-DAG theorem cover varying hidden graph topologies.
-/

namespace FiniteHiddenDAGSCM.ObservationalSourceCompression

variable {original : FiniteHiddenDAGSCM S P} {targets : List (NativeProbabilityQuery S)}

/-- Repeated interventions are harmless and are counted honestly. No equality
test or deduplication of their function-valued records is requested. -/
def retainedActions (_compressed : ObservationalSourceCompression original targets) : List (HardIntervention S) :=
  targets.map NativeProbabilityQuery.intervention

def finiteModel (compressed : ObservationalSourceCompression original targets) : FiniteHiddenDAGSCM S P :=
  compressed.codeModel.retainedValueModel compressed.retainedActions

theorem finiteModel_noise (compressed : ObservationalSourceCompression original targets) (node : Fin P.hiddenDAG.count) :
    compressed.finiteModel.Noise node = Fin (compressed.codeCard node) := rfl

theorem finiteModel_noise_bound (compressed : ObservationalSourceCompression original targets) (node : Fin P.hiddenDAG.count) :
    (compressed.finiteModel.noiseEnumeration node).length ≤ S.assignmentEnumeration.length + targets.length + 1 := by
  change (compressed.codeModel.noiseEnumeration node).length ≤ _
  rw [compressed.codeModel_noiseEnumeration_length]
  exact compressed.codeCard_bound node

theorem finiteModel_nodeValue (compressed : ObservationalSourceCompression original targets) (node : Fin P.hiddenDAG.count) :
    compressed.finiteModel.NodeValue node =
      Fin (compressed.codeModel.valueWitness compressed.retainedActions node).card := rfl

theorem finiteModel_hidden_bound (compressed : ObservationalSourceCompression original targets)
    (node : Fin P.hiddenDAG.count) (hidden : P.hiddenDAG.hidden node = true) :
    (compressed.codeModel.valueWitness compressed.retainedActions node).card ≤
      (targets.length + 1) * (S.assignmentEnumeration.length + targets.length + 1) ^ P.hiddenDAG.count := by
  have bounded (current : Fin P.hiddenDAG.count) :
      (compressed.codeModel.noiseEnumeration current).length ≤ S.assignmentEnumeration.length + targets.length + 1 := by
    rw [compressed.codeModel_noiseEnumeration_length]
    exact compressed.codeCard_bound current
  simpa only [retainedActions, List.length_map] using
    compressed.codeModel.valueWitness_card_bound_of_noise_bound compressed.retainedActions _ bounded node hidden

theorem finiteModel_observed_card (compressed : ObservationalSourceCompression original targets) (index : Fin S.count) :
    (compressed.codeModel.valueWitness compressed.retainedActions (P.hiddenDAG.observedNode index)).card =
      (S.valueEnumeration index).length :=
  compressed.codeModel.retainedObservedEquiv_card compressed.retainedActions index

theorem finiteModel_observational (compressed : ObservationalSourceCompression original targets) (event : Event S.Assignment) :
    QProb.Equiv (compressed.finiteModel.observationalValue event) (original.observationalValue event) := by
  change QProb.Equiv ((compressed.codeModel.retainedValueModel compressed.retainedActions).observationalDist.probVal event) _
  rw [compressed.codeModel.retainedValueModel_observationalDist compressed.retainedActions]
  exact compressed.codeModel_observational event

theorem finiteModel_preserved (compressed : ObservationalSourceCompression original targets)
    (query : NativeProbabilityQuery S) (listed : query ∈ targets) :
    QProb.Equiv (compressed.finiteModel.interventionalValue query.intervention query.event)
      (original.interventionalValue query.intervention query.event) := by
  have actionListed : query.intervention ∈ HardIntervention.empty S :: compressed.retainedActions :=
    List.mem_cons_of_mem _ (List.mem_map_of_mem (f := NativeProbabilityQuery.intervention) listed)
  rw [finiteModel, compressed.codeModel.retainedValueModel_interventionalValue compressed.retainedActions query.intervention actionListed]
  exact compressed.codeModel_preserved query listed

/-- Original support is still required; zeros are preserved in both directions,
not repaired by completing an undefined conditional. -/
theorem finiteModel_eventPositive_iff (compressed : ObservationalSourceCompression original targets)
    (query : NativeProbabilityQuery S) (listed : query ∈ targets) :
    (compressed.finiteModel.interventionalDist query.intervention).EventPositive query.event ↔
      (original.interventionalDist query.intervention).EventPositive query.event :=
  QProb.equiv_num_pos_iff (compressed.finiteModel_preserved query listed)

/-- Only the two retained query probabilities are needed for a conditional;
neither the unretained intervention law nor its unrequested events are claimed
unchanged from the uncompressed original. -/
theorem finiteModel_conditionOn_probVal (compressed : ObservationalSourceCompression original targets)
    (intervention : HardIntervention S) (evidence event : Event S.Assignment)
    (jointListed : (⟨intervention, fun value => evidence value && event value⟩ : NativeProbabilityQuery S) ∈ targets)
    (evidenceListed : (⟨intervention, evidence⟩ : NativeProbabilityQuery S) ∈ targets)
    (supported : (original.interventionalDist intervention).EventPositive evidence) :
    QProb.Equiv
      (((compressed.finiteModel.interventionalDist intervention).conditionOn evidence
        ((compressed.finiteModel_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported)).probVal event)
      (((original.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  let supportedNew := (compressed.finiteModel_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported
  exact QProb.equiv_trans
    ((compressed.finiteModel.interventionalDist intervention).conditionOn_probVal evidence event supportedNew)
    (QProb.equiv_trans
      (QProb.div_congr (compressed.finiteModel_preserved _ jointListed) (compressed.finiteModel_preserved _ evidenceListed)
        supportedNew supported)
      (QProb.equiv_symm ((original.interventionalDist intervention).conditionOn_probVal evidence event supported)))

end FiniteHiddenDAGSCM.ObservationalSourceCompression

namespace FiniteHiddenDAGSCM

/-- Constructive bounded-representative data for the *same full hidden DAG*.
The model contains its actual independent rational source law. The executable
constructor below proves the preservation fields; callers are not asked for
an external semantic-transfer assumption or an observed-positivity premise.
Membership in the exhaustive code-mechanism catalogue is exposed by the
separate `HiddenDAGMechanismCatalogue` adapter, keeping this construction
independent of the later enumeration machinery. -/
structure BoundedRepresentation (original : FiniteHiddenDAGSCM S P) (targets : List (NativeProbabilityQuery S)) where
  model : FiniteHiddenDAGSCM S P
  sourceCard : Fin P.hiddenDAG.count → Nat
  nodeCard : Fin P.hiddenDAG.count → Nat
  noise_type : ∀ node, model.Noise node = Fin (sourceCard node)
  node_type : ∀ node, model.NodeValue node = Fin (nodeCard node)
  source_bounded : ∀ node, sourceCard node ≤ S.assignmentEnumeration.length + targets.length + 1
  hidden_bounded : ∀ node, P.hiddenDAG.hidden node = true →
    nodeCard node ≤ (targets.length + 1) * (S.assignmentEnumeration.length + targets.length + 1) ^ P.hiddenDAG.count
  observed_card : ∀ index, nodeCard (P.hiddenDAG.observedNode index) = (S.valueEnumeration index).length
  observational : ∀ event, QProb.Equiv (model.observationalValue event) (original.observationalValue event)
  preserved : ∀ query, query ∈ targets →
    QProb.Equiv (model.interventionalValue query.intervention query.event)
      (original.interventionalValue query.intervention query.event)

/-- Every native model has an explicitly constructed bounded representative
for its entire observational law and any finite target list. The bounds depend
on that list and the fixed graph/signature, not the original hidden alphabets
or source denominators. This is representation data, not a complete search
over arbitrary rational weights or over varying hidden topologies. -/
def boundedRepresentation (original : FiniteHiddenDAGSCM S P) (targets : List (NativeProbabilityQuery S)) :
    BoundedRepresentation original targets :=
  let compressed := original.compressSourcesPreservingObservation targets
  { model := compressed.finiteModel
    sourceCard := compressed.codeCard
    nodeCard := fun node => (compressed.codeModel.valueWitness compressed.retainedActions node).card
    noise_type := compressed.finiteModel_noise
    node_type := compressed.finiteModel_nodeValue
    source_bounded := compressed.codeCard_bound
    hidden_bounded := compressed.finiteModel_hidden_bound
    observed_card := compressed.finiteModel_observed_card
    observational := compressed.finiteModel_observational
    preserved := compressed.finiteModel_preserved }

end FiniteHiddenDAGSCM
end Thesis.Causality
