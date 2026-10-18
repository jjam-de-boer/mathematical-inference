import Thesis.CausalTransport.HiddenDAGCompactSources
import Thesis.Examples.HiddenDAGSourceCompression

namespace Thesis.Causality.Examples.HiddenDAGCompactSources

open Probability HiddenDAGCollapse HiddenDAGSourceCompression

/-!
# Bounded private alphabets after actual native source compression

Reuse the five-node original hidden graph and its two retained queries. Each
input factor has four weighted occurrences. The compressed, coded model has
at most three private codes at every node, now as an actual finite noise type
rather than just a small support inside the previous ambient type.

The second interface retains the whole observed distribution and a requested
effect. Finally, retaining both the joint event and its conditioner yields
preservation of an arbitrary supported conditional after any chosen hard
intervention. All results use symbolic construction theorems; no full source
cube or concrete compression recursion is expanded by a decision tactic.
-/

def queryModel := compressed.codeModel

theorem noise_is_actual_code_type (node : Fin fullGraph.count) :
    queryModel.Noise node = Fin (compressed.codeCard node) := compressed.codeModel_noise node

theorem actual_alphabet_bounded (node : Fin fullGraph.count) :
    (queryModel.noiseEnumeration node).length ≤ 3 := by
  change (compressed.codeModel.noiseEnumeration node).length ≤ 3
  rw [compressed.codeModel_noiseEnumeration_length]
  exact compressed.codeCard_bound node

/-- Compare code positions with the original four occurrences, not with
the old Boolean type's two distinct labels: occurrence indexing can repeat. -/
theorem fewer_codes_than_original_occurrences (node : Fin fullGraph.count) :
    compressed.codeCard node < (original.factor node).atoms.length :=
  Nat.lt_of_le_of_lt (compressed.codeCard_bound node) (by change 3 < 4; decide)

theorem every_retained_query (index : Fin 2) :
    QProb.Equiv (queryModel.interventionalValue (queries index).intervention (queries index).event)
      (original.interventionalValue (queries index).intervention (queries index).event) :=
  compressed.codeModel_preserved index

theorem retained_support_exact (index : Fin 2) :
    0 < (queryModel.interventionalValue (queries index).intervention (queries index).event).num ↔
      0 < (original.interventionalValue (queries index).intervention (queries index).event).num :=
  compressed.codeModel_query_positive_iff index

def observedModel := withObservation.codeModel

theorem whole_observed_law (event : Event signature.Assignment) :
    QProb.Equiv (observedModel.observationalValue event) (original.observationalValue event) :=
  withObservation.codeModel_observational event

theorem requested_effect : QProb.Equiv
    (observedModel.interventionalValue target.intervention target.event)
    (original.interventionalValue target.intervention target.event) :=
  withObservation.codeModel_preserved target (by simp)

theorem observed_alphabet_bound (node : Fin fullGraph.count) :
    withObservation.codeCard node ≤ signature.assignmentEnumeration.length + 1 + 1 :=
  withObservation.codeCard_bound node

/-- Construct the retained pair without testing equality of function-valued
query records. Finite membership is proved directly by its list positions. -/
def conditionalTargets (intervention : HardIntervention signature) (evidence event : Event signature.Assignment) :
    List (NativeProbabilityQuery signature) :=
  [⟨intervention, fun value => evidence value && event value⟩, ⟨intervention, evidence⟩]

/-- Keep elaboration of the interface regression from unfolding the actual
five-source compression algorithm. This remains an executable definition with
its checked constructor body; the test uses the proved compression interface,
not a larger computation/heartbeat allowance or a replacement assumption. -/
@[irreducible] def conditionalCompression (intervention : HardIntervention signature) (evidence event : Event signature.Assignment) :
    FiniteHiddenDAGSCM.ObservationalSourceCompression original (conditionalTargets intervention evidence event) :=
  original.compressSourcesPreservingObservation (conditionalTargets intervention evidence event)

theorem arbitrary_supported_conditional (intervention : HardIntervention signature) (evidence event : Event signature.Assignment)
    (supported : (original.interventionalDist intervention).EventPositive evidence) :
    let retained := conditionalCompression intervention evidence event
    let evidenceListed : (⟨intervention, evidence⟩ : NativeProbabilityQuery signature) ∈ conditionalTargets intervention evidence event :=
      List.mem_cons_of_mem _ List.mem_cons_self
    QProb.Equiv
      (((retained.codeModel.interventionalDist intervention).conditionOn evidence
        ((retained.codeModel_eventPositive_iff ⟨intervention, evidence⟩ evidenceListed).mpr supported)).probVal event)
      (((original.interventionalDist intervention).conditionOn evidence supported).probVal event) := by
  dsimp only
  exact (conditionalCompression intervention evidence event).codeModel_conditionOn_probVal intervention evidence event
    List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) supported

end Thesis.Causality.Examples.HiddenDAGCompactSources
