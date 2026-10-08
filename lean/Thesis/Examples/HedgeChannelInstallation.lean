import Thesis.CausalTransport.HedgeChannelInstallation
import Thesis.Examples.HedgeChannelConstruction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelInstallation

open Probability

/-!
# Actual bow models obtained from the arbitrary-hedge installer

Unlike the earlier hand-written bow families, both models below are returned
by the general graph-indexed installer applied to the existing hedge witness.
The two genuine outer masks, one small slot, and two original-node background
slots give five channels.  The background slot at the small outcome is empty
on both sides.  The power family has scale seven, ordinary amplitude forty-
nine, capacity three hundred forty-three, and small anchored amplitude seven.

Complete integration of the actual root-major source checks all observed
assignments, including both large channels simultaneously in the row-choice
expansion.  The semantic bridge then supplies equality of every observed
event and a gap at the original intervened outcome.  Only thirty-two shared
root vectors and two already integrated private rows are evaluated; the
private response-function support is not enumerated.

This regression checks the installed indexing, masks, amplitudes and typed
parent corrections together.  The general observational assembly and outcome
flow proof are still open; one bow is not a universal completeness theorem.
-/

private def signature := HedgeChannelConstruction.signature
private def graph := HedgeChannelConstruction.graph
private def witness := HedgeChannelConstruction.witness
private def rich := HedgeChannelConstruction.rich
private def action := HedgeChannelConstruction.actionNode
private def outcome := HedgeChannelConstruction.outcomeNode
private def zeroSignal (_child : Fin signature.count) (_parents : signature.binary.ParentValues _child) : Bool := false

private def leftTables := Causality.HedgeChannelInstallation.leftTables witness
private def rightTables := Causality.HedgeChannelInstallation.rightTables witness
private def leftSignals := Causality.HedgeChannelInstallation.leftSignals witness rich zeroSignal zeroSignal
private def rightSignals := Causality.HedgeChannelInstallation.rightSignals witness zeroSignal zeroSignal
private def leftModel := Causality.HedgeChannelInstallation.leftModel witness rich zeroSignal zeroSignal
private def rightModel := Causality.HedgeChannelInstallation.rightModel witness zeroSignal zeroSignal

/-- Off-mask coordinates add no duplicate choices: the empty outer set
has one mask, whereas two genuine outer coordinates have exactly four. -/
theorem mask_enumeration_boundaries :
    (Causality.HedgeChannelInstallation.masks (NodeSet.empty : NodeSet signature)).length = 1 ∧
      (Causality.HedgeChannelInstallation.masks (NodeSet.full : NodeSet signature)).length = 4 := by decide +kernel

/-- Only the genuine outer coordinate contributes a binary mask choice.
The unused outcome-background slot is retained in the common five slots. -/
theorem channel_slot_counts :
    (Causality.HedgeChannelInstallation.masks (Causality.HedgeChannelInstallation.outer witness)).length = 2 ∧
      Causality.HedgeChannelInstallation.channelCount witness = 5 := by decide +kernel

/-- Both mask bits are correct at the outer vertex; neither mask selects
the small outcome.  This catches duplication or a reversed slot decoder. -/
theorem installed_mask_bits :
    Causality.HedgeChannelInstallation.selected witness ⟨0, by decide +kernel⟩ action = false ∧
      Causality.HedgeChannelInstallation.selected witness ⟨1, by decide +kernel⟩ action = true ∧
      Causality.HedgeChannelInstallation.selected witness ⟨0, by decide +kernel⟩ outcome = false ∧
      Causality.HedgeChannelInstallation.selected witness ⟨1, by decide +kernel⟩ outcome = false := by decide +kernel

/-- Compatibility and full observed support belong to the actual installed
SCMs, and follow symbolically from the universal installer. -/
theorem actual_models_compatible : Compatible leftModel graph.binary ∧ Compatible rightModel graph.binary :=
  Causality.HedgeChannelInstallation.models_compatible witness rich zeroSignal zeroSignal

theorem actual_models_positive : ObservationallyPositive leftModel ∧ ObservationallyPositive rightModel :=
  Causality.HedgeChannelInstallation.models_positive witness rich zeroSignal zeroSignal

private theorem assignment_presentation (sample : signature.binary.Assignment) :
    sample = (fun child => if child.val = 0 then sample (0 : Fin 2) else sample (1 : Fin 2)) := by
  funext child
  by_cases first : child.val = 0
  · have equal : child = (0 : Fin 2) := Fin.ext first
    subst child
    rfl
  · have equal : child = (1 : Fin 2) := Fin.ext (by
      change child.val = 1
      have bound := child.isLt
      change child.val < 2 at bound
      omega)
    subst child
    rfl

/-- Full factual integration of the generally installed pair agrees at
every observed assignment.  No private response-function prior is reduced. -/
theorem actual_integrated_numerators_equal (sample : signature.binary.Assignment) :
    Causality.HedgeChannelTable.integratedNumerator graph 5 leftTables leftSignals
      (FiniteLatentSCM.noIntervention signature.binary) sample =
    Causality.HedgeChannelTable.integratedNumerator graph 5 rightTables rightSignals
      (FiniteLatentSCM.noIntervention signature.binary) sample := by
  have presentation := assignment_presentation sample
  cases first : sample (0 : Fin 2) <;> cases second : sample (1 : Fin 2) <;>
    rw [first, second] at presentation <;> rw [presentation] <;> decide +kernel

/-- Equality covers complete observed events, not just the two marginals.
The exact expansion and denominator bridge refers to the same installed SCMs. -/
theorem actual_observational_equivalence : ObservationallyEquivalent leftModel rightModel := by
  apply Causality.HedgeChannelTable.model_observationallyEquivalent_of_expansion graph 5
    leftTables rightTables leftSignals rightSignals
  · exact Causality.HedgeChannelInstallation.capacities_equal witness
  · intro sample
    exact (Causality.HedgeChannelTable.integratedNumerator_expansion graph 5 leftTables leftSignals
      (FiniteLatentSCM.noIntervention signature.binary) sample).symm.trans
      ((congrArg (fun value : Nat => (value : Int)) (actual_integrated_numerators_equal sample)).trans
        (Causality.HedgeChannelTable.integratedNumerator_expansion graph 5 rightTables rightSignals
          (FiniteLatentSCM.noIntervention signature.binary) sample))

private def target : Fin signature.count -> Option Bool :=
  fun child => if child = action then some true else none
private def outcomeEvent : Event signature.binary.Assignment := fun sample => !(sample outcome)

/-- Literal event numerators retain projection onto the original outcome.
Their common actual denominator is positive by the general likelihood bridge. -/
theorem intervened_outcome_numerators :
    Causality.HedgeChannelTable.eventNumerator graph 5 leftTables leftSignals target outcomeEvent = 10976 ∧
      Causality.HedgeChannelTable.eventNumerator graph 5 rightTables rightSignals target outcomeEvent = 11200 := by
  decide +kernel

/-- The installed pair separates the original causal outcome event.  This
does not claim that every hedge's original-outcome flow has been proved. -/
theorem actual_interventional_gap :
    Not (QProb.Equiv (leftModel.interventionalValue target outcomeEvent)
      (rightModel.interventionalValue target outcomeEvent)) := by
  apply Causality.HedgeChannelTable.model_interventional_event_not_equiv graph 5
    leftTables rightTables leftSignals rightSignals
    (Causality.HedgeChannelInstallation.capacities_equal witness) target outcomeEvent
  rw [intervened_outcome_numerators.1, intervened_outcome_numerators.2]
  decide

end HedgeChannelInstallation
end Examples
end Causality
end Thesis
