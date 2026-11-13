import Thesis.CausalTransport.HedgeChannelInterventional
import Thesis.Examples.HedgeChannelConstruction

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelInterventional

open Probability

/-!
# Original action cut and conflicting cells in the installed bow

The left factual expansion of the existing installed bow has twelve row
choices.  Forcing its action changes that actual list to three choices:
one common background term and two proper large-channel selections which
integrate to zero.  The right has two actual terms, including its full small
channel.  Their signed difference is 224 when the queried outcome is false
and -224 when it is true.

The support test deliberately does not inspect the sample.  A sample
conflicting with the forced action still has the same two right choices,
but both actual integrals are zero.  Forcing the small outcome as well
removes the full-small canonical block and restores equality of the two
actual likelihoods.  These boundaries catch deletion of a consistency
indicator or retention of a channel at a forced row.

The original outcome event is used unchanged in the projection check.
Only the thirty-two actual shared root vectors and two integrated row
factors are evaluated.  This fixture does not prove the universal nonzero
projected contribution; the general event-difference theorem retains that
remaining obligation explicitly.
-/

private def signature := HedgeChannelConstruction.signature
private def graph := HedgeChannelConstruction.graph
private def witness := HedgeChannelConstruction.witness
private def rich := HedgeChannelConstruction.rich
private def action := HedgeChannelConstruction.actionNode
private def outcome := HedgeChannelConstruction.outcomeNode
private def zeroSignal (_child : Fin signature.count) (_parents : signature.binary.ParentValues _child) : Bool := false
private def target : Fin signature.count -> Option Bool := fun child => if child = action then some false else none
private def bothForced : Fin signature.count -> Option Bool := fun _ => some false
private def firstSample : signature.binary.Assignment := fun _ => false
private def secondSample : signature.binary.Assignment := fun child => decide (child = outcome)
private def conflictingSample : signature.binary.Assignment := fun child => decide (child = action)
private def originalEvent : Event signature.binary.Assignment := fun sample => !(sample outcome)
private def leftTables := Causality.HedgeChannelInstallation.leftTables witness
private def rightTables := Causality.HedgeChannelInstallation.rightTables witness
private def leftSignals := Causality.HedgeChannelInstallation.leftSignals witness rich zeroSignal zeroSignal
private def rightSignals := Causality.HedgeChannelInstallation.rightSignals witness zeroSignal zeroSignal
private def fullSum (chosenTarget : Fin signature.count -> Option Bool) (sample : signature.binary.Assignment) : Int :=
  ((Causality.HedgeChannelInstallation.rightFullChoicesUnder witness chosenTarget).map
    (Causality.HedgeChannelInstallation.rightTermIntegralUnder witness zeroSignal zeroSignal chosenTarget sample)).sum

/-- The actual forced-row product and the canonical survivors have different
counts on the left; proper main selections are proved zero by integration. -/
theorem action_choice_counts :
    (FiniteProduct.enumeration signature.count (fun _ => Option (Fin 5))
      (fun child => (leftTables child).expansionChoicesUnder (target child))).length = 3 ∧
    (FiniteProduct.enumeration signature.count (fun _ => Option (Fin 5))
      (fun child => (rightTables child).expansionChoicesUnder (target child))).length = 2 ∧
    (Causality.HedgeChannelInstallation.commonChoicesUnder witness target).length = 1 ∧
    (Causality.HedgeChannelInstallation.rightFullChoicesUnder witness target).length = 1 ∧
    (Causality.HedgeChannelInstallation.rightSurvivorsUnder witness target).length = 2 := by decide +kernel

/-- Literal full-small contributions change sign with the outcome and
vanish at a conflicting forced action value, without changing choice support. -/
theorem actual_small_term_values :
    fullSum target firstSample = 224 ∧ fullSum target secondSample = -224 ∧
      fullSum target conflictingSample = 0 := by decide +kernel

/-- Symbolic exact difference for every sample, including conflicting
forced values.  No sign or nonzero assertion is supplied as a premise. -/
theorem actual_numerator_difference (sample : signature.binary.Assignment) :
    (HedgeChannelTable.integratedNumerator graph 5 rightTables rightSignals target sample : Int) =
      (HedgeChannelTable.integratedNumerator graph 5 leftTables leftSignals target sample : Int) + fullSum target sample :=
  Causality.HedgeChannelInstallation.integratedNumerators_difference_of_action
    witness rich zeroSignal zeroSignal target false (by decide +kernel) sample

/-- Use the general projection identity at the original queried outcome
event, not a full-assignment event with the unqueried action fixed again. -/
theorem original_event_difference_formula :
    (HedgeChannelTable.eventNumerator graph 5 rightTables rightSignals target originalEvent : Int) =
      (HedgeChannelTable.eventNumerator graph 5 leftTables leftSignals target originalEvent : Int) +
      ((signature.binary.assignmentEnumeration.filter originalEvent).map (fullSum target)).sum :=
  Causality.HedgeChannelInstallation.eventNumerators_difference_of_action
    witness rich zeroSignal zeroSignal target false (by decide +kernel) originalEvent

/-- Actual original-outcome numerators retain a nonzero gap in this bow.
The conflicting full cell contributes zero, so it is not counted as a second
positive contribution merely because its outcome matches the event. -/
theorem original_event_values :
    HedgeChannelTable.eventNumerator graph 5 leftTables leftSignals target originalEvent = 10976 ∧
    HedgeChannelTable.eventNumerator graph 5 rightTables rightSignals target originalEvent = 11200 ∧
    ((signature.binary.assignmentEnumeration.filter originalEvent).map (fullSum target)).sum = 224 := by decide +kernel

/-- A forced small-forest row admits no full-small term.  Consistent
samples have the same literal prior mass, while conflicting ones remain zero. -/
theorem forced_small_boundary :
    (Causality.HedgeChannelInstallation.rightFullChoicesUnder witness bothForced).length = 0 ∧
    HedgeChannelTable.integratedNumerator graph 5 leftTables leftSignals bothForced firstSample = 32 ∧
    HedgeChannelTable.integratedNumerator graph 5 rightTables rightSignals bothForced firstSample = 32 ∧
    HedgeChannelTable.integratedNumerator graph 5 leftTables leftSignals bothForced secondSample = 0 ∧
    HedgeChannelTable.integratedNumerator graph 5 rightTables rightSignals bothForced secondSample = 0 := by decide +kernel

end HedgeChannelInterventional
end Examples
end Causality
end Thesis
