import Thesis.CausalTransport.HedgeChannelSurvivors
import Thesis.Examples.HedgeChannelInstallation

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelSurvivors

open Probability

/-!
# Complete survivor reduction of an actually installed channel pair

The existing bow installer has twelve complete left row choices but only
four canonical survivors.  The right has four complete choices and four
canonical survivors.  Those four terms on either side still include both
ordinary background masks: the reduction must not discard their interaction
with a full main channel or repeat a mask on a consumed row.

The symbolic reduction theorem identifies the actual likelihood numerator
with that repetition-free sum.  Separate literal signed-mass checks display
the full-channel contributions for two factual action values; changing that
value changes the contribution despite observational equality of the pair.
The equality criterion is also exercised at every observed assignment using
the earlier complete actual integration check.

Only finite row choices and the thirty-two actual shared root vectors are
evaluated.  No private response-function prior or full general graph scan is
reduced.  These checks do not replace the separate arbitrary-hedge coefficient
and sum assembly in `HedgeChannelObservational`, or the still-open original-
outcome flow argument.
-/

private def signature := HedgeChannelConstruction.signature
private def graph := HedgeChannelConstruction.graph
private def witness := HedgeChannelConstruction.witness
private def rich := HedgeChannelConstruction.rich
private def zeroSignal (_child : Fin signature.count) (_parents : signature.binary.ParentValues _child) : Bool := false
private def leftTables := Causality.HedgeChannelInstallation.leftTables witness
private def rightTables := Causality.HedgeChannelInstallation.rightTables witness
private def leftSignals := Causality.HedgeChannelInstallation.leftSignals witness rich zeroSignal zeroSignal
private def rightSignals := Causality.HedgeChannelInstallation.rightSignals witness zeroSignal zeroSignal

/-- The full left expansion has eight terms proved zero by integration;
the complete right expansion already has the four canonical forms. -/
theorem complete_choice_counts :
    (FiniteProduct.enumeration signature.count (fun _ => Option (Fin 5))
      (fun child => (leftTables child).expansionChoicesUnder none)).length = 12 ∧
      (FiniteProduct.enumeration signature.count (fun _ => Option (Fin 5))
        (fun child => (rightTables child).expansionChoicesUnder none)).length = 4 := by decide +kernel

/-- The canonical lists retain both background masks and both applicable
main contributions, without duplicate descriptions on consumed rows. -/
theorem survivor_counts :
    (Causality.HedgeChannelInstallation.leftSurvivors witness).length = 4 ∧
      (Causality.HedgeChannelInstallation.rightSurvivors witness).length = 4 := by decide +kernel

/-- Exact reduction for the actual left likelihood numerator, symbolic in
the entire factual observed assignment rather than one chosen cell. -/
theorem actual_left_reduction (sample : signature.binary.Assignment) :
    (Causality.HedgeChannelTable.integratedNumerator graph 5 leftTables leftSignals (fun _ => none) sample : Int) =
      ((Causality.HedgeChannelInstallation.leftSurvivors witness).map
        (Causality.HedgeChannelInstallation.leftTermIntegral witness rich zeroSignal zeroSignal sample)).sum :=
  Causality.HedgeChannelInstallation.left_integratedNumerator_survivors witness rich zeroSignal zeroSignal sample

theorem actual_right_reduction (sample : signature.binary.Assignment) :
    (Causality.HedgeChannelTable.integratedNumerator graph 5 rightTables rightSignals (fun _ => none) sample : Int) =
      ((Causality.HedgeChannelInstallation.rightSurvivors witness).map
        (Causality.HedgeChannelInstallation.rightTermIntegral witness zeroSignal zeroSignal sample)).sum :=
  Causality.HedgeChannelInstallation.right_integratedNumerator_survivors witness zeroSignal zeroSignal sample

private def firstSample : signature.binary.Assignment := fun _ => false
private def secondSample : signature.binary.Assignment := fun child => decide (child.val = 0)

private def leftFullSum (sample : signature.binary.Assignment) : Int :=
  ((Causality.HedgeChannelInstallation.leftFullChoices witness).map
    (Causality.HedgeChannelInstallation.leftTermIntegral witness rich zeroSignal zeroSignal sample)).sum
private def rightFullSum (sample : signature.binary.Assignment) : Int :=
  ((Causality.HedgeChannelInstallation.rightFullChoices witness).map
    (Causality.HedgeChannelInstallation.rightTermIntegral witness zeroSignal zeroSignal sample)).sum

/-- Literal full-channel integrals retain the complete root-prior mass.
The two models agree, but their common contribution depends on the original
action coordinate through its ordinary background character. -/
theorem full_channel_contributions :
    leftFullSum firstSample = 87808 ∧ rightFullSum firstSample = 87808 ∧
      leftFullSum secondSample = 65856 ∧ rightFullSum secondSample = 65856 := by decide +kernel

/-- Exercise the general criterion for every observed assignment, using
the earlier actual full integration check and the exact numerator bridge.
Neither equality of background blocks nor one literal cell is substituted
for the full-sample premise. -/
theorem actual_full_sums_equal (sample : signature.binary.Assignment) : leftFullSum sample = rightFullSum sample := by
  apply (Causality.HedgeChannelInstallation.expandedIntegrals_eq_iff_fullSums
    witness rich zeroSignal zeroSignal sample).mp
  exact (Causality.HedgeChannelTable.integratedNumerator_expansion graph 5 leftTables leftSignals
    (fun _ => none) sample).symm.trans
    ((congrArg (fun numerator : Nat => (numerator : Int))
      (HedgeChannelInstallation.actual_integrated_numerators_equal sample)).trans
      (Causality.HedgeChannelTable.integratedNumerator_expansion graph 5 rightTables rightSignals (fun _ => none) sample))

end HedgeChannelSurvivors
end Examples
end Causality
end Thesis
