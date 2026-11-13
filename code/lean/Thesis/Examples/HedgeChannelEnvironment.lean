import Thesis.Examples.HedgeChannelLatentBoundary
import Thesis.CausalTransport.HedgeChannelEnvironmentCounterexample

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelEnvironment

open Probability
open HedgeChannelLatentBoundary
open HedgeChannelEnvironmentInstallation
open HedgeChannelInstallation (channelCount leftTables rightTables)

/-!
# A genuine latent-entry gap in the widened independent-channel family

The unchanged original graph is `A -> R`, `A <-> R`, `U <-> R`, and the
unchanged query is `P(U | do(A), R)` on three-valued observed domains.  The
boundary fixture proves that every observed-parent-only signal pair in the
old installation agrees on this entire conditional query.

The widened pair has a different local input: the independent reserved bit
at the actual `U <-> R` root.  The small signal at `R` and background signal
at `U` both read that bit, with their actual incidence proofs.  Neither row
reads the other's observed value, and the main forest channel coordinates
remain independent of this genuine shared-input coordinate.

The four actual fixed-environment mass identities from the boundary module
are integrated over every environment assignment.  Its linear characters
cancel, while their small/background interaction survives.  Thus the whole
conditioning mass matches after integration but the joint cylinder differs.
The actual SCM conditional cells consequently differ, although the pair's
entire observational laws match by the general installation theorem.

Only the four reserved-bit assignments at the two original pair roots are
reduced here.  The literal main-prior mass is retained symbolically; neither
the main shared support nor the private response-function support is reduced.
The final countermodel retains all original three-valued labels through the
general source-cell refinement.  This verifies that the widened family
overcomes the known latent-entry obstruction, not that every irreducible
active path already has a separating signal construction.
-/

/-! ## The actual shared root and legitimate endpoint reads -/

/-- The first actual pair root is the declared `U <-> R` source.  Its finite
index is displayed explicitly, rather than selected from an existence proof. -/
def readoutRoot : Fin (pairRootCount graph.binary) := ⟨0, by decide +kernel⟩

theorem readout_incident_outcome : pairRootIncident graph.binary readoutRoot outcomeNode = true := by decide +kernel
theorem readout_incident_root : pairRootIncident graph.binary readoutRoot rootNode = true := by decide +kernel

/-- `R` reads only its genuine incident reserved bit, not observed `U`.
Every other small-signal row is zero, including the intervened action row. -/
def smallSignal : ParentSignal graph := fun child _parents inputs =>
  if atRoot : child = rootNode then inputs readoutRoot (by rw [atRoot]; exact readout_incident_root) else false

/-- `U` reads the same genuine root bit through its own incidence proof.
No new shared source or undeclared directed parent is supplied to either row. -/
def backgroundSignal : ParentSignal graph := fun child _parents inputs =>
  if atOutcome : child = outcomeNode then inputs readoutRoot (by rw [atOutcome]; exact readout_incident_outcome) else false

private theorem frozen_small_read (environment : PairRootChannels.Environment.Assignment graph.binary) :
    rootSignalAtFalse (frozenParentSignal smallSignal environment) = environment readoutRoot := by
  simp only [rootSignalAtFalse, frozenParentSignal, smallSignal, dite_true]

private theorem frozen_background_read (environment : PairRootChannels.Environment.Assignment graph.binary) :
    outcomeSignalAtFalse (frozenParentSignal backgroundSignal environment) = environment readoutRoot := by
  simp only [outcomeSignalAtFalse, frozenParentSignal, backgroundSignal, dite_true]

/-- The supplied source reference fixes the actual intervention at `A`.
Both numerator and conditioning events use this very reference. -/
def sourceReference : signature.binary.Assignment := reference false false false

-- These aliases are conveniences for local calculations only.  Public mass
-- and cell statements spell out the query operations directly: comparing
-- argument aliases inside a closed integral can otherwise trigger reduction
-- of the much larger shared support before the checker sees the same event.
private abbrev target := query.binary.operationKernel.intervention sourceReference
private abbrev jointEvent := query.binary.operationKernel.numeratorEvent sourceReference
private abbrev conditionEvent := query.binary.operationKernel.conditionEvent sourceReference
private def mainMass : Int := (PairRootChannels.prior graph.binary (channelCount witness)).den

/-! ## Exact sums on the small reserved-bit support -/

private theorem left_joint_sum :
    ((PairRootChannels.Environment.enumeration graph.binary).map (fun environment =>
      (16777216 : Int) + 2097152 * FiniteProbRecord.characterSign (environment readoutRoot))).sum = 67108864 := by
  decide +kernel

private theorem left_condition_sum :
    ((PairRootChannels.Environment.enumeration graph.binary).map (fun _environment => (33554432 : Int))).sum = 134217728 := by
  decide +kernel

private theorem right_joint_sum :
    ((PairRootChannels.Environment.enumeration graph.binary).map (fun environment =>
      ((16777216 : Int) + 2097152 * FiniteProbRecord.characterSign (environment readoutRoot)) +
        FiniteProbRecord.characterSign (environment readoutRoot) *
          (262144 + 32768 * FiniteProbRecord.characterSign (environment readoutRoot)))).sum = 67239936 := by
  decide +kernel

private theorem right_condition_sum :
    ((PairRootChannels.Environment.enumeration graph.binary).map (fun environment =>
      (33554432 : Int) + 524288 * FiniteProbRecord.characterSign (environment readoutRoot))).sum = 134217728 := by
  decide +kernel

private theorem castMapSum {α : Type} (values : List α) (term : α -> Nat) :
    (((values.map term).sum : Nat) : Int) = (values.map (fun value => (term value : Int))).sum := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, Int.natCast_add, inductionHypothesis]

/-- The complete actual left joint mass after environment integration.
The main prior's possibly large normalization is never evaluated. -/
theorem left_joint_mass :
    (leftEventNumerator witness rich smallSignal backgroundSignal
      (query.binary.operationKernel.intervention sourceReference)
      (query.binary.operationKernel.numeratorEvent sourceReference) : Int) = mainMass * 67108864 := by
  unfold leftEventNumerator
  rw [castMapSum]
  have rows :
      ((PairRootChannels.Environment.enumeration graph.binary).map (fun environment =>
        (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
          (HedgeChannelInstallation.leftSignals witness rich (frozenParentSignal smallSignal environment)
            (frozenParentSignal backgroundSignal environment))
              (query.binary.operationKernel.intervention sourceReference)
              (query.binary.operationKernel.numeratorEvent sourceReference) : Int))) =
      ((PairRootChannels.Environment.enumeration graph.binary).map (fun environment =>
        mainMass * (16777216 + 2097152 * FiniteProbRecord.characterSign (environment readoutRoot)))) := by
    apply List.map_congr_left
    intro environment _listed
    exact (left_joint_numerator_at_false (frozenParentSignal smallSignal environment)
      (frozenParentSignal backgroundSignal environment)).trans (by rw [frozen_background_read]; rfl)
  rw [rows, FiniteSupportedSum.sum_mul_left, left_joint_sum]

/-- The complete actual left conditioning mass, including every outcome
value and every zero inconsistent-action cell before projection. -/
theorem left_condition_mass :
    (leftEventNumerator witness rich smallSignal backgroundSignal
      (query.binary.operationKernel.intervention sourceReference)
      (query.binary.operationKernel.conditionEvent sourceReference) : Int) = mainMass * 134217728 := by
  unfold leftEventNumerator
  rw [castMapSum]
  have rows :
      ((PairRootChannels.Environment.enumeration graph.binary).map (fun environment =>
        (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
          (HedgeChannelInstallation.leftSignals witness rich (frozenParentSignal smallSignal environment)
            (frozenParentSignal backgroundSignal environment))
              (query.binary.operationKernel.intervention sourceReference)
              (query.binary.operationKernel.conditionEvent sourceReference) : Int))) =
      ((PairRootChannels.Environment.enumeration graph.binary).map (fun _environment => mainMass * 33554432)) := by
    apply List.map_congr_left
    intro environment _listed
    exact left_condition_numerator_at_false (frozenParentSignal smallSignal environment)
      (frozenParentSignal backgroundSignal environment)
  rw [rows, FiniteSupportedSum.sum_mul_left, left_condition_sum]

/-- The shared small/background interaction survives in the complete
right joint mass.  The baseline and every permitted full-small term are
retained through the previously proved actual action-cut change identity. -/
theorem right_joint_mass :
    (rightEventNumerator witness smallSignal backgroundSignal
      (query.binary.operationKernel.intervention sourceReference)
      (query.binary.operationKernel.numeratorEvent sourceReference) : Int) = mainMass * 67239936 := by
  unfold rightEventNumerator
  rw [castMapSum]
  have rows :
      ((PairRootChannels.Environment.enumeration graph.binary).map (fun environment =>
        (HedgeChannelTable.eventNumerator graph (channelCount witness) (rightTables witness)
          (HedgeChannelInstallation.rightSignals witness (frozenParentSignal smallSignal environment)
            (frozenParentSignal backgroundSignal environment))
              (query.binary.operationKernel.intervention sourceReference)
              (query.binary.operationKernel.numeratorEvent sourceReference) : Int))) =
      ((PairRootChannels.Environment.enumeration graph.binary).map (fun environment =>
        mainMass * ((16777216 + 2097152 * FiniteProbRecord.characterSign (environment readoutRoot)) +
          FiniteProbRecord.characterSign (environment readoutRoot) *
            (262144 + 32768 * FiniteProbRecord.characterSign (environment readoutRoot))))) := by
    apply List.map_congr_left
    intro environment _listed
    have changed := HedgeChannelInstallation.eventNumerator_change witness rich
      (frozenParentSignal smallSignal environment) (frozenParentSignal backgroundSignal environment)
        (query.binary.operationKernel.intervention sourceReference) false (by rfl)
        (query.binary.operationKernel.numeratorEvent sourceReference)
    have left :
        (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
          (HedgeChannelInstallation.leftSignals witness rich (frozenParentSignal smallSignal environment)
            (frozenParentSignal backgroundSignal environment))
              (query.binary.operationKernel.intervention sourceReference)
              (query.binary.operationKernel.numeratorEvent sourceReference) : Int) =
          mainMass * (16777216 + 2097152 * FiniteProbRecord.characterSign (environment readoutRoot)) :=
      (left_joint_numerator_at_false (frozenParentSignal smallSignal environment)
        (frozenParentSignal backgroundSignal environment)).trans (by rw [frozen_background_read]; rfl)
    have delta : HedgeChannelInstallation.projectedEventChange witness (frozenParentSignal smallSignal environment)
        (frozenParentSignal backgroundSignal environment)
          (query.binary.operationKernel.intervention sourceReference)
          (query.binary.operationKernel.numeratorEvent sourceReference) =
      mainMass * (FiniteProbRecord.characterSign (environment readoutRoot) *
        (262144 + 32768 * FiniteProbRecord.characterSign (environment readoutRoot))) :=
      (joint_change_at_false (frozenParentSignal smallSignal environment)
        (frozenParentSignal backgroundSignal environment)).trans (by rw [frozen_small_read, frozen_background_read]; rfl)
    rw [left, delta] at changed
    exact changed.trans (Int.mul_add _ _ _).symm
  rw [rows, FiniteSupportedSum.sum_mul_left, right_joint_sum]

/-- The evidence change cancels only after the entire environment has
been integrated.  This proves the matched marginal for these actual signals;
it is not imported as a premise from the frozen conditional comparisons. -/
theorem right_condition_mass :
    (rightEventNumerator witness smallSignal backgroundSignal
      (query.binary.operationKernel.intervention sourceReference)
      (query.binary.operationKernel.conditionEvent sourceReference) : Int) = mainMass * 134217728 := by
  unfold rightEventNumerator
  rw [castMapSum]
  have rows :
      ((PairRootChannels.Environment.enumeration graph.binary).map (fun environment =>
        (HedgeChannelTable.eventNumerator graph (channelCount witness) (rightTables witness)
          (HedgeChannelInstallation.rightSignals witness (frozenParentSignal smallSignal environment)
            (frozenParentSignal backgroundSignal environment))
              (query.binary.operationKernel.intervention sourceReference)
              (query.binary.operationKernel.conditionEvent sourceReference) : Int))) =
      ((PairRootChannels.Environment.enumeration graph.binary).map (fun environment =>
        mainMass * (33554432 + 524288 * FiniteProbRecord.characterSign (environment readoutRoot)))) := by
    apply List.map_congr_left
    intro environment _listed
    have changed := HedgeChannelInstallation.eventNumerator_change witness rich
      (frozenParentSignal smallSignal environment) (frozenParentSignal backgroundSignal environment)
        (query.binary.operationKernel.intervention sourceReference) false (by rfl)
        (query.binary.operationKernel.conditionEvent sourceReference)
    have left :
        (HedgeChannelTable.eventNumerator graph (channelCount witness) (leftTables witness)
          (HedgeChannelInstallation.leftSignals witness rich (frozenParentSignal smallSignal environment)
            (frozenParentSignal backgroundSignal environment))
              (query.binary.operationKernel.intervention sourceReference)
              (query.binary.operationKernel.conditionEvent sourceReference) : Int) = mainMass * 33554432 :=
      left_condition_numerator_at_false (frozenParentSignal smallSignal environment)
        (frozenParentSignal backgroundSignal environment)
    have delta : HedgeChannelInstallation.projectedEventChange witness (frozenParentSignal smallSignal environment)
        (frozenParentSignal backgroundSignal environment)
          (query.binary.operationKernel.intervention sourceReference)
          (query.binary.operationKernel.conditionEvent sourceReference) =
      mainMass * (524288 * FiniteProbRecord.characterSign (environment readoutRoot)) :=
      (condition_change_at_false (frozenParentSignal smallSignal environment)
        (frozenParentSignal backgroundSignal environment)).trans (by rw [frozen_small_read]; rfl)
    rw [left, delta] at changed
    exact changed.trans (Int.mul_add _ _ _).symm
  rw [rows, FiniteSupportedSum.sum_mul_left, right_condition_sum]

/-- A genuine cross-product inequality for the actual integrated source
cells.  Positivity supports cancellation of the common conditioning mass;
the remaining unequal joint masses have the same positive symbolic prior. -/
theorem cross_separated :
    leftEventNumerator witness rich smallSignal backgroundSignal
      (query.binary.operationKernel.intervention sourceReference)
      (query.binary.operationKernel.numeratorEvent sourceReference) *
        rightEventNumerator witness smallSignal backgroundSignal
          (query.binary.operationKernel.intervention sourceReference)
          (query.binary.operationKernel.conditionEvent sourceReference) ≠
      rightEventNumerator witness smallSignal backgroundSignal
        (query.binary.operationKernel.intervention sourceReference)
        (query.binary.operationKernel.numeratorEvent sourceReference) *
        leftEventNumerator witness rich smallSignal backgroundSignal
          (query.binary.operationKernel.intervention sourceReference)
          (query.binary.operationKernel.conditionEvent sourceReference) := by
  intro equal
  have matched : rightEventNumerator witness smallSignal backgroundSignal
    (query.binary.operationKernel.intervention sourceReference)
    (query.binary.operationKernel.conditionEvent sourceReference) =
      leftEventNumerator witness rich smallSignal backgroundSignal
        (query.binary.operationKernel.intervention sourceReference)
        (query.binary.operationKernel.conditionEvent sourceReference) :=
    Int.ofNat_inj.mp (right_condition_mass.trans left_condition_mass.symm)
  have positive : 0 < mainMass := Int.natCast_pos.mpr (PairRootChannels.prior graph.binary (channelCount witness)).den_pos
  have supported : 0 < leftEventNumerator witness rich smallSignal backgroundSignal
    (query.binary.operationKernel.intervention sourceReference)
    (query.binary.operationKernel.conditionEvent sourceReference) := by
    have cast := left_condition_mass
    omega
  rw [matched] at equal
  have jointEqual := Nat.eq_of_mul_eq_mul_right supported equal
  have cast := congrArg (fun value : Nat => (value : Int)) jointEqual
  have scalarEqual : mainMass * 67108864 = mainMass * 67239936 :=
    left_joint_mass.symm.trans (cast.trans right_joint_mass)
  omega

end HedgeChannelEnvironment
end Examples
end Causality
end Thesis
