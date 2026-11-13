import Thesis.CausalTransport.BinaryInstrumental.NativeTransportation

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability
open FourLabelTransportation

/-!
# Universal binary-IV bounds on the actual treatment risks

For a requested outcome, both instrument arms expose its potential-outcome
mass.  Their overlap is bounded by the exact transportation cell capacity.
Subtracting that maximum overlap from the sum of the observed arm margins
gives the lower bound.  The upper success-risk bound is one minus the lower
bound for failure, using the same response record and its actual normalization.

The theorem ranges over every native SCM on the original hidden DAG, with
arbitrary finite alphabets and rational response denominators.  Only the two
instrument masses must be positive in this branch; all other cells may be
zero.  The computed-margin wrapper derives the required capacity witnesses
from the actual model, not from an externally assumed soundness interface.

These are universal bounds on unconditional intervention risks.  Sharpness
requires separate native endpoint constructions, and a null instrument value
requires a separate branch.  Neither obligation is asserted completed here.
-/

variable {P : FiniteLatentProjection signature}

def outcomeLowerMass (total : Nat) (rows columns : Masses) (action outcome : Bool) : Nat :=
  rows (riskEdge action outcome).1 + columns (riskEdge action outcome).2 -
    edgeCapacity total rows columns (riskEdge action outcome)

def riskLower (total : Nat) (positive : 0 < total) (rows columns : Masses) (action : Bool) : QProb :=
  ⟨outcomeLowerMass total rows columns action true, total, positive⟩

def riskUpper (total : Nat) (positive : 0 < total) (rows columns : Masses) (action : Bool) : QProb :=
  ⟨total - outcomeLowerMass total rows columns action false, total, positive⟩

/-- Universal raw lower bound for success *or* failure.  Cross multiplication
retains the original unknown response denominator; no observed-denominator
integrality assumption is made about the native model. -/
theorem native_outcome_lower_mass (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (arms : ArmMarginals law total positive rows columns)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true)
    (action outcome : Bool) :
    outcomeLowerMass total rows columns action outcome * (responseRepresentation native graphMatch).responses.den ≤
      FiniteProbRecord.eventMass (responseRepresentation native graphMatch).responses.atoms (outcomeEvent action outcome) * total := by
  let responses := (responseRepresentation native graphMatch).responses
  let source := nativeEdgeRecord native graphMatch
  let edge := riskEdge action outcome
  have exposure := response_outcome_exposure responses action outcome
  change aggregateRows source edge.1 + aggregateColumns source edge.2 ≤
    FiniteProbRecord.eventMass responses.atoms (outcomeEvent action outcome) + aggregateCells source edge.1 edge.2 at exposure
  have weighted := Nat.mul_le_mul_right total exposure
  simp only [Nat.add_mul] at weighted
  rw [native_row_relation native graphMatch law observed total positive rows columns arms falsePositive edge.1,
    native_column_relation native graphMatch law observed total positive rows columns arms truePositive edge.2] at weighted
  have overlap : aggregateCells source edge.1 edge.2 * total ≤ edgeCapacity total rows columns edge * source.den :=
    native_cell_bound native graphMatch law observed total positive rows columns margins arms falsePositive truePositive
      edge (riskEdge_different action outcome)
  have sumBound := Nat.le_trans weighted
    (Nat.add_le_add_left overlap (FiniteProbRecord.eventMass responses.atoms (outcomeEvent action outcome) * total))
  change (rows edge.1 + columns edge.2 - edgeCapacity total rows columns edge) * source.den ≤ _
  rw [Nat.sub_mul, Nat.add_mul]
  exact Nat.sub_le_of_le_add sumBound

/-- The record's success event is the genuine native treatment intervention
outcome.  It is not an observational conditional evaluated at that action. -/
theorem native_risk_response (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P) (action : Bool) :
    QProb.Equiv (native.interventionalValue (intervention action) (fun sample => sample y))
      ((responseRepresentation native graphMatch).responses.probVal (outcomeEvent action true)) :=
  QProb.equiv_trans ((responseRepresentation native graphMatch).interventional action)
    (QProb.equiv_trans (effectRecord_probVal _ action)
      ((responseRepresentation native graphMatch).responses.probVal_congr _ _
        (fun profile => (outcomeEvent_true profile action).symm)))

/-- Both sides bound every compatible original-DAG model.  The upper side
uses an exact Boolean partition on the same record, so a negative average
effect is not implicitly truncated by this risk calculation. -/
theorem native_risk_bounds (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (arms : ArmMarginals law total positive rows columns)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) (action : Bool) :
    QProb.LE (riskLower total positive rows columns action)
        (native.interventionalValue (intervention action) (fun sample => sample y)) ∧
      QProb.LE (native.interventionalValue (intervention action) (fun sample => sample y))
        (riskUpper total positive rows columns action) := by
  let responses := (responseRepresentation native graphMatch).responses
  have lower : QProb.LE (riskLower total positive rows columns action) (responses.probVal (outcomeEvent action true)) :=
    native_outcome_lower_mass native graphMatch law observed total positive rows columns margins arms falsePositive truePositive action true
  have upper : QProb.LE (responses.probVal (outcomeEvent action true)) (riskUpper total positive rows columns action) := by
    have failLower := native_outcome_lower_mass native graphMatch law observed total positive rows columns margins arms falsePositive truePositive action false
    have partition := congrArg (fun mass => mass * total) (outcomeEvent_partition responses action)
    simp only [Nat.add_mul] at partition
    have failBound : outcomeLowerMass total rows columns action false * responses.den ≤
        FiniteProbRecord.eventMass responses.atoms (outcomeEvent action false) * total := failLower
    change FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) * total ≤
      (total - outcomeLowerMass total rows columns action false) * responses.den
    rw [Nat.sub_mul]
    apply Nat.le_sub_of_add_le
    calc
      _ ≤ FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) * total +
          FiniteProbRecord.eventMass responses.atoms (outcomeEvent action false) * total := Nat.add_le_add_left failBound _
      _ = responses.den * total := partition
      _ = total * responses.den := Nat.mul_comm _ _
  have semantics := native_risk_response native graphMatch action
  exact ⟨QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_symm semantics) lower,
    QProb.le_congr (QProb.equiv_symm semantics) (QProb.equiv_refl _) upper⟩

/-- Native existence itself supplies the observed capacity certificate.
The user-facing bound therefore needs no separately selected feasible table
or externally supplied soundness witness for these computed margins. -/
def observedMarginsOfNative (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) :
    Margins (observedTotal law) (observedRows law) (observedColumns law) :=
  ⟨observedRows_total law, observedColumns_total law,
    native_observed_capacities native graphMatch law observed falsePositive truePositive⟩

theorem native_observed_risk_bounds (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) (action : Bool) :
    QProb.LE (riskLower (observedTotal law) (observedTotal_positive law falsePositive truePositive) (observedRows law) (observedColumns law) action)
        (native.interventionalValue (intervention action) (fun sample => sample y)) ∧
      QProb.LE (native.interventionalValue (intervention action) (fun sample => sample y))
        (riskUpper (observedTotal law) (observedTotal_positive law falsePositive truePositive) (observedRows law) (observedColumns law) action) :=
  native_risk_bounds native graphMatch law observed (observedTotal law) (observedTotal_positive law falsePositive truePositive)
    (observedRows law) (observedColumns law) (observedMarginsOfNative native graphMatch law observed falsePositive truePositive)
    (observedArmMarginals law falsePositive truePositive) falsePositive truePositive action

end BinaryInstrumental
end Causality
end Thesis
