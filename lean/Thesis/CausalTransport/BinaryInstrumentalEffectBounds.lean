import Thesis.CausalTransport.BinaryInstrumentalRiskEndpoints
import Thesis.CausalTransport.BinaryInstrumentalEffect

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability
open FourLabelTransportation

/-!
# Sharp bounds on the signed binary-IV average treatment effect

The objective remains the increasing affine score `(ATE + 1) / 2`, not
truncated subtraction of nonnegative rational presentations.  Its two
components are success under treatment and failure under control.  Lower
bounds on those two events therefore give a lower score; the complementary
event bounds give the upper score.  Every inequality uses one response
record extracted from the actual native model, with its unrestricted finite
alphabets and rational denominator.

Sharpness is a separate, constructive obligation.  The lower score uses
the corner with upper control risk and lower treated risk; the upper score
uses the opposite corner.  Each corner comes from one transportation table
and one response record, not a difference between unrelated witnesses.
Both resulting SCMs agree on the entire observed law on the original DAG.

Only the two instrument masses must be positive in this branch.  All eight
other cell values and any selected capacity may vanish.  The score can be
below one half and thus represent a negative ATE; its exact signed decoding
is `responseEffectScore_signed`.  A null instrument value is handled by a
separate branch, never by dividing a zero marginal or assigning it a fake
observed conditional.
-/

variable {P : FiniteLatentProjection signature}

def effectLowerMass (total : Nat) (rows columns : Masses) : Nat :=
  outcomeLowerMass total rows columns true true + outcomeLowerMass total rows columns false false

def effectUpperMass (total : Nat) (rows columns : Masses) : Nat :=
  (total - outcomeLowerMass total rows columns true false) +
    (total - outcomeLowerMass total rows columns false true)

/-- These endpoints encode signed effects by `(ATE + 1) / 2`.  The doubled
positive denominator is shared by both displayed scores. -/
def effectLower (total : Nat) (positive : 0 < total) (rows columns : Masses) : QProb :=
  ⟨effectLowerMass total rows columns, 2 * total, Nat.mul_pos (by decide) positive⟩

def effectUpper (total : Nat) (positive : 0 < total) (rows columns : Masses) : QProb :=
  ⟨effectUpperMass total rows columns, 2 * total, Nat.mul_pos (by decide) positive⟩

/-- The score's two raw components are treatment success and control failure
on the same record.  This identity also serves the null-instrument branch. -/
theorem responseEffectScore_numerator (responses : FiniteProbRecord Profile) :
    (responseEffectScore responses).num =
      FiniteProbRecord.eventMass responses.atoms (outcomeEvent true true) +
        FiniteProbRecord.eventMass responses.atoms (outcomeEvent false false) := by
  have treated := FiniteProbRecord.eventMass_congr responses.atoms
    (fun profile => outcomeAt profile true) (outcomeEvent true true)
    (fun profile => (outcomeEvent_true profile true).symm)
  have control := FiniteProbRecord.eventMass_congr responses.atoms
    (fun profile => !outcomeAt profile false) (outcomeEvent false false)
    (fun profile => ((outcomeEvent_false profile false).trans
      (congrArg Bool.not (outcomeEvent_true profile false))).symm)
  change _ + _ = _ + _
  rw [treated, control]

/-- Boolean normalization turns a bound on the complementary response into
an upper bound on this response.  Both masses are from the same record. -/
theorem outcome_upper_mass_of_complement_lower (responses : FiniteProbRecord Profile) (total bound : Nat)
    (action outcome : Bool)
    (lowerComplement : bound * responses.den ≤
      FiniteProbRecord.eventMass responses.atoms (outcomeEvent action (!outcome)) * total) :
    FiniteProbRecord.eventMass responses.atoms (outcomeEvent action outcome) * total ≤
      (total - bound) * responses.den := by
  have partition :
      FiniteProbRecord.eventMass responses.atoms (outcomeEvent action outcome) +
        FiniteProbRecord.eventMass responses.atoms (outcomeEvent action (!outcome)) = responses.den := by
    cases outcome
    · simpa only [Bool.not_false, Nat.add_comm] using outcomeEvent_partition responses action
    · exact outcomeEvent_partition responses action
  have weighted := congrArg (fun mass => mass * total) partition
  simp only [Nat.add_mul] at weighted
  rw [Nat.sub_mul]
  apply Nat.le_sub_of_add_le
  calc
    _ ≤ FiniteProbRecord.eventMass responses.atoms (outcomeEvent action outcome) * total +
        FiniteProbRecord.eventMass responses.atoms (outcomeEvent action (!outcome)) * total :=
      Nat.add_le_add_left lowerComplement _
    _ = responses.den * total := weighted
    _ = total * responses.den := Nat.mul_comm _ _

/-- Universal bounds on the actual signed-effect encoding.  They retain
the unknown native denominator, rather than optimizing just an observed
integer grid or assuming independently attained risk endpoints coexist. -/
theorem native_effect_bounds (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (arms : ArmMarginals law total positive rows columns)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) :
    QProb.LE (effectLower total positive rows columns) (nativeEffectScore native) ∧
      QProb.LE (nativeEffectScore native) (effectUpper total positive rows columns) := by
  let responses := (responseRepresentation native graphMatch).responses
  let treated := FiniteProbRecord.eventMass responses.atoms (outcomeEvent true true)
  let controlFailure := FiniteProbRecord.eventMass responses.atoms (outcomeEvent false false)
  have lowerTreated : outcomeLowerMass total rows columns true true * responses.den ≤ treated * total :=
    native_outcome_lower_mass native graphMatch law observed total positive rows columns margins arms falsePositive truePositive true true
  have lowerControl : outcomeLowerMass total rows columns false false * responses.den ≤ controlFailure * total :=
    native_outcome_lower_mass native graphMatch law observed total positive rows columns margins arms falsePositive truePositive false false
  have upperTreated : treated * total ≤ (total - outcomeLowerMass total rows columns true false) * responses.den :=
    outcome_upper_mass_of_complement_lower responses total (outcomeLowerMass total rows columns true false) true true
      (native_outcome_lower_mass native graphMatch law observed total positive rows columns margins arms falsePositive truePositive true false)
  have upperControl : controlFailure * total ≤ (total - outcomeLowerMass total rows columns false true) * responses.den :=
    outcome_upper_mass_of_complement_lower responses total (outcomeLowerMass total rows columns false true) false false
      (native_outcome_lower_mass native graphMatch law observed total positive rows columns margins arms falsePositive truePositive false true)
  have scoreNumerator : (responseEffectScore responses).num = treated + controlFailure := by
    exact responseEffectScore_numerator responses
  have lower : QProb.LE (effectLower total positive rows columns) (responseEffectScore responses) := by
    change effectLowerMass total rows columns * (2 * responses.den) ≤
      (responseEffectScore responses).num * (2 * total)
    rw [scoreNumerator]
    calc
      _ = 2 * (outcomeLowerMass total rows columns true true * responses.den +
          outcomeLowerMass total rows columns false false * responses.den) := by
        simp only [effectLowerMass, Nat.add_mul, Nat.mul_add]
        ac_rfl
      _ ≤ 2 * (treated * total + controlFailure * total) :=
        Nat.mul_le_mul_left 2 (Nat.add_le_add lowerTreated lowerControl)
      _ = (treated + controlFailure) * (2 * total) := by
        simp only [Nat.add_mul, Nat.mul_add]
        ac_rfl
  have upper : QProb.LE (responseEffectScore responses) (effectUpper total positive rows columns) := by
    change (responseEffectScore responses).num * (2 * total) ≤
      effectUpperMass total rows columns * (2 * responses.den)
    rw [scoreNumerator]
    calc
      _ = 2 * (treated * total + controlFailure * total) := by
        simp only [Nat.add_mul, Nat.mul_add]
        ac_rfl
      _ ≤ 2 * ((total - outcomeLowerMass total rows columns true false) * responses.den +
          (total - outcomeLowerMass total rows columns false true) * responses.den) :=
        Nat.mul_le_mul_left 2 (Nat.add_le_add upperTreated upperControl)
      _ = effectUpperMass total rows columns * (2 * responses.den) := by
        simp only [effectUpperMass, Nat.add_mul, Nat.mul_add]
        ac_rfl
  have semantics := nativeEffectScore_response native graphMatch
  exact ⟨QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_symm semantics) lower,
    QProb.le_congr (QProb.equiv_symm semantics) (QProb.equiv_refl _) upper⟩

/-- Subtracting the same cleared unit mass preserves an integer inequality.
This is the signed decoding step; natural subtraction is deliberately absent. -/
private theorem signed_order (left total right denominator : Nat)
    (ordered : left * denominator ≤ right * total) :
    ((left : Int) - (total : Int)) * (denominator : Int) ≤
      ((right : Int) - (denominator : Int)) * (total : Int) := by
  have cast : ((left * denominator : Nat) : Int) ≤ ((right * total : Nat) : Int) := by omega
  simp only [Int.natCast_mul] at cast
  rw [Int.sub_mul, Int.sub_mul, Int.mul_comm (total : Int) (denominator : Int)]
  omega

/-- Literal signed ATE bounds, with no affine notation left in the target.
The response numerator is the actual potential-outcome change summed on
one native model's extracted prior.  Dividing all three cross-products by
the positive product of denominators gives the usual signed interval.
Thus the score theorem is not merely a bound on an unrelated probability.
-/
theorem native_signed_effect_bounds (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (arms : ArmMarginals law total positive rows columns)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) :
    ((effectLowerMass total rows columns : Int) - (total : Int)) *
          ((responseRepresentation native graphMatch).responses.den : Int) ≤
        (responseRepresentation native graphMatch).responses.signedMass effectChange * (total : Int) ∧
      (responseRepresentation native graphMatch).responses.signedMass effectChange * (total : Int) ≤
        ((effectUpperMass total rows columns : Int) - (total : Int)) *
          ((responseRepresentation native graphMatch).responses.den : Int) := by
  let responses := (responseRepresentation native graphMatch).responses
  have bounds := native_effect_bounds native graphMatch law observed total positive rows columns
    margins arms falsePositive truePositive
  have semantics := nativeEffectScore_response native graphMatch
  have lower := QProb.le_congr (QProb.equiv_refl _) semantics bounds.1
  have upper := QProb.le_congr semantics (QProb.equiv_refl _) bounds.2
  change effectLowerMass total rows columns * (2 * responses.den) ≤
    (responseEffectScore responses).num * (2 * total) at lower
  change (responseEffectScore responses).num * (2 * total) ≤
    effectUpperMass total rows columns * (2 * responses.den) at upper
  have lowerTwice : (effectLowerMass total rows columns * responses.den) * 2 ≤
      ((responseEffectScore responses).num * total) * 2 := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using lower
  have upperTwice : ((responseEffectScore responses).num * total) * 2 ≤
      (effectUpperMass total rows columns * responses.den) * 2 := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using upper
  have lowerSigned := signed_order (effectLowerMass total rows columns) total
    (responseEffectScore responses).num responses.den
    (Nat.le_of_mul_le_mul_right lowerTwice (by decide))
  have upperSigned := signed_order (responseEffectScore responses).num responses.den
    (effectUpperMass total rows columns) total
    (Nat.le_of_mul_le_mul_right upperTwice (by decide))
  rw [responseEffectScore_signed] at lowerSigned upperSigned
  exact ⟨lowerSigned, upperSigned⟩

private theorem lower_endpoint_score (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) :
    QProb.Equiv
      (responseEffectScore (endpointResponses total positive rows columns margins
        (endpointTable total rows columns margins true false) true false))
      (effectLower total positive rows columns) := by
  let table := endpointTable total rows columns margins true false
  let responses := endpointResponses total positive rows columns margins table true false
  have treated : FiniteProbRecord.eventMass responses.atoms (outcomeEvent true true) =
      outcomeLowerMass total rows columns true true :=
    endpoint_selected_outcome_mass total positive rows columns margins table true false true
      (endpointTable_attains total rows columns margins true false true)
  have controlFailure : FiniteProbRecord.eventMass responses.atoms (outcomeEvent false false) =
      outcomeLowerMass total rows columns false false :=
    endpoint_selected_outcome_mass total positive rows columns margins table true false false
      (endpointTable_attains total rows columns margins true false false)
  change (responseEffectScore responses).num * (2 * total) = effectLowerMass total rows columns * (2 * total)
  rw [responseEffectScore_numerator, treated, controlFailure]
  rfl

private theorem upper_endpoint_score (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) :
    QProb.Equiv
      (responseEffectScore (endpointResponses total positive rows columns margins
        (endpointTable total rows columns margins false true) false true))
      (effectUpper total positive rows columns) := by
  let table := endpointTable total rows columns margins false true
  let responses := endpointResponses total positive rows columns margins table false true
  have treatedFailure : FiniteProbRecord.eventMass responses.atoms (outcomeEvent true false) =
      outcomeLowerMass total rows columns true false :=
    endpoint_selected_outcome_mass total positive rows columns margins table false true true
      (endpointTable_attains total rows columns margins false true true)
  have controlSuccess : FiniteProbRecord.eventMass responses.atoms (outcomeEvent false true) =
      outcomeLowerMass total rows columns false true :=
    endpoint_selected_outcome_mass total positive rows columns margins table false true false
      (endpointTable_attains total rows columns margins false true false)
  have treatedPartition := outcomeEvent_partition responses true
  have controlPartition := outcomeEvent_partition responses false
  rw [treatedFailure] at treatedPartition
  rw [controlSuccess] at controlPartition
  change _ + _ = total at treatedPartition
  change _ + _ = total at controlPartition
  have treated : FiniteProbRecord.eventMass responses.atoms (outcomeEvent true true) =
      total - outcomeLowerMass total rows columns true false := by omega
  have controlFailure : FiniteProbRecord.eventMass responses.atoms (outcomeEvent false false) =
      total - outcomeLowerMass total rows columns false true := by omega
  change (responseEffectScore responses).num * (2 * total) = effectUpperMass total rows columns * (2 * total)
  rw [responseEffectScore_numerator, treated, controlFailure]
  rfl

/-- Both signed-effect endpoints have actual original-DAG witnesses with
the entire supplied law.  Each witness realizes its two opposing risks in
one model; this is the sharpness certificate complementing universal bounds. -/
theorem native_effect_endpoints_attainable (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (arms : ArmMarginals law total positive rows columns) :
    EffectScoreAttainableAt projection law (effectLower total positive rows columns) ∧
      EffectScoreAttainableAt projection law (effectUpper total positive rows columns) := by
  constructor
  · apply (effectScoreAttainableAt_iff projection graphMatch law _).mpr
    refine ⟨endpointResponses total positive rows columns margins (endpointTable total rows columns margins true false) true false,
      transportationResponses_feasible law total positive rows columns margins arms
        (endpointTable total rows columns margins true false) (endpointFill true false), ?_⟩
    exact lower_endpoint_score total positive rows columns margins
  · apply (effectScoreAttainableAt_iff projection graphMatch law _).mpr
    refine ⟨endpointResponses total positive rows columns margins (endpointTable total rows columns margins false true) false true,
      transportationResponses_feasible law total positive rows columns margins arms
        (endpointTable total rows columns margins false true) (endpointFill false true), ?_⟩
    exact upper_endpoint_score total positive rows columns margins

theorem native_observed_effect_bounds (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) :
    QProb.LE (effectLower (observedTotal law) (observedTotal_positive law falsePositive truePositive)
        (observedRows law) (observedColumns law)) (nativeEffectScore native) ∧
      QProb.LE (nativeEffectScore native)
        (effectUpper (observedTotal law) (observedTotal_positive law falsePositive truePositive)
          (observedRows law) (observedColumns law)) :=
  native_effect_bounds native graphMatch law observed (observedTotal law)
    (observedTotal_positive law falsePositive truePositive) (observedRows law) (observedColumns law)
    (observedMarginsOfNative native graphMatch law observed falsePositive truePositive)
    (observedArmMarginals law falsePositive truePositive) falsePositive truePositive

theorem native_observed_effect_endpoints_attainable (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true)
    (capacities : forall label, observedRows law label + observedColumns law label ≤ observedTotal law) :
    EffectScoreAttainableAt projection law
        (effectLower (observedTotal law) (observedTotal_positive law falsePositive truePositive)
          (observedRows law) (observedColumns law)) ∧
      EffectScoreAttainableAt projection law
        (effectUpper (observedTotal law) (observedTotal_positive law falsePositive truePositive)
          (observedRows law) (observedColumns law)) :=
  native_effect_endpoints_attainable projection graphMatch law (observedTotal law)
    (observedTotal_positive law falsePositive truePositive) (observedRows law) (observedColumns law)
    ⟨observedRows_total law, observedColumns_total law, capacities⟩
    (observedArmMarginals law falsePositive truePositive)

end BinaryInstrumental
end Causality
end Thesis
