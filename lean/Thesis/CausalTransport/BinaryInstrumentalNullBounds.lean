import Thesis.CausalTransport.BinaryInstrumentalNullResponses

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Sharp risks and signed-effect endpoints with a null instrument arm

With only one observed instrument value, consistency bounds are sharp:
the lower success risk is `Pr(X=a,Y=true)` and the upper is one minus
`Pr(X=a,Y=false)`.  These are unconditional factual masses in the whole
supplied law.  No division by the missing arm, positivity of a treatment
cell, or fictitious second-arm margin is involved.

Universal bounds use the active response cell of every actual native SCM.
Its observed coefficient has probability one, so its raw mass agrees with
the observed factual cell after cross multiplication by the native record's
own denominator.  The response cell is contained in the potential-outcome
event.  Boolean normalization gives the complementary upper bound.

Sharpness uses the explicit null-arm response construction.  Every requested
lower/upper risk corner is attained in one native model with the full law.
The opposing corners attain the average-effect endpoints on the same
responses.  Signed effects are encoded exactly by `(ATE + 1) / 2`; this
module does not replace negative effects with natural truncated subtraction.
-/

variable {P : FiniteLatentProjection signature}

def nullRiskLower (law : FiniteProbRecord signature.Assignment) (action : Bool) : QProb :=
  ⟨factualOutcomeMass law action true, law.den, law.den_pos⟩
def nullRiskUpper (law : FiniteProbRecord signature.Assignment) (action : Bool) : QProb :=
  ⟨law.den - factualOutcomeMass law action false, law.den, law.den_pos⟩

def nullSelectedRisk (law : FiniteProbRecord signature.Assignment) (controlUpper treatedUpper action : Bool) : QProb :=
  if endpointUpper controlUpper treatedUpper action then nullRiskUpper law action else nullRiskLower law action

def nullEffectLowerMass (law : FiniteProbRecord signature.Assignment) : Nat :=
  factualOutcomeMass law true true + factualOutcomeMass law false false
def nullEffectUpperMass (law : FiniteProbRecord signature.Assignment) : Nat :=
  (law.den - factualOutcomeMass law true false) + (law.den - factualOutcomeMass law false true)

def nullEffectLower (law : FiniteProbRecord signature.Assignment) : QProb :=
  ⟨nullEffectLowerMass law, 2 * law.den, Nat.mul_pos (by decide) law.den_pos⟩
def nullEffectUpper (law : FiniteProbRecord signature.Assignment) : QProb :=
  ⟨nullEffectUpperMass law, 2 * law.den, Nat.mul_pos (by decide) law.den_pos⟩

/-- The active factual cell has its exact response probability in every
native model, not just in the special equal-arm endpoint witnesses. -/
theorem nullInstrument_native_cell (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (active : Bool) (missing : instrumentMass law (!active) = 0) (action outcome : Bool) :
    QProb.Equiv (law.probVal (factualOutcomeEvent action outcome))
      ((responseRepresentation native graphMatch).responses.probVal (responseCell active action outcome)) :=
  QProb.equiv_trans (QProb.equiv_symm (nullInstrument_active_cell law active missing action outcome))
    (QProb.equiv_trans (native_responses_feasible native graphMatch law observed active action outcome)
      (QProb.equiv_trans
        (QProb.mul_congr (nullInstrument_marginal_full law active missing) (QProb.equiv_refl _))
        (by simp only [QProb.Equiv, QProb.mul, QProb.one, Nat.one_mul])))

/-- Raw consistency lower bound with the arbitrary native denominator.
The unobserved instrument arm is never identified or constrained here. -/
theorem nullInstrument_native_outcome_lower_mass (native : FiniteHiddenDAGSCM signature P)
    (graphMatch : HasIVProjection P) (law : FiniteProbRecord signature.Assignment)
    (observed : HasObservedLaw native law) (active : Bool)
    (missing : instrumentMass law (!active) = 0) (action outcome : Bool) :
    factualOutcomeMass law action outcome * (responseRepresentation native graphMatch).responses.den ≤
      FiniteProbRecord.eventMass (responseRepresentation native graphMatch).responses.atoms
        (outcomeEvent action outcome) * law.den := by
  let responses := (responseRepresentation native graphMatch).responses
  have same := nullInstrument_native_cell native graphMatch law observed active missing action outcome
  have contained := FiniteProbRecord.eventMass_mono responses.atoms (responseCell active action outcome)
    (outcomeEvent action outcome) (by
      intro profile selected
      exact (Bool.and_eq_true_iff.mp selected).2)
  calc
    _ = FiniteProbRecord.eventMass responses.atoms (responseCell active action outcome) * law.den := same
    _ ≤ _ := Nat.mul_le_mul_right law.den contained

theorem nullInstrument_native_risk_bounds (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (active : Bool) (missing : instrumentMass law (!active) = 0) (action : Bool) :
    QProb.LE (nullRiskLower law action) (native.interventionalValue (intervention action) (fun sample => sample y)) ∧
      QProb.LE (native.interventionalValue (intervention action) (fun sample => sample y)) (nullRiskUpper law action) := by
  let responses := (responseRepresentation native graphMatch).responses
  have lower : QProb.LE (nullRiskLower law action) (responses.probVal (outcomeEvent action true)) :=
    nullInstrument_native_outcome_lower_mass native graphMatch law observed active missing action true
  have upper : QProb.LE (responses.probVal (outcomeEvent action true)) (nullRiskUpper law action) :=
    outcome_upper_mass_of_complement_lower responses law.den (factualOutcomeMass law action false) action true
      (nullInstrument_native_outcome_lower_mass native graphMatch law observed active missing action false)
  have semantics := native_risk_response native graphMatch action
  exact ⟨QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_symm semantics) lower,
    QProb.le_congr (QProb.equiv_symm semantics) (QProb.equiv_refl _) upper⟩

/-- The constructed response attains its requested success-risk endpoint.
Its true and false outcomes partition the original observed denominator. -/
theorem nullResponses_risk (law : FiniteProbRecord signature.Assignment) (controlUpper treatedUpper action : Bool) :
    QProb.Equiv ((effectRecord (nullResponses law controlUpper treatedUpper) action).probVal id)
      (nullSelectedRisk law controlUpper treatedUpper action) := by
  let responses := nullResponses law controlUpper treatedUpper
  have selected := nullResponses_selected_outcome_mass law controlUpper treatedUpper action
  have semantics : QProb.Equiv ((effectRecord responses action).probVal id) (responses.probVal (outcomeEvent action true)) :=
    QProb.equiv_trans (effectRecord_probVal responses action)
      (responses.probVal_congr _ _ (fun profile => (outcomeEvent_true profile action).symm))
  apply QProb.equiv_trans semantics
  cases chosen : endpointUpper controlUpper treatedUpper action with
  | false =>
      have exactMass : FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) = factualOutcomeMass law action true := by
        simpa only [chosen, Bool.not_false] using selected
      simp only [nullSelectedRisk, chosen, Bool.false_eq_true, if_false]
      change FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) * law.den =
        factualOutcomeMass law action true * law.den
      rw [exactMass]
  | true =>
      have failure : FiniteProbRecord.eventMass responses.atoms (outcomeEvent action false) = factualOutcomeMass law action false := by
        simpa only [chosen, Bool.not_true] using selected
      have partition := outcomeEvent_partition responses action
      rw [failure] at partition
      change _ + _ = law.den at partition
      have exactMass : FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) = law.den - factualOutcomeMass law action false := by omega
      simp only [nullSelectedRisk, chosen, if_true]
      change FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) * law.den =
        (law.den - factualOutcomeMass law action false) * law.den
      rw [exactMass]

theorem nullInstrument_native_risk_endpoints_attainable (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (active : Bool) (missing : instrumentMass law (!active) = 0) (controlUpper treatedUpper : Bool) :
    RisksAttainableAt projection law (nullSelectedRisk law controlUpper treatedUpper) := by
  apply (risksAttainableAt_iff projection graphMatch law _).mpr
  exact ⟨nullResponses law controlUpper treatedUpper,
    nullResponses_feasible law active missing controlUpper treatedUpper,
    nullResponses_risk law controlUpper treatedUpper⟩

/-- Universal signed-effect score bounds for the null-arm branch, using
one actual native response record and its own denominator throughout. -/
theorem nullInstrument_native_effect_bounds (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (active : Bool) (missing : instrumentMass law (!active) = 0) :
    QProb.LE (nullEffectLower law) (nativeEffectScore native) ∧
      QProb.LE (nativeEffectScore native) (nullEffectUpper law) := by
  let responses := (responseRepresentation native graphMatch).responses
  let treated := FiniteProbRecord.eventMass responses.atoms (outcomeEvent true true)
  let controlFailure := FiniteProbRecord.eventMass responses.atoms (outcomeEvent false false)
  have lowerTreated : factualOutcomeMass law true true * responses.den ≤ treated * law.den :=
    nullInstrument_native_outcome_lower_mass native graphMatch law observed active missing true true
  have lowerControl : factualOutcomeMass law false false * responses.den ≤ controlFailure * law.den :=
    nullInstrument_native_outcome_lower_mass native graphMatch law observed active missing false false
  have upperTreated : treated * law.den ≤ (law.den - factualOutcomeMass law true false) * responses.den :=
    outcome_upper_mass_of_complement_lower responses law.den (factualOutcomeMass law true false) true true
      (nullInstrument_native_outcome_lower_mass native graphMatch law observed active missing true false)
  have upperControl : controlFailure * law.den ≤ (law.den - factualOutcomeMass law false true) * responses.den :=
    outcome_upper_mass_of_complement_lower responses law.den (factualOutcomeMass law false true) false false
      (nullInstrument_native_outcome_lower_mass native graphMatch law observed active missing false true)
  have lower : QProb.LE (nullEffectLower law) (responseEffectScore responses) := by
    change nullEffectLowerMass law * (2 * responses.den) ≤ (responseEffectScore responses).num * (2 * law.den)
    rw [responseEffectScore_numerator]
    change _ ≤ (treated + controlFailure) * (2 * law.den)
    calc
      _ = 2 * (factualOutcomeMass law true true * responses.den + factualOutcomeMass law false false * responses.den) := by
        simp only [nullEffectLowerMass, Nat.add_mul, Nat.mul_add]
        ac_rfl
      _ ≤ 2 * (treated * law.den + controlFailure * law.den) := Nat.mul_le_mul_left 2 (Nat.add_le_add lowerTreated lowerControl)
      _ = _ := by simp only [Nat.add_mul, Nat.mul_add]; ac_rfl
  have upper : QProb.LE (responseEffectScore responses) (nullEffectUpper law) := by
    change (responseEffectScore responses).num * (2 * law.den) ≤ nullEffectUpperMass law * (2 * responses.den)
    rw [responseEffectScore_numerator]
    change (treated + controlFailure) * (2 * law.den) ≤ _
    calc
      _ = 2 * (treated * law.den + controlFailure * law.den) := by simp only [Nat.add_mul, Nat.mul_add]; ac_rfl
      _ ≤ 2 * ((law.den - factualOutcomeMass law true false) * responses.den +
          (law.den - factualOutcomeMass law false true) * responses.den) := Nat.mul_le_mul_left 2 (Nat.add_le_add upperTreated upperControl)
      _ = _ := by simp only [nullEffectUpperMass, Nat.add_mul, Nat.mul_add]; ac_rfl
  have semantics := nativeEffectScore_response native graphMatch
  exact ⟨QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_symm semantics) lower,
    QProb.le_congr (QProb.equiv_symm semantics) (QProb.equiv_refl _) upper⟩

private theorem nullResponses_lower_score (law : FiniteProbRecord signature.Assignment) :
    QProb.Equiv (responseEffectScore (nullResponses law true false)) (nullEffectLower law) := by
  let responses := nullResponses law true false
  have treated : FiniteProbRecord.eventMass responses.atoms (outcomeEvent true true) = factualOutcomeMass law true true :=
    nullResponses_selected_outcome_mass law true false true
  have controlFailure : FiniteProbRecord.eventMass responses.atoms (outcomeEvent false false) = factualOutcomeMass law false false :=
    nullResponses_selected_outcome_mass law true false false
  change (responseEffectScore responses).num * (2 * law.den) = nullEffectLowerMass law * (2 * law.den)
  rw [responseEffectScore_numerator, treated, controlFailure]
  rfl

private theorem nullResponses_upper_score (law : FiniteProbRecord signature.Assignment) :
    QProb.Equiv (responseEffectScore (nullResponses law false true)) (nullEffectUpper law) := by
  let responses := nullResponses law false true
  have treatedFailure : FiniteProbRecord.eventMass responses.atoms (outcomeEvent true false) = factualOutcomeMass law true false :=
    nullResponses_selected_outcome_mass law false true true
  have controlSuccess : FiniteProbRecord.eventMass responses.atoms (outcomeEvent false true) = factualOutcomeMass law false true :=
    nullResponses_selected_outcome_mass law false true false
  have treatedPartition := outcomeEvent_partition responses true
  have controlPartition := outcomeEvent_partition responses false
  rw [treatedFailure] at treatedPartition
  rw [controlSuccess] at controlPartition
  change _ + _ = law.den at treatedPartition
  change _ + _ = law.den at controlPartition
  have treated : FiniteProbRecord.eventMass responses.atoms (outcomeEvent true true) = law.den - factualOutcomeMass law true false := by omega
  have controlFailure : FiniteProbRecord.eventMass responses.atoms (outcomeEvent false false) = law.den - factualOutcomeMass law false true := by omega
  change (responseEffectScore responses).num * (2 * law.den) = nullEffectUpperMass law * (2 * law.den)
  rw [responseEffectScore_numerator, treated, controlFailure]
  rfl

/-- One native witness attains each signed-effect endpoint, including its
two opposing risks.  All observed cells, including zero cells, are preserved. -/
theorem nullInstrument_native_effect_endpoints_attainable (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (active : Bool) (missing : instrumentMass law (!active) = 0) :
    EffectScoreAttainableAt projection law (nullEffectLower law) ∧
      EffectScoreAttainableAt projection law (nullEffectUpper law) := by
  constructor
  · apply (effectScoreAttainableAt_iff projection graphMatch law _).mpr
    exact ⟨nullResponses law true false, nullResponses_feasible law active missing true false,
      nullResponses_lower_score law⟩
  · apply (effectScoreAttainableAt_iff projection graphMatch law _).mpr
    exact ⟨nullResponses law false true, nullResponses_feasible law active missing false true,
      nullResponses_upper_score law⟩

end BinaryInstrumental
end Causality
end Thesis
