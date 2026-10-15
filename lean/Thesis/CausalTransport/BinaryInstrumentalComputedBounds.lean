import Thesis.CausalTransport.BinaryInstrumentalNullBounds

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

variable {P : FiniteLatentProjection signature}

/-!
# Computed sharp binary-IV bounds throughout the finite rational domain

This API reads an arbitrary whole observed finite record and returns both
treatment-risk intervals, the signed-effect interval encoded by
`(ATE + 1) / 2`, and an executable compatibility flag.  It includes laws
with either instrument value absent as well as laws with positive instrument
masses and arbitrary zero treatment/outcome cells.  There is no conditional
at a null value, denominator grid cutoff, monotonicity, or fixed hidden size.

The flag is equivalent to the existence of an actual native model on the
specified original DAG.  When true, the sharpness theorem supplies universal
containment, every risk corner in one model, and both effect endpoints in
genuine native models preserving the entire law.  When false, the returned
numeric expressions are not advertised as sharp bounds for a nonempty class.

Calculating bounds uses just observed masses and the four finite capacity
checks.  Constructing endpoint witnesses is separate: the existing exact
transportation constructor now fills each selected cell by a whole maximal
batch rather than one unit of its integer total.  Theorems do not evaluate a large native noise product or
enumerate denominators, and this API does not claim efficient execution of
those expanded model witnesses at large observed totals.
-/

structure ComputedIVBounds where
  lowerRisk : Bool → QProb
  upperRisk : Bool → QProb
  lowerEffect : QProb
  upperEffect : QProb
  compatible : Bool

def observedCapacityCheck (law : FiniteProbRecord signature.Assignment) : Bool :=
  finAll 4 (fun label => decide (observedRows law label + observedColumns law label ≤ observedTotal law))

theorem observedCapacityCheck_iff (law : FiniteProbRecord signature.Assignment) :
    observedCapacityCheck law = true ↔
      forall label, observedRows law label + observedColumns law label ≤ observedTotal law := by
  constructor
  · intro checked label
    exact of_decide_eq_true ((finAll_eq_true_iff _).mp checked label)
  · intro capacities
    apply (finAll_eq_true_iff _).mpr
    intro label
    exact decide_eq_true (capacities label)

/-- Branch only on decidable natural masses.  The null branch uses the
positive whole-record denominator; the other branch uses the proved positive
product of instrument masses.  Neither branch chooses from an existential. -/
def computedBounds (law : FiniteProbRecord signature.Assignment) : ComputedIVBounds :=
  if falseZero : instrumentMass law false = 0 then
    ⟨nullRiskLower law, nullRiskUpper law, nullEffectLower law, nullEffectUpper law, true⟩
  else if trueZero : instrumentMass law true = 0 then
    ⟨nullRiskLower law, nullRiskUpper law, nullEffectLower law, nullEffectUpper law, true⟩
  else
    let positive := observedTotal_positive law (Nat.pos_of_ne_zero falseZero) (Nat.pos_of_ne_zero trueZero)
    ⟨riskLower (observedTotal law) positive (observedRows law) (observedColumns law),
      riskUpper (observedTotal law) positive (observedRows law) (observedColumns law),
      effectLower (observedTotal law) positive (observedRows law) (observedColumns law),
      effectUpper (observedTotal law) positive (observedRows law) (observedColumns law), observedCapacityCheck law⟩

def computedSelectedRisk (law : FiniteProbRecord signature.Assignment) (controlUpper treatedUpper action : Bool) : QProb :=
  if endpointUpper controlUpper treatedUpper action then (computedBounds law).upperRisk action
  else (computedBounds law).lowerRisk action

/-- The finite compatibility test is complete for the actual native class.
Null-arm observations always have an explicit witness; positive-arm data
must and can satisfy the four computed transportation capacity inequalities. -/
theorem computedBounds_compatible_iff (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment) :
    (computedBounds law).compatible = true ↔
      ∃ native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native law := by
  by_cases falseZero : instrumentMass law false = 0
  · simp only [computedBounds, falseZero, dif_pos]
    constructor
    · intro _
      exact nullInstrument_native_exists projection graphMatch law true falseZero
    · intro _
      exact True.intro
  · by_cases trueZero : instrumentMass law true = 0
    · simp only [computedBounds, falseZero, trueZero, dif_pos]
      constructor
      · intro _
        exact nullInstrument_native_exists projection graphMatch law false trueZero
      · intro _
        rfl
    · simp only [computedBounds, falseZero, trueZero]
      exact (observedCapacityCheck_iff law).trans
        (nativeModelExists_iff_observed_capacities projection graphMatch law
          (Nat.pos_of_ne_zero falseZero) (Nat.pos_of_ne_zero trueZero)).symm

theorem computedBounds_native_risks (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law) (action : Bool) :
    QProb.LE ((computedBounds law).lowerRisk action)
        (native.interventionalValue (intervention action) (fun sample => sample y)) ∧
      QProb.LE (native.interventionalValue (intervention action) (fun sample => sample y))
        ((computedBounds law).upperRisk action) := by
  by_cases falseZero : instrumentMass law false = 0
  · simpa only [computedBounds, falseZero, dif_pos] using
      nullInstrument_native_risk_bounds native graphMatch law observed true falseZero action
  · by_cases trueZero : instrumentMass law true = 0
    · simpa only [computedBounds, falseZero, trueZero, dif_neg, dif_pos] using
        nullInstrument_native_risk_bounds native graphMatch law observed false trueZero action
    · simpa only [computedBounds, falseZero, trueZero, dif_neg] using
        native_observed_risk_bounds native graphMatch law observed
          (Nat.pos_of_ne_zero falseZero) (Nat.pos_of_ne_zero trueZero) action

theorem computedBounds_native_effect (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law) :
    QProb.LE (computedBounds law).lowerEffect (nativeEffectScore native) ∧
      QProb.LE (nativeEffectScore native) (computedBounds law).upperEffect := by
  by_cases falseZero : instrumentMass law false = 0
  · simpa only [computedBounds, falseZero, dif_pos] using
      nullInstrument_native_effect_bounds native graphMatch law observed true falseZero
  · by_cases trueZero : instrumentMass law true = 0
    · simpa only [computedBounds, falseZero, trueZero, dif_neg, dif_pos] using
        nullInstrument_native_effect_bounds native graphMatch law observed false trueZero
    · simpa only [computedBounds, falseZero, trueZero, dif_neg] using
        native_observed_effect_bounds native graphMatch law observed
          (Nat.pos_of_ne_zero falseZero) (Nat.pos_of_ne_zero trueZero)

theorem computedBounds_risk_corners (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (checked : (computedBounds law).compatible = true) (controlUpper treatedUpper : Bool) :
    RisksAttainableAt projection law (computedSelectedRisk law controlUpper treatedUpper) := by
  by_cases falseZero : instrumentMass law false = 0
  · have selected : computedSelectedRisk law controlUpper treatedUpper = nullSelectedRisk law controlUpper treatedUpper := by
      funext action
      simp only [computedSelectedRisk, computedBounds, falseZero, dif_pos, nullSelectedRisk]
    rw [selected]
    exact nullInstrument_native_risk_endpoints_attainable projection graphMatch law true falseZero controlUpper treatedUpper
  · by_cases trueZero : instrumentMass law true = 0
    · have selected : computedSelectedRisk law controlUpper treatedUpper = nullSelectedRisk law controlUpper treatedUpper := by
        funext action
        simp only [computedSelectedRisk, computedBounds, falseZero, trueZero, dite_false, dif_pos, nullSelectedRisk]
      rw [selected]
      exact nullInstrument_native_risk_endpoints_attainable projection graphMatch law false trueZero controlUpper treatedUpper
    · have capacityCheck : observedCapacityCheck law = true := by
        simpa only [computedBounds, falseZero, trueZero, dif_neg] using checked
      have selected : computedSelectedRisk law controlUpper treatedUpper =
          selectedRisk (observedTotal law)
            (observedTotal_positive law (Nat.pos_of_ne_zero falseZero) (Nat.pos_of_ne_zero trueZero))
            (observedRows law) (observedColumns law) controlUpper treatedUpper := by
        funext action
        simp only [computedSelectedRisk, computedBounds, falseZero, trueZero, dite_false, selectedRisk]
      rw [selected]
      exact native_observed_risk_endpoints_attainable projection graphMatch law
          (Nat.pos_of_ne_zero falseZero) (Nat.pos_of_ne_zero trueZero)
          ((observedCapacityCheck_iff law).mp capacityCheck) controlUpper treatedUpper

theorem computedBounds_effect_endpoints (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (checked : (computedBounds law).compatible = true) :
    EffectScoreAttainableAt projection law (computedBounds law).lowerEffect ∧
      EffectScoreAttainableAt projection law (computedBounds law).upperEffect := by
  by_cases falseZero : instrumentMass law false = 0
  · simpa only [computedBounds, falseZero, dif_pos] using
      nullInstrument_native_effect_endpoints_attainable projection graphMatch law true falseZero
  · by_cases trueZero : instrumentMass law true = 0
    · simpa only [computedBounds, falseZero, trueZero, dif_neg, dif_pos] using
        nullInstrument_native_effect_endpoints_attainable projection graphMatch law false trueZero
    · have capacityCheck : observedCapacityCheck law = true := by
        simpa only [computedBounds, falseZero, trueZero, dif_neg] using checked
      simpa only [computedBounds, falseZero, trueZero, dif_neg] using
        native_observed_effect_endpoints_attainable projection graphMatch law
          (Nat.pos_of_ne_zero falseZero) (Nat.pos_of_ne_zero trueZero)
          ((observedCapacityCheck_iff law).mp capacityCheck)

/-- A proved sharpness certificate, not an assumed semantic interface.
Endpoint attainment prevents incompatible-law vacuity and retains the joint
model requirement essential to the two-risk and signed-effect assertions. -/
structure ComputedBoundsSharp (projection : FiniteLatentProjection signature)
    (law : FiniteProbRecord signature.Assignment) : Prop where
  risk_bounds : forall native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native law → forall action,
    QProb.LE ((computedBounds law).lowerRisk action)
        (native.interventionalValue (intervention action) (fun sample => sample y)) ∧
      QProb.LE (native.interventionalValue (intervention action) (fun sample => sample y))
        ((computedBounds law).upperRisk action)
  risk_corners : forall controlUpper treatedUpper,
    RisksAttainableAt projection law (computedSelectedRisk law controlUpper treatedUpper)
  effect_bounds : forall native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native law →
    QProb.LE (computedBounds law).lowerEffect (nativeEffectScore native) ∧
      QProb.LE (nativeEffectScore native) (computedBounds law).upperEffect
  effect_endpoints : EffectScoreAttainableAt projection law (computedBounds law).lowerEffect ∧
    EffectScoreAttainableAt projection law (computedBounds law).upperEffect

/-- Sharp native risk and ATE bounds for every compatible finite rational
observed law of this binary-IV graph, including either null instrument arm. -/
theorem computedBounds_sharp (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (checked : (computedBounds law).compatible = true) : ComputedBoundsSharp projection law :=
  ⟨fun native observed action => computedBounds_native_risks native graphMatch law observed action,
    computedBounds_risk_corners projection graphMatch law checked,
    fun native observed => computedBounds_native_effect native graphMatch law observed,
    computedBounds_effect_endpoints projection graphMatch law checked⟩

end BinaryInstrumental
end Causality
end Thesis
