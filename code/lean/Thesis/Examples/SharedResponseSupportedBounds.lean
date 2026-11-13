import Thesis.CausalTransport.SharedResponseSupportedBounds
import Thesis.Examples.SharedResponseSupport

namespace Thesis.Causality.Examples.SharedResponseSupportedBounds

open Probability Causality.SharedResponse Probability.Distros

/-!
# Fitted records and attained bounds through the filtered problem

The three-valued record remains admissible literally, including its repeated
label, unreduced denominator and zero occurrence outside the filtered grid.
The bow example supplies two explicit endpoint laws and a simple analytic
bound certificate. Transferring that certificate through the new bridge
still proves ambiguity after an observationally null action is forced.

These checks do not execute the linear optimizer. Only small table, filter
and rational-record calculations use kernel reduction. The bounds are proved
from the probability interval [0,1] and the displayed attaining laws; no
solver result, speedup or new causal execution pilot is claimed.
-/

namespace Unary

open SharedResponseLinearBounds.Unary

theorem unchanged_record_admissible :
    (⟨law⟩ : Distro (Table signature)).AlmostSurely
        (fun table => table ∈ (supportedProblem signature observed).cells) ∧
      ∀ constraint ∈ (supportedProblem signature observed).intervals,
        constraint.LawHolds (⟨law⟩ : Distro (Table signature)) :=
  (supportedProblem_law_iff signature observed ⟨law⟩).mpr law_fits

theorem feasible_with_null_value :
    ∃ values, (supportedProblem signature observed).VectorHolds values :=
  (supportedProblem_feasible_iff signature observed).mpr ⟨original, original_fits⟩

end Unary

namespace Bow

open BinaryBow
open SharedResponseLinearBounds.Bow (observed)
open SharedResponseSupport.Bow (responseTable)

def endpointLaw (offFactual : Bool) : FiniteProbRecord (Table signature) :=
  ⟨[(responseTable false, if offFactual then 0 else 1),
      (responseTable true, if offFactual then 1 else 0)],
    1, Nat.zero_lt_one, by cases offFactual <;> rfl⟩

private theorem factual_response (offFactual : Bool) :
    eval signature (FiniteLatentSCM.noIntervention signature) (responseTable offFactual) =
      (fun _ => false) := by
  cases offFactual <;> decide +kernel

theorem endpointLaw_fits (offFactual : Bool) : Fits signature observed (endpointLaw offFactual) := by
  intro event
  cases offFactual <;>
    simp only [endpointLaw, observed, FiniteProbRecord.probVal, FiniteProbRecord.eventMass,
      factual_response, QProb.Equiv, Nat.mul_one, Nat.add_zero, Nat.zero_add] <;>
    cases event (fun _ => false) <;> rfl

private theorem supported_grid : supportedEnumeration signature observed =
    [responseTable false, responseTable true] := by decide +kernel

/-- Each endpoint retains both filtered labels, with one at weight zero.
This is a full compatible-law certificate, not just a feasibility premise. -/
def endpointCompatible (offFactual : Bool) : (supportedProblem signature observed).CompatibleLaw where
  distro := ⟨endpointLaw offFactual⟩
  support := fits_supportedEnumeration signature observed ⟨endpointLaw offFactual⟩ (endpointLaw_fits offFactual)
  moments := (supportedProblem_moments_iff_fits signature observed ⟨endpointLaw offFactual⟩).mpr
    (endpointLaw_fits offFactual)
  retains := by
    intro table listed
    change table ∈ supportedEnumeration signature observed at listed
    rw [supported_grid] at listed
    rcases List.mem_cons.mp listed with same | later
    · subst table
      exact ⟨_, List.mem_cons_self ..⟩
    · have same := List.mem_singleton.mp later
      subst table
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩

def effectEvent : Event (Table signature) :=
  fun table => eval signature (intervention true).value table y

theorem endpoint_effect (offFactual : Bool) :
    QProb.Equiv ((endpointLaw offFactual).probVal effectEvent)
      (if offFactual then QProb.one else QProb.zero) := by
  cases offFactual <;> decide +kernel

/-- Probability bounds alone supply the universal inequalities. The two
explicit laws prove attainment without asking the elimination engine to run. -/
def certificate : (supportedProblem signature observed).SharpBounds (eventResponse effectEvent) where
  lower := SignedRatio.zero
  upper := SignedRatio.one
  lowerLaw := endpointCompatible false
  upperLaw := endpointCompatible true
  lower_attained := SignedRatio.equiv_trans (eventResponse_expectation _ effectEvent)
    (QProb.toSignedRatio_congr (endpoint_effect false))
  upper_attained := SignedRatio.equiv_trans (eventResponse_expectation _ effectEvent)
    (QProb.toSignedRatio_congr (endpoint_effect true))
  bounds := by
    intro law _support _moments
    have lower := (SignedRatio.toSignedRatio_le_iff QProb.zero (law.record.probVal effectEvent)).mpr
      (law.record.probVal_nonneg effectEvent)
    have upper := (SignedRatio.toSignedRatio_le_iff (law.record.probVal effectEvent) QProb.one).mpr
      (law.record.probVal_le_one effectEvent)
    have integral := eventResponse_expectation law effectEvent
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm integral)).mp lower,
      (SignedRatio.le_congr (SignedRatio.equiv_symm integral) (SignedRatio.equiv_refl _)).mp upper⟩

def nativeCertificate : SharpBounds signature observed (intervention true) (fun values => values y) :=
  boundsOfSupportedMoment signature observed (intervention true) (fun values => values y) certificate

/-- The new certificate still ranges over every original model in the
stated class. Null factual action support does not imply identification. -/
theorem effect_not_point_identified :
    ¬ PointIdentified signature observed (intervention true) (fun values => values y) := by
  intro identified
  have coincident := (pointIdentified_iff_supportedBounds signature observed (intervention true)
    (fun values => values y) certificate).mp identified
  exact (by decide +kernel : ¬ SignedRatio.Equiv SignedRatio.zero SignedRatio.one) coincident

end Bow
end Thesis.Causality.Examples.SharedResponseSupportedBounds
