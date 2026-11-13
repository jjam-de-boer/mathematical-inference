import Thesis.CausalTransport.SharedResponseSupportedBounds

namespace Thesis.Causality.SharedResponse

open Probability Probability.Distros

/-!
# A separate solver entry point for the supported response grid

`boundResultOfSupportedMoment` transports an already checked linear answer:
attained endpoints become native sharp bounds, while an elimination refutation
excludes every fitted original native model. Keeping this transport separate
also lets callers check certificate routing without executing the optimizer.

`solveSupportedBounds` supplies the supported moment problem's actual answer
to that transport. It returns the existing `BoundResult`, so clients retain
the same native witnesses and identification-decision interface. Agreement
with the old entry point means the same feasibility outcome and equivalent
rational endpoints, not identical endpoint models or record presentations.

The class remains the complete bidirected projection class. No hidden-source
or denominator cap is added, and observationally null intervention values
remain allowed. The original `solveBounds` and elimination engine are not
modified. Filtering still first enumerates the full response grid; neither
this definition nor its correctness proof establishes practical running time.
-/

variable (S : ObservedSignature.{0})

def boundResultOfSupportedMoment (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment)
    (answer : (supportedProblem S observed).BoundResult
      (eventResponse (fun table => event (eval S intervention.value table)))) :
    BoundResult S observed intervention event :=
  match answer with
  | .bounded sharp => .bounded (boundsOfSupportedMoment S observed intervention event sharp)
  | .infeasible certificate =>
      .incompatible (supportedProblem_refutation_not_fitted S observed certificate)

/-- An opt-in entry point using the filtered coordinates. All numerical
work is still performed by the existing constructive rational linear solver. -/
def solveSupportedBounds (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    BoundResult S observed intervention event :=
  boundResultOfSupportedMoment S observed intervention event
    ((supportedProblem S observed).solveEventBounds (fun table => event (eval S intervention.value table)))

/-- Success is equivalent to actual native compatibility. A failed answer
cannot merely mean that a supported model was absent from the filtered grid. -/
theorem solveSupportedBounds_success_iff (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    (match solveSupportedBounds S observed intervention event with
    | .bounded _ => True
    | .incompatible _ => False) ↔ ∃ original, NativeFits S observed original := by
  cases answer : solveSupportedBounds S observed intervention event with
  | bounded sharp =>
      constructor
      · intro _
        exact ⟨sharp.lowerModel, sharp.lower_fits⟩
      · intro _
        trivial
  | incompatible excluded =>
      constructor
      · intro impossible
        exact False.elim impossible
      · rintro ⟨original, fitted⟩
        exact excluded original fitted

private theorem native_sharpBounds_equiv {observed : FiniteProbRecord S.Assignment}
    {intervention : HardIntervention S} {event : Event S.Assignment}
    (first second : SharpBounds S observed intervention event) :
    SignedRatio.Equiv first.lower second.lower ∧ SignedRatio.Equiv first.upper second.upper := by
  -- Each endpoint is attained inside the common original model class.
  -- Applying the other certificate to that witness gives the reverse bound.
  have lowerForward := (first.bounds second.lowerModel second.lower_fits).1
  have lowerBackward := (second.bounds first.lowerModel first.lower_fits).1
  have upperForward := (second.bounds first.upperModel first.upper_fits).2
  have upperBackward := (first.bounds second.upperModel second.upper_fits).2
  exact ⟨SignedRatio.equiv_of_le_of_le
      ((SignedRatio.le_congr (SignedRatio.equiv_refl _) second.lower_attained).mp lowerForward)
      ((SignedRatio.le_congr (SignedRatio.equiv_refl _) first.lower_attained).mp lowerBackward),
    SignedRatio.equiv_of_le_of_le
      ((SignedRatio.le_congr first.upper_attained (SignedRatio.equiv_refl _)).mp upperForward)
      ((SignedRatio.le_congr second.upper_attained (SignedRatio.equiv_refl _)).mp upperBackward)⟩

/-- Compare the actual two entry points without evaluating either on a
ground query. Incompatibility on one side contradicts the other's fitted
witness; when both succeed, attainment forces both endpoints to agree. -/
theorem solveSupportedBounds_agrees (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    match solveBounds S observed intervention event, solveSupportedBounds S observed intervention event with
    | .bounded full, .bounded filtered =>
        SignedRatio.Equiv full.lower filtered.lower ∧ SignedRatio.Equiv full.upper filtered.upper
    | .incompatible _, .incompatible _ => True
    | _, _ => False := by
  cases fullAnswer : solveBounds S observed intervention event with
  | bounded full =>
      cases filteredAnswer : solveSupportedBounds S observed intervention event with
      | bounded filtered => exact native_sharpBounds_equiv S full filtered
      | incompatible excluded => exact excluded full.lowerModel full.lower_fits
  | incompatible excluded =>
      cases filteredAnswer : solveSupportedBounds S observed intervention event with
      | bounded filtered => exact excluded filtered.lowerModel filtered.lower_fits
      | incompatible _ => trivial

end Thesis.Causality.SharedResponse
