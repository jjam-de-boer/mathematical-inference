import Thesis.CausalTransport.SharedResponseSupportedSolver
import Thesis.Examples.SharedResponseSupportedBounds

namespace Thesis.Causality.Examples.SharedResponseSupportedSolver

open Probability Causality.SharedResponse

/-!
# Solver-adapter clients, without an optimizer execution

The bow certificate below was proved analytically in the preceding regression.
Routing that supplied certificate checks native endpoint preservation and the
existing identification decision at a null factual action. No call to either
linear solver is normalized on this concrete example.

The final interface check keeps the observation, action and event arbitrary.
It confirms that callers of the new entry point can reuse the old decision
interface; its proof does not execute a closed causal query. A resource-capped
causal optimizer pilot remains a separate checkpoint.
-/

namespace Bow

open BinaryBow
open SharedResponseLinearBounds.Bow (observed)
open SharedResponseSupportedBounds.Bow (certificate)

def routed : BoundResult signature observed (intervention true) (fun values => values y) :=
  boundResultOfSupportedMoment signature observed (intervention true) (fun values => values y)
    (.bounded certificate)

theorem supplied_endpoints_preserved :
    match routed with
    | .bounded sharp =>
        SignedRatio.Equiv sharp.lower SignedRatio.zero ∧ SignedRatio.Equiv sharp.upper SignedRatio.one
    | .incompatible _ => False :=
  ⟨SignedRatio.equiv_refl _, SignedRatio.equiv_refl _⟩

def routedDecision : Decidable (PointIdentified signature observed (intervention true) (fun values => values y)) :=
  BoundResult.identificationDecision signature routed

/-- Only the rational endpoint comparison runs here. It returns a proof of
non-identification throughout the original native class, rather than merely
observing that the two displayed endpoint numbers differ. -/
theorem supplied_certificate_decision :
    (match routedDecision with | .isTrue _ => False | .isFalse _ => True) :=
  True.intro

end Bow

example (S : ObservedSignature.{0}) (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    Decidable (PointIdentified S observed intervention event) :=
  BoundResult.identificationDecision S (solveSupportedBounds S observed intervention event)

end Thesis.Causality.Examples.SharedResponseSupportedSolver
