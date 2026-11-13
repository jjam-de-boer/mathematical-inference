import Thesis.CausalTransport.SharedResponseProblem

namespace Thesis.Causality.SharedResponse

open Probability Probability.Distros

/-!
# Unrestricted-denominator sharp bounds in the shared-root class

The existing constructive rational linear solver supplies feasible masses or
an elimination refutation, and attains both extrema of an integer response.
The response/native coverage bridge below turns those results into bounds on
every original finite hidden DAG with the complete bidirected projection.
No hidden alphabet or rational denominator cap is a premise of this class.

Each endpoint includes an actual fitted native model. Point identification is
therefore equivalent to coincident endpoints, not to a vacuous universal
statement at incompatible data. Distinct endpoints give genuine disagreeing
models, rather than just a numerical gap in a relaxation.

This first solver adapter concerns unconditional hard-intervention events.
The representation already preserves conditional support, but separate support
and supported-value classification is not implemented here. These explicit
procedures can be very large; they are not installed as global decision
instances and no practical running-time guarantee is made.
-/

variable (S : ObservedSignature.{0})

def PointIdentified (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment) : Prop :=
  (∃ original, NativeFits S observed original) ∧
  ∀ left right, NativeFits S observed left → NativeFits S observed right →
    QProb.Equiv (left.model.interventionalValue intervention event)
      (right.model.interventionalValue intervention event)

structure SharpBounds (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment) where
  lower : SignedRatio
  upper : SignedRatio
  lowerModel : ProjectedHiddenDAGModel (graph S)
  upperModel : ProjectedHiddenDAGModel (graph S)
  lower_fits : NativeFits S observed lowerModel
  upper_fits : NativeFits S observed upperModel
  lower_attained : SignedRatio.Equiv (lowerModel.model.interventionalValue intervention event).toSignedRatio lower
  upper_attained : SignedRatio.Equiv (upperModel.model.interventionalValue intervention event).toSignedRatio upper
  bounds : ∀ original, NativeFits S observed original →
    SignedRatio.LE lower (original.model.interventionalValue intervention event).toSignedRatio ∧
      SignedRatio.LE (original.model.interventionalValue intervention event).toSignedRatio upper

/-- Transfer attained rational linear extrema to the unchanged original
native class, in both the witness and universal-bound directions. -/
def boundsOfMoment (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment)
    (sharp : (problem S observed).SharpBounds
      (eventResponse (fun table => event (eval S intervention.value table)))) :
    SharpBounds S observed intervention event where
  lower := sharp.lower
  upper := sharp.upper
  lowerModel := fittedModel S observed sharp.lowerLaw
  upperModel := fittedModel S observed sharp.upperLaw
  lower_fits := fittedModel_fits S observed sharp.lowerLaw
  upper_fits := fittedModel_fits S observed sharp.upperLaw
  lower_attained := SignedRatio.equiv_trans
    (QProb.toSignedRatio_congr (nativeModel_interventionalValue S _ intervention event))
    sharp.event_lower_attained
  upper_attained := SignedRatio.equiv_trans
    (QProb.toSignedRatio_congr (nativeModel_interventionalValue S _ intervention event))
    sharp.event_upper_attained
  bounds := by
    intro original fitted
    let law : Distro (Table S) := ⟨lawOfNative S original.model⟩
    have moments := (moments_iff_fits S observed law).mpr (lawOfNative_fits S observed original fitted)
    have bounded := sharp.event_bounds law (law_supported S law) moments
    have preserved := QProb.toSignedRatio_congr
      (lawOfNative_interventionalValue S original.model intervention event)
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) preserved).mp bounded.1,
      (SignedRatio.le_congr preserved (SignedRatio.equiv_refl _)).mp bounded.2⟩

inductive BoundResult (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment) where
  | bounded (sharp : SharpBounds S observed intervention event)
  | incompatible (excluded : ∀ original, ¬ NativeFits S observed original)

/-- Exact rational optimization with no denominator bound. Only the finite
response grid is enumerated; its unknown rational masses are solved linearly. -/
def solveBounds (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment) :
    BoundResult S observed intervention event :=
  match (problem S observed).solveEventBounds (fun table => event (eval S intervention.value table)) with
  | .bounded sharp => .bounded (boundsOfMoment S observed intervention event sharp)
  | .infeasible certificate => .incompatible (by
      intro original fitted
      let law : Distro (Table S) := ⟨lawOfNative S original.model⟩
      exact (problem S observed).refutation_not_realizable certificate
        ⟨law, law_supported S law,
          (moments_iff_fits S observed law).mpr (lawOfNative_fits S observed original fitted)⟩)

namespace SharpBounds

variable {S} {observed : FiniteProbRecord S.Assignment}
variable {intervention : HardIntervention S} {event : Event S.Assignment}

/-- This criterion quantifies over all original graphs in the stated class,
not merely the two endpoint models or the printed finite table catalogue. -/
theorem pointIdentified_iff (sharp : SharpBounds S observed intervention event) :
    PointIdentified S observed intervention event ↔ SignedRatio.Equiv sharp.lower sharp.upper := by
  constructor
  · intro identified
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm sharp.lower_attained)
      (SignedRatio.equiv_trans (QProb.toSignedRatio_congr
        (identified.2 sharp.lowerModel sharp.upperModel sharp.lower_fits sharp.upper_fits)) sharp.upper_attained)
  · intro coincident
    refine ⟨⟨sharp.lowerModel, sharp.lower_fits⟩, ?_⟩
    intro left right leftFits rightFits
    have atLower (original : ProjectedHiddenDAGModel (graph S)) (fitted : NativeFits S observed original) :
        SignedRatio.Equiv (original.model.interventionalValue intervention event).toSignedRatio sharp.lower := by
      have bounded := sharp.bounds original fitted
      exact SignedRatio.equiv_of_le_of_le
        ((SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm coincident)).mp bounded.2) bounded.1
    exact (QProb.toSignedRatio_equiv_iff _ _).mp
      (SignedRatio.equiv_trans (atLower left leftFits) (SignedRatio.equiv_symm (atLower right rightFits)))

theorem endpoints_differ (sharp : SharpBounds S observed intervention event)
    (different : ¬ SignedRatio.Equiv sharp.lower sharp.upper) :
    ¬ QProb.Equiv (sharp.lowerModel.model.interventionalValue intervention event)
      (sharp.upperModel.model.interventionalValue intervention event) := by
  intro same
  exact different (SignedRatio.equiv_trans (SignedRatio.equiv_symm sharp.lower_attained)
    (SignedRatio.equiv_trans (QProb.toSignedRatio_congr same) sharp.upper_attained))

end SharpBounds

/-- Explicit exact identification decision for a supplied solver result.
The only final test compares integer cross-products of rational endpoints. -/
def BoundResult.identificationDecision {observed : FiniteProbRecord S.Assignment}
    {intervention : HardIntervention S} {event : Event S.Assignment}
    (answer : BoundResult S observed intervention event) :
    Decidable (PointIdentified S observed intervention event) :=
  match answer with
  | .incompatible excluded => .isFalse (fun identified => by
      rcases identified.1 with ⟨original, fitted⟩
      exact excluded original fitted)
  | .bounded sharp =>
      if same : SignedRatio.Equiv sharp.lower sharp.upper then
        .isTrue (sharp.pointIdentified_iff.mpr same)
      else .isFalse (fun identified => same (sharp.pointIdentified_iff.mp identified))

end Thesis.Causality.SharedResponse
