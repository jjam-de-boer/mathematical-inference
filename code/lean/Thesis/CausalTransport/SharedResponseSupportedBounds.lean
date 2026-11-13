import Thesis.CausalTransport.SharedResponseSupportedProblem
import Thesis.CausalTransport.SharedResponseLinearBounds

namespace Thesis.Causality.SharedResponse

open Probability Probability.Distros

/-!
# Sharp bounds are invariant under observational-support pruning

The first theorem compares arbitrary sharp-bound certificates for an integer
response on the full and filtered problems. Each certificate bounds the other
one's attaining laws, because those very laws are admissible in both problems.
The resulting two inequalities identify each endpoint as a rational value;
record syntax, chosen endpoint models and unreduced presentations may differ.

The native bridge then realizes filtered event-bound endpoints as actual
original hidden-DAG models and bounds every fitted original model in the
unchanged complete-bidirected projection class. All hard interventions are
allowed, including observationally null actions. The existing native
point-identification criterion applies directly to these certificates.

No optimizer is run or given a new public entry point. In particular, the
existing `solveBounds` definition and linear elimination engine are unchanged.
This proves preservation of certificates, not a measured running-time gain.
-/

variable (S : ObservedSignature.{0})

/-- Attainment in both problems is essential: comparing only non-sharp
valid intervals would not force their endpoints to agree. -/
theorem supportedProblem_sharpBounds_equiv (observed : FiniteProbRecord S.Assignment)
    (response : Table S → Int) (full : (problem S observed).SharpBounds response)
    (filtered : (supportedProblem S observed).SharpBounds response) :
    SignedRatio.Equiv full.lower filtered.lower ∧ SignedRatio.Equiv full.upper filtered.upper := by
  have filteredLower := (supportedProblem_law_iff_problem S observed filtered.lowerLaw.distro).mp
    ⟨filtered.lowerLaw.support, filtered.lowerLaw.moments⟩
  have filteredUpper := (supportedProblem_law_iff_problem S observed filtered.upperLaw.distro).mp
    ⟨filtered.upperLaw.support, filtered.upperLaw.moments⟩
  have fullLower := (supportedProblem_law_iff_problem S observed full.lowerLaw.distro).mpr
    ⟨full.lowerLaw.support, full.lowerLaw.moments⟩
  have fullUpper := (supportedProblem_law_iff_problem S observed full.upperLaw.distro).mpr
    ⟨full.upperLaw.support, full.upperLaw.moments⟩
  have lowerForward := (full.bounds filtered.lowerLaw.distro filteredLower.1 filteredLower.2).1
  have lowerBackward := (filtered.bounds full.lowerLaw.distro fullLower.1 fullLower.2).1
  have upperForward := (filtered.bounds full.upperLaw.distro fullUpper.1 fullUpper.2).2
  have upperBackward := (full.bounds filtered.upperLaw.distro filteredUpper.1 filteredUpper.2).2
  exact ⟨SignedRatio.equiv_of_le_of_le
      ((SignedRatio.le_congr (SignedRatio.equiv_refl _) filtered.lower_attained).mp lowerForward)
      ((SignedRatio.le_congr (SignedRatio.equiv_refl _) full.lower_attained).mp lowerBackward),
    SignedRatio.equiv_of_le_of_le
      ((SignedRatio.le_congr full.upper_attained (SignedRatio.equiv_refl _)).mp upperForward)
      ((SignedRatio.le_congr filtered.upper_attained (SignedRatio.equiv_refl _)).mp upperBackward)⟩

/-- Transfer both attained endpoints and the universal inequalities. The
universal step uses the coverage theorem, so it does not restrict the input
native model's source sizes or require strict observational positivity. -/
def boundsOfSupportedMoment (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment)
    (sharp : (supportedProblem S observed).SharpBounds
      (eventResponse (fun table => event (eval S intervention.value table)))) :
    SharpBounds S observed intervention event where
  lower := sharp.lower
  upper := sharp.upper
  lowerModel := supportedFittedModel S observed sharp.lowerLaw
  upperModel := supportedFittedModel S observed sharp.upperLaw
  lower_fits := supportedFittedModel_fits S observed sharp.lowerLaw
  upper_fits := supportedFittedModel_fits S observed sharp.upperLaw
  lower_attained := SignedRatio.equiv_trans
    (QProb.toSignedRatio_congr (nativeModel_interventionalValue S _ intervention event))
    sharp.event_lower_attained
  upper_attained := SignedRatio.equiv_trans
    (QProb.toSignedRatio_congr (nativeModel_interventionalValue S _ intervention event))
    sharp.event_upper_attained
  bounds := by
    intro original fitted
    let law : Distro (Table S) := ⟨lawOfNative S original.model⟩
    have admissible := (supportedProblem_law_iff S observed law).mpr
      (lawOfNative_fits S observed original fitted)
    have bounded := sharp.event_bounds law admissible.1 admissible.2
    have preserved := QProb.toSignedRatio_congr
      (lawOfNative_interventionalValue S original.model intervention event)
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) preserved).mp bounded.1,
      (SignedRatio.le_congr preserved (SignedRatio.equiv_refl _)).mp bounded.2⟩

/-- Coincident filtered endpoints characterize identification throughout
the original native class, rather than just agreement of two witnesses. -/
theorem pointIdentified_iff_supportedBounds (observed : FiniteProbRecord S.Assignment)
    (intervention : HardIntervention S) (event : Event S.Assignment)
    (sharp : (supportedProblem S observed).SharpBounds
      (eventResponse (fun table => event (eval S intervention.value table)))) :
    PointIdentified S observed intervention event ↔ SignedRatio.Equiv sharp.lower sharp.upper :=
  (boundsOfSupportedMoment S observed intervention event sharp).pointIdentified_iff

end Thesis.Causality.SharedResponse
