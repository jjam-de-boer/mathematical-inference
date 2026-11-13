import Thesis.CausalTransport.SharedResponseSupport

namespace Thesis.Causality.SharedResponse

open Probability Probability.Distros

/-!
# The observationally supported response problem

Only the probability coordinates change: the new problem uses the supported
response grid and exactly the old observational moment equations. Its laws
still have full response tables, arbitrary rational denominators, repeated
labels and zero occurrences. Almost-sure support permits an excluded label
to remain in a record at weight zero; no input record needs to be rewritten.

`supportedProblem_law_iff_problem` compares admissibility of the very same
record in both problems. `supportedProblem_feasible_iff` additionally connects
feasible rational vectors to fitted original native models in the complete
bidirected projection class. Thus no fitted native model is lost, and no
feasible response law is merely an unrealized numerical relaxation.

This is a separate problem, not a replacement for `problem` or `solveBounds`.
The full response grid is still enumerated before filtering. Neither a new
solver entry point nor an optimizer execution is introduced here.
-/

variable (S : ObservedSignature.{0})

def supportedProblem (observed : FiniteProbRecord S.Assignment) : PartialMomentProblem (Table S) where
  cells := supportedEnumeration S observed
  default := defaultTable S
  nonempty := supportedEnumeration_nonempty S observed
  distinct := supportedEnumeration_nodup S observed
  intervals := (problem S observed).intervals

theorem supportedProblem_moments_iff_fits (observed : FiniteProbRecord S.Assignment)
    (law : Distro (Table S)) :
    (∀ constraint ∈ (supportedProblem S observed).intervals, constraint.LawHolds law) ↔
      Fits S observed law.record :=
  moments_iff_fits S observed law

/-- Fitting already forces the new support restriction. This equivalence
does not require every listed occurrence to have positive weight. -/
theorem supportedProblem_law_iff (observed : FiniteProbRecord S.Assignment)
    (law : Distro (Table S)) :
    (law.AlmostSurely (fun table => table ∈ (supportedProblem S observed).cells) ∧
      ∀ constraint ∈ (supportedProblem S observed).intervals, constraint.LawHolds law) ↔
      Fits S observed law.record := by
  constructor
  · intro admissible
    exact (supportedProblem_moments_iff_fits S observed law).mp admissible.2
  · intro fitted
    exact ⟨fits_supportedEnumeration S observed law fitted,
      (supportedProblem_moments_iff_fits S observed law).mpr fitted⟩

/-- The equality is semantic admissibility, not equality of grid lengths or
of the endpoint constructors' atom lists. It holds for each unchanged law. -/
theorem supportedProblem_law_iff_problem (observed : FiniteProbRecord S.Assignment)
    (law : Distro (Table S)) :
    (law.AlmostSurely (fun table => table ∈ (supportedProblem S observed).cells) ∧
      ∀ constraint ∈ (supportedProblem S observed).intervals, constraint.LawHolds law) ↔
    (law.AlmostSurely (fun table => table ∈ (problem S observed).cells) ∧
      ∀ constraint ∈ (problem S observed).intervals, constraint.LawHolds law) := by
  constructor
  · intro admissible
    exact ⟨law_supported S law, admissible.2⟩
  · intro admissible
    exact (supportedProblem_law_iff S observed law).mpr ((moments_iff_fits S observed law).mp admissible.2)

/-- A filtered endpoint law has the same actual native realization as any
other response law. Retaining every excluded zero label is not required. -/
def supportedFittedModel (observed : FiniteProbRecord S.Assignment)
    (law : (supportedProblem S observed).CompatibleLaw) : ProjectedHiddenDAGModel (graph S) :=
  asProjectedModel S law.distro.record

theorem supportedFittedModel_fits (observed : FiniteProbRecord S.Assignment)
    (law : (supportedProblem S observed).CompatibleLaw) :
    NativeFits S observed (supportedFittedModel S observed law) :=
  nativeFits_of_fits S observed law.distro.record
    ((supportedProblem_moments_iff_fits S observed law.distro).mp law.moments)

/-- Both existence directions are constructive. Native input is compressed
to its actual response law; feasible masses reconstruct a genuine law and
then a native model. No fixed denominator or hidden alphabet is assumed. -/
theorem supportedProblem_feasible_iff (observed : FiniteProbRecord S.Assignment) :
    (∃ values, (supportedProblem S observed).VectorHolds values) ↔
      ∃ original, NativeFits S observed original := by
  constructor
  · rintro ⟨values, valid⟩
    let law := (supportedProblem S observed).lawOfVector values valid
    exact ⟨supportedFittedModel S observed law, supportedFittedModel_fits S observed law⟩
  · rintro ⟨original, fitted⟩
    let law : Distro (Table S) := ⟨lawOfNative S original.model⟩
    have admissible := (supportedProblem_law_iff S observed law).mpr
      (lawOfNative_fits S observed original fitted)
    exact ⟨gridMasses law (supportedProblem S observed).cells (supportedProblem S observed).default,
      (supportedProblem S observed).vectorOfLaw law admissible.1 admissible.2⟩

/-- A checked refutation of the filtered linear constraints still excludes
every original native model, not merely laws with a chosen presentation. -/
theorem supportedProblem_refutation_not_fitted (observed : FiniteProbRecord S.Assignment)
    (certificate : RationalLinear.Infeasibility (supportedProblem S observed).cells.length
      (supportedProblem S observed).rows) :
    ∀ original, ¬ NativeFits S observed original := by
  intro original fitted
  let law : Distro (Table S) := ⟨lawOfNative S original.model⟩
  have admissible := (supportedProblem_law_iff S observed law).mpr
    (lawOfNative_fits S observed original fitted)
  exact (supportedProblem S observed).refutation_not_realizable certificate
    ⟨law, admissible.1, admissible.2⟩

end Thesis.Causality.SharedResponse
