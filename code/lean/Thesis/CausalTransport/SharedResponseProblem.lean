import Thesis.CausalTransport.SharedResponseNative
import Thesis.Probability.Distros.PartialMomentBounds

namespace Thesis.Causality.SharedResponse

open Probability Probability.Distros

/-!
# Exact observational constraints on the finite response grid

The only unknowns are the rational masses of the enumerated response atoms.
Every observed singleton supplies an exact integer-response moment equation;
the simplex constraints are constructed by `PartialMomentProblem`. The lemma
`moments_iff_fits` proves that these equations mean equality of the whole
observational law, not merely a collection of unchecked numerical inputs.

The two coverage directions are actual original native models and actual
finite rational records. Neither direction presupposes compatibility or a
denominator bound. This is the fully shared-root projection of
`SharedResponseNative`, not an optimizer over arbitrary independent roots.
-/

variable (S : ObservedSignature.{0})

def Fits (observed : FiniteProbRecord S.Assignment) (law : FiniteProbRecord (Table S)) : Prop :=
  ∀ event, QProb.Equiv (law.probVal (fun table => event (eval S (FiniteLatentSCM.noIntervention S) table)))
    (observed.probVal event)

def NativeFits (observed : FiniteProbRecord S.Assignment)
    (original : ProjectedHiddenDAGModel (graph S)) : Prop :=
  ∀ event, QProb.Equiv (original.model.observationalValue event) (observed.probVal event)

def observedEvent (reference : S.Assignment) : Event (Table S) :=
  fun table => FiniteProbRecord.singletonEvent reference (eval S (FiniteLatentSCM.noIntervention S) table)

def observationMoment (observed : FiniteProbRecord S.Assignment) (reference : S.Assignment) : MomentInterval (Table S) :=
  MomentInterval.exact (eventResponse (observedEvent S reference))
    (observed.probVal (FiniteProbRecord.singletonEvent reference)).toSignedRatio

def problem (observed : FiniteProbRecord S.Assignment) : PartialMomentProblem (Table S) where
  cells := enumeration S
  default := defaultTable S
  nonempty := enumeration_nonempty S
  distinct := enumeration_nodup S
  intervals := S.assignmentEnumeration.map (observationMoment S observed)

private theorem eventMoment_iff (law : Distro A) (event : Event A) (value : QProb) :
    (MomentInterval.exact (eventResponse event) value.toSignedRatio).LawHolds law ↔
      QProb.Equiv (law.record.probVal event) value := by
  have indicator := eventResponse_expectation law event
  constructor
  · intro bounded
    have same := SignedRatio.equiv_of_le_of_le bounded.2 bounded.1
    exact (QProb.toSignedRatio_equiv_iff _ _).mp
      (SignedRatio.equiv_trans (SignedRatio.equiv_symm indicator) same)
  · intro same
    have mean := SignedRatio.equiv_trans indicator (QProb.toSignedRatio_congr same)
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) mean).mpr (SignedRatio.le_refl _),
      (SignedRatio.le_congr mean (SignedRatio.equiv_refl _)).mpr (SignedRatio.le_refl _)⟩

theorem moments_iff_fits (observed : FiniteProbRecord S.Assignment) (law : Distro (Table S)) :
    (∀ constraint ∈ (problem S observed).intervals, constraint.LawHolds law) ↔ Fits S observed law.record := by
  constructor
  · intro moments event
    have cells : ∀ reference, QProb.Equiv
        ((law.record.map (eval S (FiniteLatentSCM.noIntervention S))).probVal (FiniteProbRecord.singletonEvent reference))
        (observed.probVal (FiniteProbRecord.singletonEvent reference)) := by
      intro reference
      have single := (eventMoment_iff law (observedEvent S reference) _).mp
        (moments (observationMoment S observed reference)
          (List.mem_map_of_mem (S.assignmentEnumeration_complete reference)))
      exact QProb.equiv_trans (law.record.map_probVal _ _) single
    exact QProb.equiv_trans (QProb.equiv_symm (law.record.map_probVal _ _))
      (FiniteProbRecord.probVal_extensional_of_singletons _ _ S.assignmentEnumeration
        S.assignmentEnumeration_nodup S.assignmentEnumeration_complete cells event)
  · intro fitted constraint member
    rcases List.mem_map.mp member with ⟨reference, _listed, same⟩
    cases same
    exact (eventMoment_iff law (observedEvent S reference) _).mpr
      (fitted (FiniteProbRecord.singletonEvent reference))

/-- Every table label is in the grid, even when its occurrence has zero mass.
The moment API only needs almost-sure membership; no support is discarded. -/
theorem law_supported {observed : FiniteProbRecord S.Assignment} (law : Distro (Table S)) :
    law.AlmostSurely (fun table => table ∈ (problem S observed).cells) := by
  intro atom _member _positive
  exact enumeration_complete S atom.1

theorem nativeFits_of_fits (observed : FiniteProbRecord S.Assignment) (law : FiniteProbRecord (Table S))
    (fitted : Fits S observed law) : NativeFits S observed (asProjectedModel S law) := by
  intro event
  exact QProb.equiv_trans (nativeModel_interventionalValue S law (HardIntervention.empty S) event) (fitted event)

theorem lawOfNative_fits (observed : FiniteProbRecord S.Assignment)
    (original : ProjectedHiddenDAGModel (graph S)) (fitted : NativeFits S observed original) :
    Fits S observed (lawOfNative S original.model) := by
  intro event
  exact QProb.equiv_trans (lawOfNative_interventionalValue S original.model (HardIntervention.empty S) event) (fitted event)

/-- Feasible linear masses already carry an actual rational record. Realizing
it gives an original native model, rather than leaving a simulation premise. -/
def fittedModel (observed : FiniteProbRecord S.Assignment) (law : (problem S observed).CompatibleLaw) :
    ProjectedHiddenDAGModel (graph S) := asProjectedModel S law.distro.record

theorem fittedModel_fits (observed : FiniteProbRecord S.Assignment) (law : (problem S observed).CompatibleLaw) :
    NativeFits S observed (fittedModel S observed law) :=
  nativeFits_of_fits S observed law.distro.record ((moments_iff_fits S observed law.distro).mp law.moments)

end Thesis.Causality.SharedResponse
