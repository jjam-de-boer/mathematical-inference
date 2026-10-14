import Thesis.Causality.BinaryInstrumentalCoupling
import Thesis.CausalTransport.BinaryInstrumentalFeasibility
import Thesis.Probability.FourLabelTransportationJointExtrema

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Whole-law IV compatibility through a permitted coupling table

The transportation table has four treatment/outcome labels on each side.
Its arm margins are compared with the observed joint cells using the fixed
instrument marginal.  Null instrument values therefore impose zero joint
constraints, not invented conditional tables.  Permittedness is the actual
same-treatment/same-outcome consistency restriction of response profiles.

The exact equivalence below ranges over every native model on the original
hidden DAG.  A forward native model supplies its real response coupling;
a reverse coupling supplies explicit profiles, then a constructed native
model with the supplied *whole* law.  It is not a relaxation certified only
by matching some outcome moments or by an external realization assumption.

Changing the fill rule preserves observations but can change causal risks.
This freedom will be used to realize extremal response assignments after
the permitted-cell transportation problem has been solved.  Nothing here
claims that every possible set of arm margins admits a permitted coupling.
-/

variable {P : FiniteLatentProjection signature}

/-- The observation constraints of the four-by-four table.  These are
linear in its masses once the observed instrument factor has been fixed. -/
def CouplingFits (law : FiniteProbRecord signature.Assignment)
    (coupling : FiniteProbRecord ResponsePair) : Prop :=
  forall instrument treatment outcome : Bool,
    QProb.Equiv (law.probVal (observedCell instrument treatment outcome))
      (QProb.mul ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent instrument))
        (coupling.probVal (couplingCell instrument treatment outcome)))

theorem responseCoupling_fits (law : FiniteProbRecord signature.Assignment)
    (responses : FiniteProbRecord Profile) (feasible : FeasibleResponses law responses) :
    CouplingFits law (responseCoupling responses) := by
  intro instrument treatment outcome
  exact QProb.equiv_trans (feasible instrument treatment outcome)
    (QProb.mul_congr (QProb.equiv_refl _)
      (QProb.equiv_symm (responseCoupling_cell responses instrument treatment outcome)))

/-- Every explicit fill rule gives a feasible response law.  This theorem
retains whole observational agreement without promising that causal values
stay fixed while filling an unobserved response bit. -/
theorem responsesOfCoupling_feasible (law : FiniteProbRecord signature.Assignment)
    (coupling : FiniteProbRecord ResponsePair)
    (permitted : QProb.Equiv (coupling.probVal permittedPair) QProb.one)
    (fits : CouplingFits law coupling) (fill : ResponsePair → Bool) :
    FeasibleResponses law (responsesOfCoupling coupling fill) := by
  intro instrument treatment outcome
  exact QProb.equiv_trans (fits instrument treatment outcome)
    (QProb.mul_congr (QProb.equiv_refl _)
      (QProb.equiv_symm (responsesOfCoupling_cell coupling permitted fill instrument treatment outcome)))

/-- Original-DAG compatibility is exactly existence of an actual rational
coupling concentrated on permitted cells and satisfying the joint-cell
constraints.  This does not make incompatibility a vacuous sharp interval. -/
theorem nativeModelExists_iff_coupling (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment) :
    (∃ native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native law) ↔
      ∃ coupling : FiniteProbRecord ResponsePair,
        QProb.Equiv (coupling.probVal permittedPair) QProb.one ∧ CouplingFits law coupling := by
  constructor
  · rintro ⟨native, observed⟩
    let responses := (responseRepresentation native graphMatch).responses
    exact ⟨responseCoupling responses, responseCoupling_permitted responses,
      responseCoupling_fits law responses (native_responses_feasible native graphMatch law observed)⟩
  · rintro ⟨coupling, permitted, fits⟩
    let responses := responsesOfCoupling coupling (fun _ => false)
    exact ⟨nativeProfileModel projection graphMatch (instrumentMarginal law) responses,
      nativeProfileModel_hasObservedLaw projection graphMatch law responses
        (responsesOfCoupling_feasible law coupling permitted fits (fun _ => false))⟩

end BinaryInstrumental
end Causality
end Thesis
