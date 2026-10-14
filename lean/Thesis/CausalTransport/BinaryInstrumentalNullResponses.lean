import Thesis.CausalTransport.BinaryInstrumentalSharpBounds

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Actual IV response witnesses when one instrument value has zero mass

The observed law then determines only one instrument arm.  A witness may
copy its factual treatment into both response arms, and retain the factual
outcome under that treatment.  The other treatment outcome is filled in the
requested lower/upper direction.  This is an explicit feasible witness, not
a claim that every compatible model has equal treatment responses in both
arms or that the missing arm has an observed conditional distribution.

The construction maps the original finite record, retaining its weights,
denominator, repeated labels and zeros.  The missing instrument mass is
never divided out.  Its complement has probability one by Boolean partition
and normalization, so the eight joint-cell equations preserve the entire
observed law.  The already proved native realization then supplies a genuine
SCM on the original hidden DAG, with unrestricted finite hidden alphabets.

The raw selected-outcome equality is proved separately from feasibility.
It identifies the precise factual mass attained by the fill rule, and will
support sharp risk and signed-effect endpoints for the null-instrument branch.
-/

def factualOutcomeEvent (action outcome : Bool) : Event signature.Assignment :=
  fun sample => decide (sample x = action) && decide (sample y = outcome)

def factualOutcomeMass (law : FiniteProbRecord signature.Assignment) (action outcome : Bool) : Nat :=
  FiniteProbRecord.eventMass law.atoms (factualOutcomeEvent action outcome)

/-- Both treatment-response bits copy the factual treatment.  Only its
unobserved opposite treatment outcome receives the selected fill value. -/
def nullProfile (controlUpper treatedUpper : Bool) (sample : signature.Assignment) : Profile :=
  profileOfPair ((sample x, sample y), (sample x, sample y))
    (if sample x then controlUpper else treatedUpper)

def nullResponses (law : FiniteProbRecord signature.Assignment) (controlUpper treatedUpper : Bool) :
    FiniteProbRecord Profile := law.map (nullProfile controlUpper treatedUpper)

private theorem null_profile_cell : forall factualX factualY controlUpper treatedUpper instrument action outcome : Bool,
    responseCell instrument action outcome
        (profileOfPair ((factualX, factualY), (factualX, factualY))
          (if factualX then controlUpper else treatedUpper)) =
      (decide (factualX = action) && decide (factualY = outcome)) := by
  decide +kernel

private theorem null_profile_selected : forall factualX factualY controlUpper treatedUpper action : Bool,
    outcomeEvent action (!(endpointUpper controlUpper treatedUpper action))
        (profileOfPair ((factualX, factualY), (factualX, factualY))
          (if factualX then controlUpper else treatedUpper)) =
      (decide (factualX = action) && decide (factualY = !(endpointUpper controlUpper treatedUpper action))) := by
  decide +kernel

/-- Each arm of the constructed record has the observed factual `(X,Y)`
law.  Only its nonnull arm is constrained by observations; the other copy
is a legitimate witness choice, not a restriction on all native models. -/
theorem nullResponses_cell (law : FiniteProbRecord signature.Assignment)
    (controlUpper treatedUpper instrument action outcome : Bool) :
    QProb.Equiv ((nullResponses law controlUpper treatedUpper).probVal (responseCell instrument action outcome))
      (law.probVal (factualOutcomeEvent action outcome)) :=
  QProb.equiv_trans (law.map_probVal (nullProfile controlUpper treatedUpper) (responseCell instrument action outcome))
    (law.probVal_congr _ _ (fun sample => null_profile_cell (sample x) (sample y)
      controlUpper treatedUpper instrument action outcome))

theorem nullResponses_selected_outcome_mass (law : FiniteProbRecord signature.Assignment)
    (controlUpper treatedUpper action : Bool) :
    FiniteProbRecord.eventMass (nullResponses law controlUpper treatedUpper).atoms
        (outcomeEvent action (!(endpointUpper controlUpper treatedUpper action))) =
      factualOutcomeMass law action (!(endpointUpper controlUpper treatedUpper action)) := by
  change FiniteProbRecord.eventMass (law.atoms.map (fun atom => (nullProfile controlUpper treatedUpper atom.1, atom.2))) _ = _
  rw [FiniteProbRecord.eventMass_map_labels]
  exact FiniteProbRecord.eventMass_congr law.atoms _ _ (fun sample => null_profile_selected
    (sample x) (sample y) controlUpper treatedUpper action)

/-- Zero mass for the opposite Boolean value forces the active value's
mass to equal the full positive denominator.  No cell positivity is used. -/
theorem nullInstrument_active_mass (law : FiniteProbRecord signature.Assignment) (active : Bool)
    (missing : instrumentMass law (!active) = 0) : instrumentMass law active = law.den := by
  have partition := instrumentMass_partition law
  cases active
  · change instrumentMass law true = 0 at missing
    rw [missing, Nat.add_zero] at partition
    exact partition
  · change instrumentMass law false = 0 at missing
    rw [missing, Nat.zero_add] at partition
    exact partition

theorem nullInstrument_active_full (law : FiniteProbRecord signature.Assignment) (active : Bool)
    (missing : instrumentMass law (!active) = 0) :
    QProb.Equiv (law.probVal (instrumentEvent active)) QProb.one := by
  change instrumentMass law active * 1 = 1 * law.den
  rw [nullInstrument_active_mass law active missing]
  simp only [Nat.mul_one, Nat.one_mul]

theorem nullInstrument_marginal_full (law : FiniteProbRecord signature.Assignment) (active : Bool)
    (missing : instrumentMass law (!active) = 0) :
    QProb.Equiv ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent active)) QProb.one :=
  QProb.equiv_trans (instrumentMarginal_probVal law active) (by
    change instrumentMass law active * 1 = 1 * law.den
    rw [nullInstrument_active_mass law active missing]
    simp only [Nat.mul_one, Nat.one_mul])

/-- Whole-law probability-one support makes the active joint cell equal
to its factual `(X,Y)` marginal, including zero-weight off-support labels. -/
theorem nullInstrument_active_cell (law : FiniteProbRecord signature.Assignment) (active : Bool)
    (missing : instrumentMass law (!active) = 0) (action outcome : Bool) :
    QProb.Equiv (law.probVal (observedCell active action outcome))
      (law.probVal (factualOutcomeEvent action outcome)) :=
  law.probVal_congr_on_probability_one (instrumentEvent active) _ _
    (nullInstrument_active_full law active missing) (by
      intro sample selected
      have same : sample z = active := of_decide_eq_true selected
      simp only [observedCell, factualOutcomeEvent, same, decide_true, Bool.true_and])

/-- Every requested fill is feasible for the complete law.  The inactive
joint cells and their instrument coefficients are both genuinely zero;
no arbitrary conditional at that missing arm is introduced. -/
theorem nullResponses_feasible (law : FiniteProbRecord signature.Assignment) (active : Bool)
    (missing : instrumentMass law (!active) = 0) (controlUpper treatedUpper : Bool) :
    FeasibleResponses law (nullResponses law controlUpper treatedUpper) := by
  intro instrument action outcome
  by_cases same : instrument = active
  · subst instrument
    have product : QProb.Equiv
        (QProb.mul ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent active))
          ((nullResponses law controlUpper treatedUpper).probVal (responseCell active action outcome)))
        (law.probVal (factualOutcomeEvent action outcome)) :=
      QProb.equiv_trans
        (QProb.mul_congr (nullInstrument_marginal_full law active missing)
          (nullResponses_cell law controlUpper treatedUpper active action outcome))
        (by simp only [QProb.Equiv, QProb.mul, QProb.one, Nat.one_mul])
    exact QProb.equiv_trans (nullInstrument_active_cell law active missing action outcome)
      (QProb.equiv_symm product)
  · have opposite : instrument = !active := by
      cases active <;> cases instrument
      · exact False.elim (same rfl)
      · rfl
      · rfl
      · exact False.elim (same rfl)
    have zeroCoefficient : QProb.Equiv
        ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent instrument)) QProb.zero := by
      apply QProb.equiv_trans (instrumentMarginal_probVal law instrument)
      change instrumentMass law instrument * 1 = 0 * law.den
      rw [opposite, missing]
    have zeroCell : QProb.Equiv (law.probVal (observedCell instrument action outcome)) QProb.zero :=
      QProb.equiv_trans
        (law.probVal_congr_on_probability_one (instrumentEvent active) _ (fun _ => false)
          (nullInstrument_active_full law active missing) (by
            intro sample selected
            have atActive : sample z = active := of_decide_eq_true selected
            have away : sample z ≠ instrument := fun equal => same (equal.symm.trans atActive)
            simp only [observedCell, away, decide_false, Bool.false_and]))
        law.probVal_false
    have zeroProduct : QProb.Equiv
        (QProb.mul ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent instrument))
          ((nullResponses law controlUpper treatedUpper).probVal (responseCell instrument action outcome))) QProb.zero :=
      QProb.equiv_trans (QProb.mul_congr zeroCoefficient (QProb.equiv_refl _))
        (by simp only [QProb.Equiv, QProb.mul, QProb.zero, Nat.zero_mul])
    exact QProb.equiv_trans zeroCell (QProb.equiv_symm zeroProduct)

/-- Any whole law supported on one instrument value admits a genuine native
IV model.  No observed capacity test on a fictitious second arm is needed. -/
theorem nullInstrument_native_exists (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (active : Bool) (missing : instrumentMass law (!active) = 0) :
    ∃ native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native law :=
  ⟨nativeProfileModel projection graphMatch (instrumentMarginal law) (nullResponses law false false),
    nativeProfileModel_hasObservedLaw projection graphMatch law (nullResponses law false false)
      (nullResponses_feasible law active missing false false)⟩

end BinaryInstrumental
end Causality
end Thesis
