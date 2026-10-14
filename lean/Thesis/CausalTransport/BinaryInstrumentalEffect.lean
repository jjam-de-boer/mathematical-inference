import Thesis.CausalTransport.BinaryInstrumentalFeasibility

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# The signed average treatment effect on one IV response law

For Boolean outcomes the average treatment effect is
`Pr(Y(1)=true) - Pr(Y(0)=true)`.  It can be negative.  Natural-number
subtraction in `QProb` would silently truncate such an effect, so it is not
used here.  Instead, the linear optimizer's probability-valued objective is
the strictly increasing affine encoding `(ATE + 1) / 2`, namely
`(Pr(Y(1)=true) + Pr(Y(0)=false)) / 2`.

The response score has one common positive denominator and a natural
numerator.  Its decoding theorem identifies the *signed integer* numerator
of the ATE against the original finite record.  Integers occur only in that
integrand; all source weights remain ordinary nonnegative probability weights.
Thus a score below one half really encodes a negative treatment effect.

Native scores use the two actual intervention distributions.  Both risks
are transferred to the same response record, and every feasible response
score is realized on the original hidden DAG.  This is an exact attainable
set reduction, not a sharp-bound theorem, and does not subtract independently
attained endpoints or assume that their attaining models coincide.
-/

variable {P : FiniteLatentProjection signature}

def effectHalf : QProb := ⟨1, 2, by decide⟩

/-- Unit-level signed change of outcome.  Only the integrand, never an atom
weight or a probability numerator, is allowed to be negative. -/
def effectChange (profile : Profile) : Int :=
  (if outcomeAt profile true then 1 else 0) - (if outcomeAt profile false then 1 else 0)

/-- A linear score on the original response weights with denominator
`2 * responses.den`.  Zero response cells need no special convention. -/
def responseEffectScore (responses : FiniteProbRecord Profile) : QProb where
  num := FiniteProbRecord.eventMass responses.atoms (fun profile => outcomeAt profile true) +
    FiniteProbRecord.eventMass responses.atoms (fun profile => !outcomeAt profile false)
  den := 2 * responses.den
  den_pos := Nat.mul_pos (by decide) responses.den_pos

private theorem effectMass_eq_difference (atoms : List (Profile × Nat)) :
    FiniteProbRecord.signedAtomMass atoms effectChange =
      (FiniteProbRecord.eventMass atoms (fun profile => outcomeAt profile true) : Int) -
        (FiniteProbRecord.eventMass atoms (fun profile => outcomeAt profile false) : Int) := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨profile, weight⟩
      cases positive : outcomeAt profile true <;> cases negative : outcomeAt profile false <;>
        simp [FiniteProbRecord.signedAtomMass, FiniteProbRecord.eventMass,
          effectChange, positive, negative] at inductionHypothesis ⊢ <;>
        omega

/-- Exact signed decoding: the ATE is this integer numerator divided by
`responses.den`, equivalently `2 * responseEffectScore - 1`.  No rational
representative or negative probability record is introduced. -/
theorem responseEffectScore_signed (responses : FiniteProbRecord Profile) :
    ((responseEffectScore responses).num : Int) - (responses.den : Int) =
      responses.signedMass effectChange := by
  have partition := (FiniteProbRecord.eventMass_add_complement responses.atoms
    (fun profile => outcomeAt profile false)).trans responses.total_mass
  rw [FiniteProbRecord.signedMass, effectMass_eq_difference]
  change
    ((FiniteProbRecord.eventMass responses.atoms (fun profile => outcomeAt profile true) +
      FiniteProbRecord.eventMass responses.atoms (fun profile => !outcomeAt profile false) : Nat) : Int) -
        (responses.den : Int) = _
  rw [Int.natCast_add]
  have castPartition := congrArg (fun mass : Nat => (mass : Int)) partition
  simp only [Int.natCast_add] at castPartition
  omega

/-- The affine encoding is always a genuine value in `[0,1]`, even when
the signed effect is negative or the source law contains zeros. -/
theorem responseEffectScore_le_one (responses : FiniteProbRecord Profile) :
    QProb.LE (responseEffectScore responses) QProb.one := by
  have positiveBound := FiniteProbRecord.eventMass_le_totalMass responses.atoms
    (fun profile => outcomeAt profile true)
  have negativeBound := FiniteProbRecord.eventMass_le_totalMass responses.atoms
    (fun profile => !outcomeAt profile false)
  rw [responses.total_mass] at positiveBound negativeBound
  change _ + _ ≤ 2 * responses.den
  omega

/-- This common-denominator objective is exactly the average of the
success probability under treatment and failure probability under control. -/
theorem responseEffectScore_probVal (responses : FiniteProbRecord Profile) :
    QProb.Equiv
      (QProb.mul effectHalf (QProb.add
        (responses.probVal (fun profile => outcomeAt profile true))
        (responses.probVal (fun profile => !outcomeAt profile false))))
      (responseEffectScore responses) :=
  QProb.equiv_trans
    (QProb.mul_congr (QProb.equiv_refl effectHalf)
      (QProb.add_mk_same_den responses.den responses.den_pos _ _))
    (by simp only [QProb.Equiv, QProb.mul, effectHalf, responseEffectScore, Nat.one_mul])

/-- Actual native interventions define the same increasing affine ATE
encoding.  The two probabilities come from one model, not separate witnesses. -/
def nativeEffectScore (native : FiniteHiddenDAGSCM signature P) : QProb :=
  QProb.mul effectHalf (QProb.add
    (native.interventionalValue (intervention true) (fun sample => sample y))
    (native.interventionalValue (intervention false) (fun sample => !sample y)))

/-- Equality of the two treatment risks is sufficient for equality of the
signed-effect encoding.  The control failure probability is recovered by
the proved Boolean partition theorem, including probability-zero boundaries. -/
theorem nativeEffectScore_of_responses (native : FiniteHiddenDAGSCM signature P)
    (responses : FiniteProbRecord Profile)
    (same : forall action, QProb.Equiv
      (native.interventionalValue (intervention action) (fun sample => sample y))
      ((effectRecord responses action).probVal id)) :
    QProb.Equiv (nativeEffectScore native) (responseEffectScore responses) := by
  have controlFailure := (FiniteProbRecord.probVal_complement_equiv_iff
    (native.interventionalDist (intervention false)) (fun sample => sample y)
    (effectRecord responses false) id).mpr (same false)
  have control : QProb.Equiv
      (native.interventionalValue (intervention false) (fun sample => !sample y))
      (responses.probVal (fun profile => !outcomeAt profile false)) :=
    QProb.equiv_trans controlFailure
      (responses.map_probVal (fun profile => outcomeAt profile false) (fun bit => !bit))
  exact QProb.equiv_trans
    (QProb.mul_congr (QProb.equiv_refl effectHalf)
      (QProb.add_congr (QProb.equiv_trans (same true) (effectRecord_probVal responses true)) control))
    (responseEffectScore_probVal responses)

theorem nativeEffectScore_response (native : FiniteHiddenDAGSCM signature P)
    (graphMatch : HasIVProjection P) :
    QProb.Equiv (nativeEffectScore native)
      (responseEffectScore (responseRepresentation native graphMatch).responses) :=
  nativeEffectScore_of_responses native _ (responseRepresentation native graphMatch).interventional

/-- An attained score needs a genuine original-DAG model with the whole
observed law.  Incompatibility cannot masquerade as a sharp bound. -/
def EffectScoreAttainableAt (projection : FiniteLatentProjection signature)
    (law : FiniteProbRecord signature.Assignment) (score : QProb) : Prop :=
  ∃ native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native law ∧
    QProb.Equiv (nativeEffectScore native) score

/-- The full native signed-effect attainable set is exactly the scores of
feasible response records.  This is the load-bearing semantic prerequisite
for optimizing the average treatment effect alongside the individual risks. -/
theorem effectScoreAttainableAt_iff (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (score : QProb) :
    EffectScoreAttainableAt projection law score ↔
      ∃ responses : FiniteProbRecord Profile, FeasibleResponses law responses ∧
        QProb.Equiv (responseEffectScore responses) score := by
  constructor
  · rintro ⟨native, observed, attained⟩
    refine ⟨(responseRepresentation native graphMatch).responses,
      native_responses_feasible native graphMatch law observed, ?_⟩
    exact QProb.equiv_trans (QProb.equiv_symm (nativeEffectScore_response native graphMatch)) attained
  · rintro ⟨responses, feasible, attained⟩
    let native := nativeProfileModel projection graphMatch (instrumentMarginal law) responses
    refine ⟨native, nativeProfileModel_hasObservedLaw projection graphMatch law responses feasible, ?_⟩
    exact QProb.equiv_trans
      (nativeEffectScore_of_responses native responses
        (nativeProfileModel_interventionalValue projection graphMatch (instrumentMarginal law) responses))
      attained

end BinaryInstrumental
end Causality
end Thesis
