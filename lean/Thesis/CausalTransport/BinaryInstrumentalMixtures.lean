import Thesis.CausalTransport.BinaryInstrumentalEffect
import Thesis.Probability.RationalMixture

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Whole-law-preserving mixtures of feasible IV response records

The observed instrument marginal is held fixed.  Its eight response-cell
equations are linear, so normalized mixtures of feasible response records
remain feasible for the *same whole observed law*, even at null instrument
values.  Both treatment risks and the signed-effect score vary linearly.

Native closure is obtained by extracting response records, mixing those
records, and realizing one new native model on the original DAG.  This does
not assert that an arbitrary mixture of independent-source SCMs retains
independence.  The existing IV realization theorem is load-bearing: its
independent instrument is unchanged, and the shared response source may have
any finite rational law.  No monotonicity or hidden-cardinality restriction is
introduced, and both risks always belong to one actual native model.
-/

/-- Preserve all eight joint-cell equations without division or cancelling
an instrument mass.  Null instrument arms are therefore included directly. -/
theorem feasibleResponses_mixture (law : FiniteProbRecord signature.Assignment)
    (left right : FiniteProbRecord Profile) (leftFeasible : FeasibleResponses law left)
    (rightFeasible : FeasibleResponses law right) (leftWeight rightWeight : Nat)
    (positive : 0 < leftWeight + rightWeight) :
    FeasibleResponses law (left.mixture right leftWeight rightWeight positive) := by
  intro instrument treatment outcome
  let coefficient := (instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent instrument)
  let event := responseCell instrument treatment outcome
  exact QProb.equiv_trans (QProb.equiv_symm
      (QProb.weightedPair_constant leftWeight rightWeight positive (law.probVal (observedCell instrument treatment outcome))))
    (QProb.equiv_trans
      (QProb.weightedPair_congr leftWeight rightWeight positive
        (leftFeasible instrument treatment outcome) (rightFeasible instrument treatment outcome))
      (QProb.equiv_trans (QProb.equiv_symm
        (QProb.weightedPair_mul_left leftWeight rightWeight positive coefficient (left.probVal event) (right.probVal event)))
        (QProb.mul_congr (QProb.equiv_refl coefficient)
          (QProb.equiv_symm (left.mixture_probVal right leftWeight rightWeight positive event)))))

theorem effectRecord_mixture_probVal (left right : FiniteProbRecord Profile)
    (leftWeight rightWeight : Nat) (positive : 0 < leftWeight + rightWeight) (action : Bool) :
    QProb.Equiv ((effectRecord (left.mixture right leftWeight rightWeight positive) action).probVal id)
      (QProb.weightedPair leftWeight rightWeight positive
        ((effectRecord left action).probVal id) ((effectRecord right action).probVal id)) :=
  QProb.equiv_trans (effectRecord_probVal _ action)
    (QProb.equiv_trans (left.mixture_probVal right leftWeight rightWeight positive (fun profile => outcomeAt profile action))
      (QProb.weightedPair_congr leftWeight rightWeight positive
        (QProb.equiv_symm (effectRecord_probVal left action)) (QProb.equiv_symm (effectRecord_probVal right action))))

/-- The score uses treated success and control failure on the same response
weights.  This direct numerator identity preserves signed ATE semantics even
when the score is below one half; no subtraction of natural weights occurs. -/
theorem responseEffectScore_mixture (left right : FiniteProbRecord Profile)
    (leftWeight rightWeight : Nat) (positive : 0 < leftWeight + rightWeight) :
    QProb.Equiv (responseEffectScore (left.mixture right leftWeight rightWeight positive))
      (QProb.weightedPair leftWeight rightWeight positive (responseEffectScore left) (responseEffectScore right)) := by
  simp only [QProb.Equiv, responseEffectScore, QProb.weightedPair, FiniteProbRecord.mixture_eventMass]
  simp only [FiniteProbRecord.mixture, Nat.add_mul, Nat.mul_add]
  ac_rfl

theorem risksAttainableAt_congr (projection : FiniteLatentProjection signature)
    (law : FiniteProbRecord signature.Assignment) {left right : Bool → QProb}
    (attained : RisksAttainableAt projection law left) (same : forall action, QProb.Equiv (left action) (right action)) :
    RisksAttainableAt projection law right := by
  obtain ⟨native, observed, values⟩ := attained
  exact ⟨native, observed, fun action => QProb.equiv_trans (values action) (same action)⟩

/-- One actual original-DAG model realizes the coordinatewise mixture of
two attainable risk pairs, with its entire observed law unchanged. -/
theorem risksAttainableAt_mixture (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (left right : Bool → QProb) (leftAttained : RisksAttainableAt projection law left)
    (rightAttained : RisksAttainableAt projection law right) (leftWeight rightWeight : Nat)
    (positive : 0 < leftWeight + rightWeight) :
    RisksAttainableAt projection law (fun action => QProb.weightedPair leftWeight rightWeight positive (left action) (right action)) := by
  obtain ⟨leftResponses, leftFeasible, leftValues⟩ := (risksAttainableAt_iff projection graphMatch law left).mp leftAttained
  obtain ⟨rightResponses, rightFeasible, rightValues⟩ := (risksAttainableAt_iff projection graphMatch law right).mp rightAttained
  apply (risksAttainableAt_iff projection graphMatch law _).mpr
  refine ⟨leftResponses.mixture rightResponses leftWeight rightWeight positive,
    feasibleResponses_mixture law leftResponses rightResponses leftFeasible rightFeasible leftWeight rightWeight positive, ?_⟩
  intro action
  exact QProb.equiv_trans (effectRecord_mixture_probVal leftResponses rightResponses leftWeight rightWeight positive action)
    (QProb.weightedPair_congr leftWeight rightWeight positive (leftValues action) (rightValues action))

theorem effectScoreAttainableAt_congr (projection : FiniteLatentProjection signature)
    (law : FiniteProbRecord signature.Assignment) {left right : QProb}
    (attained : EffectScoreAttainableAt projection law left) (same : QProb.Equiv left right) :
    EffectScoreAttainableAt projection law right := by
  obtain ⟨native, observed, value⟩ := attained
  exact ⟨native, observed, QProb.equiv_trans value same⟩

/-- Effect interpolation also produces one genuine native model, not a
formal average of scores with no graph-compatible realizing model. -/
theorem effectScoreAttainableAt_mixture (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (left right : QProb) (leftAttained : EffectScoreAttainableAt projection law left)
    (rightAttained : EffectScoreAttainableAt projection law right) (leftWeight rightWeight : Nat)
    (positive : 0 < leftWeight + rightWeight) :
    EffectScoreAttainableAt projection law (QProb.weightedPair leftWeight rightWeight positive left right) := by
  obtain ⟨leftResponses, leftFeasible, leftValue⟩ := (effectScoreAttainableAt_iff projection graphMatch law left).mp leftAttained
  obtain ⟨rightResponses, rightFeasible, rightValue⟩ := (effectScoreAttainableAt_iff projection graphMatch law right).mp rightAttained
  apply (effectScoreAttainableAt_iff projection graphMatch law _).mpr
  refine ⟨leftResponses.mixture rightResponses leftWeight rightWeight positive,
    feasibleResponses_mixture law leftResponses rightResponses leftFeasible rightFeasible leftWeight rightWeight positive, ?_⟩
  exact QProb.equiv_trans (responseEffectScore_mixture leftResponses rightResponses leftWeight rightWeight positive)
    (QProb.weightedPair_congr leftWeight rightWeight positive leftValue rightValue)

end BinaryInstrumental
end Causality
end Thesis
