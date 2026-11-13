import Thesis.CausalTransport.BinaryInstrumental.Identification
import Thesis.CausalTransport.BinaryInstrumental.Mixtures

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Complete rational attainable sets for binary IV

Every rational pair inside the two computed treatment-risk intervals is
realized by one native model with the *entire* supplied observed law.  First
mix along each of two parallel edges of the four attained risk corners,
using the same control weights.  Then mix the resulting edges using the
treated weights.  The control risk is constant in that last mixture.  This
proves a rectangle of simultaneous risks, not two unrelated scalar claims.

The signed ATE's increasing affine score has its complete rational interval
as well: mix its two attained endpoints.  All interpolation is exact and
constructive, including zero mixing weights and collapsed intervals.  Native
realization is the response-record construction of `BinaryInstrumental.Mixtures`,
not an unproved convexity assertion about arbitrary hidden-DAG model classes.

The final iff statements include the computed compatibility flag.  Thus an
incompatible law has an empty attainable set, not a vacuously sharp interval.
Either instrument value may be absent; observed zeros, unrestricted finite
hidden sizes, and both signs of the ATE remain covered.
-/

/-- Two successive one-coordinate interpolations construct all rational
interior pairs and all boundary pairs on this very same original hidden DAG. -/
theorem risksAttainableAt_of_computed_bounds (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (checked : (computedBounds law).compatible = true) (risks : Bool → QProb)
    (bounds : forall action, QProb.LE ((computedBounds law).lowerRisk action) (risks action) ∧
      QProb.LE (risks action) ((computedBounds law).upperRisk action)) :
    RisksAttainableAt projection law risks := by
  obtain ⟨controlLeft, controlRight, controlPositive, controlValue⟩ :=
    QProb.exists_weightedPair_equiv _ _ _ (bounds false).1 (bounds false).2
  obtain ⟨treatedLeft, treatedRight, treatedPositive, treatedValue⟩ :=
    QProb.exists_weightedPair_equiv _ _ _ (bounds true).1 (bounds true).2
  have stripe (treatedUpper : Bool) : RisksAttainableAt projection law (fun action =>
      if action then (if treatedUpper then (computedBounds law).upperRisk true else (computedBounds law).lowerRisk true)
      else risks false) := by
    have first := computedBounds_risk_corners projection graphMatch law checked false treatedUpper
    have second := computedBounds_risk_corners projection graphMatch law checked true treatedUpper
    have mixed := risksAttainableAt_mixture projection graphMatch law _ _ first second
      controlLeft controlRight controlPositive
    apply risksAttainableAt_congr projection law mixed
    intro action
    cases action
    · exact controlValue
    · exact QProb.weightedPair_constant controlLeft controlRight controlPositive _
  have mixed := risksAttainableAt_mixture projection graphMatch law _ _ (stripe false) (stripe true)
    treatedLeft treatedRight treatedPositive
  apply risksAttainableAt_congr projection law mixed
  intro action
  cases action
  · exact QProb.weightedPair_constant treatedLeft treatedRight treatedPositive (risks false)
  · exact treatedValue

/-- Exact simultaneous risk attainable set, including incompatible laws.
No restrictions on the requested rational presentations or their denominators
are imposed beyond the displayed necessary and sufficient bounds. -/
theorem risksAttainableAt_iff_computed_bounds (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (risks : Bool → QProb) :
    RisksAttainableAt projection law risks ↔
      (computedBounds law).compatible = true ∧
        forall action, QProb.LE ((computedBounds law).lowerRisk action) (risks action) ∧
          QProb.LE (risks action) ((computedBounds law).upperRisk action) := by
  constructor
  · rintro ⟨native, observed, values⟩
    refine ⟨(computedBounds_compatible_iff projection graphMatch law).mpr ⟨native, observed⟩, ?_⟩
    intro action
    have bounds := computedBounds_native_risks native graphMatch law observed action
    exact ⟨QProb.le_congr (QProb.equiv_refl _) (values action) bounds.1,
      QProb.le_congr (values action) (QProb.equiv_refl _) bounds.2⟩
  · rintro ⟨checked, bounds⟩
    exact risksAttainableAt_of_computed_bounds projection graphMatch law checked risks bounds

/-- The rational interval between the sharp signed-effect endpoints is
fully attained.  Scores below one half represent genuinely negative ATEs. -/
theorem effectScoreAttainableAt_of_computed_bounds (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (checked : (computedBounds law).compatible = true) (score : QProb)
    (lower : QProb.LE (computedBounds law).lowerEffect score)
    (upper : QProb.LE score (computedBounds law).upperEffect) :
    EffectScoreAttainableAt projection law score := by
  obtain ⟨leftWeight, rightWeight, positive, value⟩ := QProb.exists_weightedPair_equiv _ _ _ lower upper
  have endpoints := computedBounds_effect_endpoints projection graphMatch law checked
  exact effectScoreAttainableAt_congr projection law
    (effectScoreAttainableAt_mixture projection graphMatch law _ _ endpoints.1 endpoints.2 leftWeight rightWeight positive) value

/-- Exact signed-ATE attainable set via its injective score `(ATE + 1)/2`.
Unlike an endpoint-only sharpness statement, this includes every rational
interior score, with a whole-law-preserving native witness. -/
theorem effectScoreAttainableAt_iff_computed_bounds (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (score : QProb) :
    EffectScoreAttainableAt projection law score ↔
      (computedBounds law).compatible = true ∧
        QProb.LE (computedBounds law).lowerEffect score ∧ QProb.LE score (computedBounds law).upperEffect := by
  constructor
  · rintro ⟨native, observed, value⟩
    have bounds := computedBounds_native_effect native graphMatch law observed
    exact ⟨(computedBounds_compatible_iff projection graphMatch law).mpr ⟨native, observed⟩,
      QProb.le_congr (QProb.equiv_refl _) value bounds.1,
      QProb.le_congr value (QProb.equiv_refl _) bounds.2⟩
  · rintro ⟨checked, lower, upper⟩
    exact effectScoreAttainableAt_of_computed_bounds projection graphMatch law checked score lower upper

end BinaryInstrumental
end Causality
end Thesis
