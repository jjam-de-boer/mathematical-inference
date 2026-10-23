import Thesis.Probability.EntropyInterpretation
import Thesis.Probability.ConstructiveRealRationalScaling

namespace Thesis.Probability.ConstructiveReal

/-- Rational coefficient representation changes do not change real scaling. -/
theorem scaleRatio_weight_congr {first second : QProb} (same : QProb.Equiv first second) (x : ConstructiveReal) :
    Equiv (scaleRatio first x) (scaleRatio second x) :=
  equiv_trans (scaleRatio_mul first x) (equiv_trans
    (mul_congr ((ofSignedRatio_equiv_iff _ _).mpr ((QProb.toSignedRatio_equiv_iff _ _).mpr same)) (equiv_refl _))
    (equiv_symm (scaleRatio_mul second x)))

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability

/-- On positive rational mass, the exact entropy term interprets as an
ordinary real product, using the constructed multiplication. -/
theorem entropyTerm_interpret_mul (mass : QProb) (positive : 0 < mass.num) :
    ConstructiveReal.Equiv (entropyTerm mass).interpret
      (ConstructiveReal.neg (ConstructiveReal.mul (ConstructiveReal.ofSignedRatio mass.toSignedRatio)
        (ConstructiveReal.rationalLog2 ⟨mass.num, mass.den, positive, mass.den_pos⟩))) := by
  apply ConstructiveReal.equiv_trans (entropyTerm_interpret mass)
  simp only [ConstructiveReal.entropyTerm, positive, ↓reduceDIte]
  exact ConstructiveReal.neg_congr (ConstructiveReal.scaleRatio_mul _ _)

/-- The complete Shannon sum uses ordinary real products and the explicit
zero-mass convention. The logarithm still has positive rational arguments. -/
theorem entropySum_interpret_mul (masses : List QProb) :
    ConstructiveReal.Equiv (entropySum masses).interpret
      (ConstructiveReal.listSum (masses.map (fun mass =>
        if positive : 0 < mass.num then
          ConstructiveReal.neg (ConstructiveReal.mul (ConstructiveReal.ofSignedRatio mass.toSignedRatio)
            (ConstructiveReal.rationalLog2 ⟨mass.num, mass.den, positive, mass.den_pos⟩))
        else ConstructiveReal.zero))) := by
  apply ConstructiveReal.equiv_trans (entropySum_interpret masses)
  apply ConstructiveReal.listSum_map_congr
  intro mass _
  by_cases positive : 0 < mass.num
  · simp only [ConstructiveReal.entropyTerm, positive, ↓reduceDIte]
    exact ConstructiveReal.neg_congr (ConstructiveReal.scaleRatio_mul _ _)
  · simp only [ConstructiveReal.entropyTerm, positive, ↓reduceDIte]
    exact ConstructiveReal.equiv_refl _

/-- The exact KL summand similarly interprets as `p (log₂ p − log₂ r)`
with the constructed general product. -/
theorem relativeEntropyTerm_interpret_mul (observed reference : QProb)
    (observedPositive : 0 < observed.num) (referencePositive : 0 < reference.num) :
    ConstructiveReal.Equiv (relativeEntropyTerm observed reference referencePositive).interpret
      (ConstructiveReal.mul (ConstructiveReal.ofSignedRatio observed.toSignedRatio)
        (ConstructiveReal.sub (ConstructiveReal.rationalLog2 ⟨observed.num, observed.den, observedPositive, observed.den_pos⟩)
          (ConstructiveReal.rationalLog2 ⟨reference.num, reference.den, referencePositive, reference.den_pos⟩))) := by
  apply ConstructiveReal.equiv_trans (relativeEntropyTerm_interpret observed reference referencePositive)
  simp only [ConstructiveReal.relativeEntropyTerm, observedPositive, ↓reduceDIte]
  exact ConstructiveReal.scaleRatio_mul _ _

end Thesis.Probability
