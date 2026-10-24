import Thesis.Probability.RationalExponentialVariation
import Thesis.Probability.RationalApproximationSequence
import Thesis.Probability.ConstructiveRealDifferenceLimits
import Thesis.Probability.ConstructiveRealErrorLimits
import Thesis.Probability.ConstructiveRealExpLimits

namespace Thesis.Probability.SignedRatio

private theorem magnitude_square (value : SignedRatio) :
    Equiv (QProb.mul value.magnitude value.magnitude).toSignedRatio (mul value value) := by
  simp only [Equiv, QProb.mul, QProb.toSignedRatio, magnitude, mul, Int.natCast_mul, Int.natAbs_mul_self']

/-- The rational squared-error expression is exactly the signed square, with
no positivity or sign decision on the increment required. -/
theorem quadratic_error_value (a b : SignedRatio) (bound : Nat) :
    Equiv (QProb.mul (RationalTaylorExponential.quadraticError a b) (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound))).toSignedRatio
      (mul (mul (sub b a) (sub b a)) (⟨RationalTaylorExponential.uniformSumBound bound, 2, by decide⟩ : QProb).toSignedRatio) := by
  have scalar : QProb.Equiv (QProb.mul (⟨1, 2, by decide⟩ : QProb) (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound)))
      (⟨RationalTaylorExponential.uniformSumBound bound, 2, by decide⟩ : QProb) := by
    simp only [QProb.Equiv, QProb.mul, QProb.ofNat, Nat.one_mul, Nat.mul_one]
  have grouped : QProb.Equiv
      (QProb.mul (RationalTaylorExponential.quadraticError a b) (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound)))
      (QProb.mul (QProb.mul (sub b a).magnitude (sub b a).magnitude)
        (⟨RationalTaylorExponential.uniformSumBound bound, 2, by decide⟩ : QProb)) :=
    QProb.equiv_trans (QProb.mul_assoc _ _ _) (QProb.mul_congr (QProb.equiv_refl _) scalar)
  have projected := QProb.toSignedRatio_congr grouped
  apply equiv_trans projected
  rw [QProb.toSignedRatio_mul]
  exact mul_congr (magnitude_square _) (equiv_refl _)

end Thesis.Probability.SignedRatio

namespace Thesis.Probability.ConstructiveReal

/-- Linear Taylor approximation at the first input, evaluated at the second. -/
def expLinear (x y : ConstructiveReal) : ConstructiveReal := add x.exp (mul (sub y x) x.exp)

/-- The real quadratic error uses an explicit finite interval constant from
the rational Taylor bound. It introduces no real absolute-value decision. -/
def expQuadraticError (x y : ConstructiveReal) (bound : Nat) : ConstructiveReal :=
  mul (mul (sub y x) (sub y x))
    (ofSignedRatio (⟨RationalTaylorExponential.uniformSumBound bound, 2, by decide⟩ : QProb).toSignedRatio)

private theorem first_variation_sequences (a b : RationalCauchySequence) (x y : ConstructiveReal)
    (limitA : Equiv a.limit x) (limitB : Equiv b.limit y) (bound : Nat)
    (boundedA : ∀ n, QProb.LE (a.value n).magnitude (QProb.ofNat bound))
    (boundedB : ∀ n, QProb.LE (b.value n).magnitude (QProb.ofNat bound)) :
    WithinReal (expQuadraticError x y bound) y.exp (expLinear x y) := by
  let sa := a.toReal
  let sb := b.toReal
  let h := sb.sub sa
  let ea := sa.mapExp
  let eb := sb.mapExp
  let linear := ea.add (h.mul ea)
  let coefficient := ofSignedRatio (⟨RationalTaylorExponential.uniformSumBound bound, 2, by decide⟩ : QProb).toSignedRatio
  let errors := (h.mul h).mul (RealCauchySequence.constant coefficient)
  have finite (n : Nat) : WithinReal (errors.value n) (eb.value n) (linear.value n) := by
    have rational := RationalExponential.first_variation (a.value n) (b.value n) bound (boundedA n) (boundedB n)
    have hEmbed : Equiv (ofSignedRatio (SignedRatio.sub (b.value n) (a.value n))) (h.value n) :=
      equiv_symm (ofSignedRatio_sub _ _)
    have errorEmbed : Equiv
        (ofSignedRatio (QProb.mul (RationalTaylorExponential.quadraticError (a.value n) (b.value n))
          (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound))).toSignedRatio) (errors.value n) :=
      equiv_trans ((ofSignedRatio_equiv_iff _ _).mpr (SignedRatio.quadratic_error_value _ _ bound))
        (equiv_trans (equiv_symm (ofSignedRatio_mul _ _)) (mul_congr
          (equiv_trans (equiv_symm (ofSignedRatio_mul _ _)) (mul_congr hEmbed hEmbed)) (equiv_refl _)))
    have eaEmbed : Equiv (RationalExponential.exp (a.value n)) (ea.value n) := equiv_symm (exp_ofSignedRatio _)
    have ebEmbed : Equiv (RationalExponential.exp (b.value n)) (eb.value n) := equiv_symm (exp_ofSignedRatio _)
    exact (withinReal_congr errorEmbed ebEmbed (add_congr eaEmbed (mul_congr hEmbed eaEmbed))).mp rational
  have aLimit : Equiv sa.limit x := equiv_trans a.toReal_limit limitA
  have bLimit : Equiv sb.limit y := equiv_trans b.toReal_limit limitB
  have hLimit : Equiv h.limit (sub y x) :=
    equiv_trans (sb.sub_limit sa) (add_congr bLimit (neg_congr aLimit))
  have eaLimit : Equiv ea.limit x.exp := equiv_trans sa.mapExp_limit (exp_congr aLimit)
  have ebLimit : Equiv eb.limit y.exp := equiv_trans sb.mapExp_limit (exp_congr bLimit)
  have linearLimit : Equiv linear.limit (expLinear x y) :=
    equiv_trans (ea.add_limit (h.mul ea)) (add_congr eaLimit
      (equiv_trans (h.mul_limit ea) (mul_congr hLimit eaLimit)))
  have errorLimit : Equiv errors.limit (expQuadraticError x y bound) :=
    equiv_trans ((h.mul h).mul_limit (RealCauchySequence.constant coefficient))
      (mul_congr (equiv_trans (h.mul_limit h) (mul_congr hLimit hLimit)) (RealCauchySequence.constant_limit _))
  exact (withinReal_congr errorLimit ebLimit linearLimit).mp (RealCauchySequence.limit_withinReal eb linear errors finite)

/-- Quadratic first variation of the constructed exponential on a bounded
real interval. This transfers the proved rational Taylor remainder through
explicit effective limits; it assumes neither a derivative nor an exponential
addition law. Supplied bounds concern computable rational approximants. -/
theorem exp_first_variation_bounded (x y : ConstructiveReal) (bound : Nat)
    (boundedX : ∀ precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE (x.rationalApproximation.value precision).magnitude (QProb.ofNat bound))
    (boundedY : ∀ precision, PositiveRatio.LE precision PositiveRatio.one →
      QProb.LE (y.rationalApproximation.value precision).magnitude (QProb.ofNat bound)) :
    WithinReal (expQuadraticError x y bound) y.exp (expLinear x y) :=
  first_variation_sequences x.rationalApproximation.sequence y.rationalApproximation.sequence x y
    (equiv_trans x.rationalApproximation.sequence_limit x.rationalApproximation_limit)
    (equiv_trans y.rationalApproximation.sequence_limit y.rationalApproximation_limit) bound
    (fun n => boundedX _ (PositiveRatio.unitPrecision_le_one n))
    (fun n => boundedY _ (PositiveRatio.unitPrecision_le_one n))

end Thesis.Probability.ConstructiveReal
