import Thesis.Probability.ConstructiveRealExpPositive

namespace Thesis.Examples.ConstructiveExpAddition
open Probability ConstructiveReal

example (a b : SignedRatio) (n : Nat) : SignedRatio.Equiv
    (RationalTaylorExponential.term (SignedRatio.add a b) n) (RationalTaylorExponential.convolution a b n) :=
  RationalTaylorExponential.term_add a b n

/-- Opposite signed arguments cancel in the actual finite coefficients. -/
example : SignedRatio.Equiv
    (RationalTaylorExponential.convolution SignedRatio.one (SignedRatio.neg SignedRatio.one) 4) SignedRatio.zero := by decide +kernel

/-- A finite Taylor product can differ from the corresponding triangular
truncation. The nonzero corner must be estimated before taking limits. -/
example : SignedRatio.Equiv
    (RationalDoubleSum.corner (fun i j => SignedRatio.mul (RationalTaylorExponential.term SignedRatio.one i)
      (RationalTaylorExponential.term (SignedRatio.neg SignedRatio.one) j)) 2) (SignedRatio.neg SignedRatio.one) := by decide +kernel

example (coefficient n : Nat) : QProb.LE
    (QProb.scale (n * n) (RationalGeometricSeries.envelope coefficient n))
    (RationalGeometricSeries.envelope (16 * coefficient) (n / 2)) := RationalGeometricSeries.square_envelope_bound coefficient n

example : QProb.LE (QProb.scale (0 * 0) (RationalGeometricSeries.envelope 7 0)) (⟨1, 8, by decide⟩ : QProb) := by decide +kernel

/-- The explicit decay schedule includes a zero domination coefficient. -/
example : QProb.LE (QProb.scale (2 * 2) (RationalGeometricSeries.envelope 0 2)) (⟨1, 8, by decide⟩ : QProb) :=
  RationalGeometricSeries.square_envelope_small 0 ⟨1, 8, by decide, by decide⟩ 2 (by decide +kernel)

example (x y : ConstructiveReal) : Equiv (exp (add x y)) (mul x.exp y.exp) := exp_add x y
example (x : ConstructiveReal) : Equiv (mul x.exp (neg x).exp) one := exp_mul_exp_neg x
example (x : ConstructiveReal) : LE zero x.exp := exp_nonnegative x
example (x : ConstructiveReal) : LE (ofSignedRatio x.expLower.toSignedRatio) x.exp := exp_lower x

/-- Every exponential has the supplied positive inverse, with no extra
positivity assumption left to the caller. -/
example (x : ConstructiveReal) : Equiv (x.exp.positiveInverse x.expLower x.exp_lower) (neg x).exp := exp_positiveInverse x

/-- A zero value contradicts the proved product-one identity. -/
example (x : ConstructiveReal) (vanished : Equiv x.exp zero) : False := by
  have impossible : Equiv one zero :=
    equiv_trans (equiv_symm (exp_mul_exp_neg x))
      (equiv_trans (mul_congr vanished (equiv_refl (neg x).exp)) (zero_mul (neg x).exp))
  exact (by decide +kernel : ¬ SignedRatio.Equiv SignedRatio.one SignedRatio.zero) ((ofSignedRatio_equiv_iff _ _).mp impossible)

example (x : ConstructiveReal) (n : Nat) : Equiv (exp (scaleNat n x)) (pow x.exp n) := exp_scaleNat x n
example (x y : ConstructiveReal) : Equiv (exp (sub x y)) (mul x.exp (y.exp.positiveInverse y.expLower y.exp_lower)) := exp_sub x y

end Thesis.Examples.ConstructiveExpAddition
