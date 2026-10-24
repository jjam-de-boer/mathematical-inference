import Thesis.Probability.ConstructiveDerivativeUniqueness
import Thesis.Probability.ConstructiveRealExpDerivative

namespace Thesis.Examples.ConstructiveDerivative
open Probability ConstructiveReal

/-- The derivative certificate has an effective modulus and quantifies over
all nearby real values, including the point itself. -/
example (x : ConstructiveReal) : HasDerivativeAt exp x x.exp := exp_hasDerivativeAt x
example : HasDerivativeAt exp zero one := (exp_hasDerivativeAt zero).slope_congr exp_zero

example (x : ConstructiveReal) (epsilon radius : PositiveRatio)
    (small : PositiveRatio.LE radius ((exp_hasDerivativeAt x).modulus epsilon)) (y : ConstructiveReal)
    (close : Within radius.toQProb x y) :
    Within (QProb.mul epsilon.toQProb radius.toQProb) y.exp (expLinear x y) :=
  (exp_hasDerivativeAt x).remainder epsilon radius small y close

example (x : ConstructiveReal) (epsilon : PositiveRatio) :
    Within (QProb.mul epsilon.toQProb ((exp_hasDerivativeAt x).modulus epsilon).toQProb)
      x.exp (expLinear x x) :=
  (exp_hasDerivativeAt x).remainder epsilon _ (PositiveRatio.le_refl _) x (within_refl _ x)

example (point value : ConstructiveReal) : HasDerivativeAt (fun _ => value) point zero := HasDerivativeAt.constant point value
example (point : ConstructiveReal) : HasDerivativeAt (fun x => x) point one := HasDerivativeAt.identity point

/-- Empty sums and repeated indices retain their actual finite-sum semantics. -/
example (point : ConstructiveReal) :
    HasDerivativeAt (fun x => listSum [x.exp, x.exp]) point (listSum [point.exp, point.exp]) :=
  HasDerivativeAt.listSum ([0, 0] : List Nat) (fun _ => exp) (fun _ => point.exp) point (fun _ => exp_hasDerivativeAt point)

example (point : ConstructiveReal) : HasDerivativeAt (fun _ => listSum []) point (listSum []) :=
  HasDerivativeAt.listSum ([] : List Nat) (fun _ => exp) (fun _ => point.exp) point (fun _ => exp_hasDerivativeAt point)

/-- A concrete negative increment is accepted by the computed modulus. -/
private def epsilon : PositiveRatio := ⟨1, 10, by decide, by decide⟩
private def radius : PositiveRatio := (exp_hasDerivativeAt zero).modulus epsilon
private def nearby : ConstructiveReal := ofSignedRatio (SignedRatio.neg radius.half.toSignedRatio)
example : Within (QProb.mul epsilon.toQProb radius.toQProb) nearby.exp (expLinear zero nearby) :=
  (exp_hasDerivativeAt zero).remainder epsilon radius (PositiveRatio.le_refl _) nearby
    ((within_ofSignedRatio_iff _ _ _).mpr (by decide +kernel))

/-- Real approximation and error-limit helpers remain audited independently
of the particular exponential derivative proof. -/
example (x : ConstructiveReal) : Equiv x.rationalSequence.limit x := x.rationalSequence_limit
example (sequence : RealCauchySequence) : Equiv sequence.neg.limit (neg sequence.limit) := sequence.neg_limit
example (a b error : RealCauchySequence)
    (bounded : ∀ n, WithinReal (error.value n) (a.value n) (b.value n)) :
    WithinReal error.limit a.limit b.limit := RealCauchySequence.limit_withinReal a b error bounded

/-- Uniqueness excludes a wrong derivative even though the certificate uses
only finite rational error radii. -/
example (bad : HasDerivativeAt (fun x => x) zero zero) : False := by
  have same := (HasDerivativeAt.identity zero).unique bad
  have rational := (ofSignedRatio_equiv_iff SignedRatio.one SignedRatio.zero).mp same
  exact (by decide +kernel : ¬ SignedRatio.Equiv SignedRatio.one SignedRatio.zero) rational

example (x slope : ConstructiveReal) (derivative : HasDerivativeAt exp x slope) : Equiv slope x.exp :=
  derivative.unique (exp_hasDerivativeAt x)

example (x x' : ConstructiveReal) (same : Equiv x x') : HasDerivativeAt exp x' x.exp :=
  (exp_hasDerivativeAt x).point_congr same (exp_congr same)

/-- Composition uses the derivative of the outer function at the actual
image of the inner point. -/
example (f g : ConstructiveReal → ConstructiveReal) (point sf sg : ConstructiveReal)
    (first : HasDerivativeAt f point sf) (second : HasDerivativeAt g (f point) sg) :
    HasDerivativeAt (fun y => g (f y)) point (mul sf sg) := first.chain second

example (point factor offset : ConstructiveReal) :
    HasDerivativeAt (fun y => exp (add (mul y factor) offset)) point
      (mul factor (exp (add (mul point factor) offset))) := exp_affine_hasDerivativeAt point factor offset

/-- Zero factors remain valid and give zero derivative. -/
example (point offset : ConstructiveReal) :
    HasDerivativeAt (fun y => exp (add (mul y zero) offset)) point zero :=
  (exp_affine_hasDerivativeAt point zero offset).slope_congr (zero_mul _)

/-- A negative affine coefficient gives the correct negative derivative. -/
example : HasDerivativeAt (fun y => exp (add (mul y (neg one)) zero)) zero (neg one) := by
  have argument : Equiv (add (mul zero (neg one)) zero) zero :=
    equiv_trans (add_congr (zero_mul _) (equiv_refl _)) (zero_add zero)
  have value := equiv_trans (exp_congr argument) exp_zero
  exact (exp_affine_hasDerivativeAt zero (neg one) zero).slope_congr
    (equiv_trans (mul_congr (equiv_refl _) value) (mul_one _))

end Thesis.Examples.ConstructiveDerivative
