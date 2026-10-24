import Thesis.Probability.ConstructiveDerivativeAlgebra
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

end Thesis.Examples.ConstructiveDerivative
