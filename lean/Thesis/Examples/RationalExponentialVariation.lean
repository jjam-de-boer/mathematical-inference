import Thesis.Probability.RationalExponentialVariation

namespace Thesis.Examples.RationalExponentialVariation
open Probability

/-- The finite algebra checker remains universal in its signed variables. -/
private def x : RationalPolynomial.Expression 2 := .coordinate 0
private def y : RationalPolynomial.Expression 2 := .coordinate 1
private def left : RationalPolynomial.Expression 2 := .mul (.add x y) (.sub x y)
private def right : RationalPolynomial.Expression 2 := .sub (.mul x x) (.mul y y)

example : RationalPolynomial.Expression.equalityCheck left right = true := by decide +kernel
example : RationalPolynomial.Expression.equalityCheck left (.add (.mul x x) (.mul y y)) = false := by decide +kernel
example (values : Fin 2 → SignedRatio) : SignedRatio.Equiv (left.evaluate values) (right.evaluate values) :=
  RationalPolynomial.Expression.equalityCheck_sound left right (by decide +kernel) values

example (a b : SignedRatio) : SignedRatio.Equiv (RationalTaylorExponential.firstRemainder a b 0) SignedRatio.zero :=
  RationalTaylorExponential.firstRemainder_zero a b

example (a b : SignedRatio) (bound count : Nat)
    (boundedA : QProb.LE a.magnitude (QProb.ofNat bound)) (boundedB : QProb.LE b.magnitude (QProb.ofNat bound)) :
    QProb.LE (RationalTaylorExponential.partialRemainder a b count).magnitude
      (QProb.mul (RationalTaylorExponential.quadraticError a b) (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound))) :=
  RationalTaylorExponential.partialRemainder_bound a b bound boundedA boundedB count

/-- The completed-value bound is proved from finite remainders and effective
limits; it is not a premise about an assumed exponential derivative. -/
example (a b : SignedRatio) (bound : Nat)
    (boundedA : QProb.LE a.magnitude (QProb.ofNat bound)) (boundedB : QProb.LE b.magnitude (QProb.ofNat bound)) :
    ConstructiveReal.Within
      (QProb.mul (RationalTaylorExponential.quadraticError a b) (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound)))
      (Probability.RationalExponential.exp b)
      (ConstructiveReal.add (Probability.RationalExponential.exp a)
        (ConstructiveReal.mul (ConstructiveReal.ofSignedRatio (SignedRatio.sub b a)) (Probability.RationalExponential.exp a))) :=
  Probability.RationalExponential.first_variation a b bound boundedA boundedB

example : QProb.Equiv (RationalTaylorExponential.quadraticError ⟨-1, 2, by decide⟩ ⟨-49, 100, by decide⟩) ⟨1, 20000, by decide⟩ := by decide +kernel
example : QProb.Equiv (RationalTaylorExponential.quadraticError ⟨-1, 2, by decide⟩ ⟨-500, 1000, by decide⟩) QProb.zero := by decide +kernel

example (sequence : RealCauchySequence) (offset : Nat) : ConstructiveReal.Equiv (sequence.shift offset).limit sequence.limit :=
  sequence.shift_limit offset

end Thesis.Examples.RationalExponentialVariation
