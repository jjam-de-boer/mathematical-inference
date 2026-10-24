import Thesis.Probability.RationalTaylorVariation
import Thesis.Probability.ConstructiveRealSequenceShift
import Thesis.Probability.ConstructiveRealProductLimits

namespace Thesis.Probability.RationalExponential
open ConstructiveReal

/-- A certified quadratic first-order remainder for the completed exponential
at any two bounded rational arguments. This is derived from finite Taylor
polynomials and effective product/sum limits, without assuming calculus. -/
theorem first_variation (a b : SignedRatio) (bound : Nat)
    (boundedA : QProb.LE a.magnitude (QProb.ofNat bound)) (boundedB : QProb.LE b.magnitude (QProb.ofNat bound)) :
    Within (QProb.mul (RationalTaylorExponential.quadraticError a b) (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound)))
      (exp b) (add (exp a) (mul (ofSignedRatio (SignedRatio.sub b a)) (exp a))) := by
  let first := (sequence b).toReal.shift 1
  let aSeq := (sequence a).toReal
  let increment := RealCauchySequence.constant (ofSignedRatio (SignedRatio.sub b a))
  let second := (aSeq.shift 1).add (increment.mul aSeq)
  have finite (n : Nat) : Within
      (QProb.mul (RationalTaylorExponential.quadraticError a b) (QProb.ofNat (RationalTaylorExponential.uniformSumBound bound)))
      (first.value n) (second.value n) := by
    let pa := RationalGeometricSeries.partialSum (RationalTaylorExponential.term a) (n + 1)
    let pb := RationalGeometricSeries.partialSum (RationalTaylorExponential.term b) (n + 1)
    let linear := SignedRatio.mul (SignedRatio.sub b a) (RationalGeometricSeries.partialSum (RationalTaylorExponential.term a) n)
    have same : SignedRatio.Equiv (RationalTaylorExponential.partialRemainder a b n) (SignedRatio.sub pb (SignedRatio.add pa linear)) :=
      SignedRatio.equiv_trans (SignedRatio.add_assoc _ _ _)
        (SignedRatio.add_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm (SignedRatio.neg_add _ _)))
    have boundError := QProb.le_congr (SignedRatio.magnitude_congr same) (QProb.equiv_refl _)
      (RationalTaylorExponential.partialRemainder_bound a b bound boundedA boundedB n)
    have rational := (within_ofSignedRatio_iff pb (SignedRatio.add pa linear) _).mpr boundError
    have shiftedA : Equiv (ofSignedRatio pa) ((aSeq.shift 1).value n) := by
      change Equiv _ (ofSignedRatio (RationalGeometricSeries.partialSum (RationalTaylorExponential.term a) (1 + n)))
      rw [Nat.add_comm 1]
      exact equiv_refl _
    have embedded : Equiv (ofSignedRatio (SignedRatio.add pa linear)) (second.value n) :=
      equiv_trans (equiv_symm (ofSignedRatio_add _ _))
        (add_congr shiftedA (equiv_symm (ofSignedRatio_mul _ _)))
    have indices : first.value n = ofSignedRatio pb := by
      change ofSignedRatio (RationalGeometricSeries.partialSum (RationalTaylorExponential.term b) (1 + n)) = _
      rw [Nat.add_comm 1]
    rw [indices]
    exact (within_congr (equiv_refl _) embedded).mp rational
  have limits := RealCauchySequence.limit_within_of_tail first second _ 0 (fun n _ => finite n)
  have firstLimit : Equiv first.limit (exp b) := equiv_trans ((sequence b).toReal.shift_limit 1) (sequence b).toReal_limit
  have secondLimit : Equiv second.limit (add (exp a) (mul (ofSignedRatio (SignedRatio.sub b a)) (exp a))) :=
    equiv_trans ((aSeq.shift 1).add_limit (increment.mul aSeq))
      (add_congr (equiv_trans (aSeq.shift_limit 1) (sequence a).toReal_limit)
        (equiv_trans (increment.mul_limit aSeq) (mul_congr (RealCauchySequence.constant_limit _) (sequence a).toReal_limit)))
  exact (within_congr firstLimit secondLimit).mp limits

end Thesis.Probability.RationalExponential
