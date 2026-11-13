import Thesis.Probability.EntropyValue
import Thesis.Probability.ExactLogLinear

namespace Thesis.Probability

/-- The exact cross-entropy contribution `-p log₂(r)` for positive reference
mass. Zero observed mass is handled by rational scaling, without clipping. -/
def crossEntropyTerm (p r : QProb) (referencePositive : 0 < r.num) : ExactLog :=
  ExactLog.scaleRatio p (ExactLog.log (PositiveRatio.inv ⟨r.num, r.den, referencePositive, r.den_pos⟩))

theorem crossEntropyTerm_congr {p p' r r' : QProb} (observed : QProb.Equiv p p')
    (reference : QProb.Equiv r r') (referencePositive : 0 < r.num) (referencePositive' : 0 < r'.num) :
    ExactLog.Equiv (crossEntropyTerm p r referencePositive) (crossEntropyTerm p' r' referencePositive') := by
  apply ExactLog.scaleRatio_congr observed
  exact (ExactLog.log_equiv_log_iff _ _).mpr (PositiveRatio.inv_congr reference)

/-- KL is cross entropy minus entropy, including at zero observed mass. -/
theorem relativeEntropyTerm_cross_sub (p r : QProb) (referencePositive : 0 < r.num) :
    ExactLog.Equiv (relativeEntropyTerm p r referencePositive)
      (ExactLog.sub (crossEntropyTerm p r referencePositive) (entropyTerm p)) := by
  by_cases positive : 0 < p.num
  · simp only [relativeEntropyTerm, crossEntropyTerm, entropyTerm, positive, ↓reduceDIte]
    rw [← ExactLog.log_mul]
    simp only [ExactLog.log_inv, ExactLog.scaleRatio_neg, ExactLog.sub, ExactLog.neg_neg]
    exact ExactLog.equiv_trans (ExactLog.scaleRatio_add_value p _ _) (ExactLog.add_comm _ _)
  · have zero : p.num = 0 := Nat.eq_zero_of_not_pos positive
    rw [relativeEntropyTerm_zero_num p r referencePositive zero, entropyTerm_zero_num p zero,
      ExactLog.sub, ExactLog.neg_zero, ExactLog.add_zero]
    have observedZero : QProb.Equiv p QProb.zero := by
      simp only [QProb.Equiv, QProb.zero, zero, Nat.zero_mul, Nat.mul_one]
    exact ExactLog.equiv_symm (ExactLog.equiv_trans (ExactLog.scaleRatio_weight_congr observedZero _)
      (ExactLog.scaleRatio_zero_weight _))

end Thesis.Probability
