import Thesis.Probability.ExactLogWeights

namespace Thesis.Probability

/-- The exact contribution `-p log₂(p)`, with the conventional value zero
at zero mass. No artificial positive lower bound on probabilities is needed. -/
def entropyTerm (p : QProb) : ExactLog :=
  if positive : 0 < p.num then
    ExactLog.scaleRatio p (ExactLog.log (PositiveRatio.inv ⟨p.num, p.den, positive, p.den_pos⟩))
  else ExactLog.zero

theorem entropyTerm_zero_num (p : QProb) (zero : p.num = 0) : entropyTerm p = ExactLog.zero := by
  simp only [entropyTerm, zero, Nat.lt_irrefl, ↓reduceDIte]

theorem entropyTerm_congr {p q : QProb} (same : QProb.Equiv p q) :
    ExactLog.Equiv (entropyTerm p) (entropyTerm q) := by
  by_cases positive : 0 < p.num
  · have positive' : 0 < q.num := (QProb.equiv_num_pos_iff same).mp positive
    simp only [entropyTerm, positive, positive', ↓reduceDIte]
    apply ExactLog.scaleRatio_congr same
    apply (ExactLog.log_equiv_log_iff _ _).mpr
    exact PositiveRatio.inv_congr same
  · have zero : p.num = 0 := Nat.eq_zero_of_not_pos positive
    have zero' : q.num = 0 := (QProb.equiv_num_zero_iff same).mp zero
    rw [entropyTerm_zero_num p zero, entropyTerm_zero_num q zero']
    exact ExactLog.equiv_refl _

theorem entropyTerm_nonnegative (p : QProb) (bounded : QProb.LE p QProb.one) :
    ExactLog.LE ExactLog.zero (entropyTerm p) := by
  by_cases positive : 0 < p.num
  · simp only [entropyTerm, positive, ↓reduceDIte]
    apply ExactLog.scaleRatio_nonnegative
    change ExactLog.LE (ExactLog.log PositiveRatio.one)
      (ExactLog.log (PositiveRatio.inv ⟨p.num, p.den, positive, p.den_pos⟩))
    apply (ExactLog.log_le_log_iff _ _).mpr
    change 1 * p.num ≤ p.den * 1
    simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using bounded
  · simp only [entropyTerm, positive, ↓reduceDIte]
    exact ExactLog.le_refl _

/-- A KL contribution `p log₂(p/r)` with a strictly positive reference mass.
Zero observed mass contributes zero, including on retained null grid cells. -/
def relativeEntropyTerm (p r : QProb) (referencePositive : 0 < r.num) : ExactLog :=
  if positive : 0 < p.num then
    ExactLog.scaleRatio p (ExactLog.log (PositiveRatio.mul ⟨p.num, p.den, positive, p.den_pos⟩
      (PositiveRatio.inv ⟨r.num, r.den, referencePositive, r.den_pos⟩)))
  else ExactLog.zero

theorem relativeEntropyTerm_zero_num (p r : QProb) (referencePositive : 0 < r.num) (zero : p.num = 0) :
    relativeEntropyTerm p r referencePositive = ExactLog.zero := by
  simp only [relativeEntropyTerm, zero, Nat.lt_irrefl, ↓reduceDIte]

theorem relativeEntropyTerm_congr {p p' r r' : QProb}
    (observed : QProb.Equiv p p') (reference : QProb.Equiv r r')
    (referencePositive : 0 < r.num) (referencePositive' : 0 < r'.num) :
    ExactLog.Equiv (relativeEntropyTerm p r referencePositive) (relativeEntropyTerm p' r' referencePositive') := by
  by_cases positive : 0 < p.num
  · have positive' : 0 < p'.num := (QProb.equiv_num_pos_iff observed).mp positive
    simp only [relativeEntropyTerm, positive, positive', ↓reduceDIte]
    apply ExactLog.scaleRatio_congr observed
    apply (ExactLog.log_equiv_log_iff _ _).mpr
    exact PositiveRatio.mul_congr observed (PositiveRatio.inv_congr reference)
  · have zero : p.num = 0 := Nat.eq_zero_of_not_pos positive
    have zero' : p'.num = 0 := (QProb.equiv_num_zero_iff observed).mp zero
    rw [relativeEntropyTerm_zero_num p r referencePositive zero,
      relativeEntropyTerm_zero_num p' r' referencePositive' zero']
    exact ExactLog.equiv_refl _

theorem relativeEntropyTerm_self (p : QProb) (positive : 0 < p.num) :
    ExactLog.Equiv (relativeEntropyTerm p p positive) ExactLog.zero := by
  simp only [relativeEntropyTerm, positive, ↓reduceDIte]
  have logZero : ExactLog.Equiv
      (ExactLog.log (PositiveRatio.mul ⟨p.num, p.den, positive, p.den_pos⟩
        (PositiveRatio.inv ⟨p.num, p.den, positive, p.den_pos⟩))) ExactLog.zero :=
    (ExactLog.log_equiv_log_iff _ _).mpr (PositiveRatio.mul_inv _)
  exact ExactLog.equiv_trans (ExactLog.scaleRatio_value_congr p logZero) (ExactLog.scaleRatio_zero_value p)

end Thesis.Probability
