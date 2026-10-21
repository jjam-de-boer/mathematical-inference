import Thesis.Probability.EntropyTermBounds

namespace Thesis.Probability

/-- Algebraic one-sided entropy increment bounds away from zero. Together
with the proved zero-boundary estimate, these avoid an unbounded derivative
argument in the later uniform continuity proof. -/
theorem entropyTerm_increment_bounds (p q : QProb) (pPositive : 0 < p.num) (qPositive : 0 < q.num)
    (pBounded : QProb.LE p QProb.one) (ordered : QProb.LE q p) :
    ExactLog.LE (entropyTerm p)
      (ExactLog.add (entropyTerm q) (ExactLog.scaleRatio (QProb.sub p q ordered)
        (ExactLog.log ⟨p.den, p.num, p.den_pos, pPositive⟩))) ∧
    ExactLog.LE (entropyTerm q)
      (ExactLog.add (entropyTerm p) (ExactLog.log (PositiveRatio.mul
        ⟨p.num, p.den, pPositive, p.den_pos⟩ (PositiveRatio.inv ⟨q.num, q.den, qPositive, q.den_pos⟩)))) := by
  let P : PositiveRatio := ⟨p.num, p.den, pPositive, p.den_pos⟩
  let Q : PositiveRatio := ⟨q.num, q.den, qPositive, q.den_pos⟩
  let scoreP := ExactLog.log P.inv
  let scoreQ := ExactLog.log Q.inv
  let ratio := ExactLog.log (PositiveRatio.mul P Q.inv)
  have pEntropy : entropyTerm p = ExactLog.scaleRatio p scoreP := by
    simp only [entropyTerm, pPositive, dif_pos]; rfl
  have qEntropy : entropyTerm q = ExactLog.scaleRatio q scoreQ := by
    simp only [entropyTerm, qPositive, dif_pos]; rfl
  have scoreOrder : ExactLog.LE scoreP scoreQ :=
    (ExactLog.log_le_log_iff _ _).mpr ((PositiveRatio.inv_le_inv_iff P Q).mpr ordered)
  have scorePositive : ExactLog.LE ExactLog.zero scoreP := by
    apply (ExactLog.log_le_log_iff PositiveRatio.one _).mpr
    simpa only [PositiveRatio.LE, PositiveRatio.one, PositiveRatio.inv, PositiveRatio.toQProb, QProb.LE,
      Nat.one_mul, Nat.mul_one, P, QProb.one] using pBounded
  have ratioPositive : ExactLog.LE ExactLog.zero ratio := by
    apply (ExactLog.log_le_log_iff PositiveRatio.one _).mpr
    simpa only [PositiveRatio.LE, PositiveRatio.one, PositiveRatio.mul, PositiveRatio.inv, PositiveRatio.toQProb,
      QProb.LE, Nat.one_mul, Nat.mul_one, P, Q, Nat.mul_comm] using ordered
  have recovered := QProb.sub_add p q ordered
  have decomposition := ExactLog.equiv_trans
    (ExactLog.scaleRatio_weight_congr (QProb.equiv_symm recovered) scoreP)
    (ExactLog.scaleRatio_add_weight (QProb.sub p q ordered) q scoreP)
  have firstComparison := (ExactLog.add_le_add_left_iff _ _
    (ExactLog.scaleRatio (QProb.sub p q ordered) scoreP)).mpr (ExactLog.scaleRatio_mono q scoreOrder)
  have firstBound := (ExactLog.le_congr (ExactLog.equiv_symm decomposition) (ExactLog.add_comm _ _)).mp firstComparison
  rw [← pEntropy, ← qEntropy] at firstBound
  have scoreSplit : ExactLog.Equiv scoreQ (ExactLog.add scoreP ratio) := by
    rw [ExactLog.log_mul]
    apply (ExactLog.log_equiv_log_iff _ _).mpr
    simp only [PositiveRatio.Equiv, PositiveRatio.toQProb, QProb.Equiv, PositiveRatio.inv, PositiveRatio.mul, P, Q]
    ac_rfl
  have secondDecomposition := ExactLog.equiv_trans (ExactLog.scaleRatio_value_congr q scoreSplit)
    (ExactLog.scaleRatio_add_value q scoreP ratio)
  have boundedQ : QProb.LE q QProb.one := QProb.le_trans ordered pBounded
  have secondComparison := ExactLog.add_le_add (ExactLog.scaleRatio_weight_mono ordered scoreP scorePositive)
    (ExactLog.scaleRatio_weight_mono boundedQ ratio ratioPositive)
  rw [ExactLog.scaleRatio_one] at secondComparison
  have secondBound := (ExactLog.le_congr (ExactLog.equiv_symm secondDecomposition) (ExactLog.equiv_refl _)).mp secondComparison
  rw [← pEntropy, ← qEntropy] at secondBound
  exact ⟨firstBound, secondBound⟩

end Thesis.Probability
