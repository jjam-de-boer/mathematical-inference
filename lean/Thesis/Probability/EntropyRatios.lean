import Thesis.Probability.EntropyValue
import Thesis.Probability.ExactLogRoots
import Thesis.Probability.QProbOrder

namespace Thesis.Probability

/-- The positive likelihood ratio `p/r` at positive observed mass. At zero
observed mass its harmless value one is always given multiplicity zero. -/
def relativeRatio (p r : QProb) (referencePositive : 0 < r.num) : PositiveRatio :=
  if positive : 0 < p.num then
    PositiveRatio.mul ⟨p.num, p.den, positive, p.den_pos⟩
      (PositiveRatio.inv ⟨r.num, r.den, referencePositive, r.den_pos⟩)
  else PositiveRatio.one

theorem relativeEntropyTerm_root (p r : QProb) (referencePositive : 0 < r.num) :
    ExactLog.Equiv (relativeEntropyTerm p r referencePositive)
      (ExactLog.root ((relativeRatio p r referencePositive).pow p.num) p.den p.den_pos) := by
  by_cases positive : 0 < p.num
  · simp only [relativeEntropyTerm, relativeRatio, positive, ↓reduceDIte,
      ExactLog.scaleRatio, ExactLog.log, ExactLog.root, Nat.one_mul]
    exact ExactLog.equiv_refl _
  · have zero : p.num = 0 := Nat.eq_zero_of_not_pos positive
    rw [relativeEntropyTerm_zero_num p r referencePositive zero]
    unfold relativeRatio
    rw [dif_neg positive, zero, PositiveRatio.pow_zero]
    exact ExactLog.equiv_symm (ExactLog.root_one_equiv_zero p.den p.den_pos)

theorem inverse_relativeRatio_scale (p r : QProb) (referencePositive : 0 < r.num) (positive : 0 < p.num) :
    QProb.Equiv (QProb.scale p.num (relativeRatio p r referencePositive).inv.toQProb) (QProb.scale p.den r) := by
  simp only [relativeRatio, positive, ↓reduceDIte, PositiveRatio.inv, PositiveRatio.mul,
    PositiveRatio.toQProb, QProb.scale, QProb.Equiv]
  ac_rfl

/-- The weighted inverse-ratio bound remains valid at zero observed mass;
no missing-support or positivity premise is silently added. -/
theorem inverse_relativeRatio_bound (p r : QProb) (referencePositive : 0 < r.num) :
    QProb.LE (QProb.scale p.num (relativeRatio p r referencePositive).inv.toQProb) (QProb.scale p.den r) := by
  by_cases positive : 0 < p.num
  · exact Nat.le_of_eq (inverse_relativeRatio_scale p r referencePositive positive)
  · have zero : p.num = 0 := Nat.eq_zero_of_not_pos positive
    rw [relativeRatio, dif_neg positive, zero]
    change QProb.LE QProb.zero (QProb.scale p.den r)
    exact QProb.zero_le _

theorem relativeRatio_equiv_one_iff (p r : QProb) (referencePositive : 0 < r.num) (positive : 0 < p.num) :
    PositiveRatio.Equiv (relativeRatio p r referencePositive) PositiveRatio.one ↔ QProb.Equiv p r := by
  simp only [relativeRatio, positive, ↓reduceDIte, PositiveRatio.Equiv, PositiveRatio.toQProb,
    PositiveRatio.mul, PositiveRatio.inv, PositiveRatio.one, QProb.Equiv, Nat.mul_one, Nat.one_mul]
  rw [Nat.mul_comm p.den r.num]

end Thesis.Probability
