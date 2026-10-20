import Thesis.Probability.RationalAMGM
import Thesis.Probability.FiniteAMGMEquality

namespace Thesis.Probability.RationalAMGM
open Combinatorics

/-- Equality in rational Gibbs forces every positively weighted argument to
be one. Zero-weight arguments remain unrestricted. -/
theorem eq_one_of_weightedProduct_equiv_one (items : List (PositiveRatio × Nat))
    (weightPositive : 0 < totalWeight items)
    (bounded : QProb.LE (weightedSum items) (QProb.ofNat (totalWeight items)))
    (equal : PositiveRatio.Equiv (weightedProduct items) PositiveRatio.one) :
    ∀ item ∈ items, 0 < item.2 → PositiveRatio.Equiv item.1 PositiveRatio.one := by
  let den := commonDenominator items
  let nums := clearedNumerator den
  let cleared := clearedItems items nums
  have denPositive : 0 < den := commonDenominator_pos items
  have represented := commonDenominator_represents items
  have sumSame := weightedSum_cleared items den denPositive nums represented
  have prodSame := weightedProduct_cleared items den denPositive nums represented
  have weights : weightTotal cleared = totalWeight items := cleared_weight items nums
  have arithmetic : Combinatorics.weightedSum cleared ≤ weightTotal cleared * den := by
    have moved := QProb.le_congr sumSame (QProb.equiv_refl _) bounded
    change Combinatorics.weightedSum cleared * 1 ≤ totalWeight items * den at moved
    simpa only [Nat.mul_one, weights] using moved
  have productEqual : FiniteAMGM.weightedProduct cleared = den ^ weightTotal cleared := by
    have normalized := QProb.equiv_trans (QProb.equiv_symm prodSame) equal
    simpa only [QProb.Equiv, PositiveRatio.toQProb, PositiveRatio.one, Nat.mul_one, Nat.one_mul, weights] using normalized
  have positive : ∀ item ∈ cleared, 0 < item.1 := by
    intro item member
    rcases List.mem_map.mp member with ⟨original, listed, rfl⟩
    exact (QProb.equiv_num_pos_iff (represented original listed)).mp original.1.num_pos
  have each := FiniteAMGM.eq_den_of_weightedProduct_eq_pow cleared den denPositive
    (by rw [weights]; exact weightPositive) positive arithmetic productEqual
  intro item member weight
  have coordinate := each (nums item.1, item.2) (List.mem_map.mpr ⟨item, member, rfl⟩) weight
  change nums item.1 = den at coordinate
  have relation := represented item member
  change item.1.num * den = nums item.1 * item.1.den at relation
  rw [coordinate] at relation
  have cancelled : item.1.num = item.1.den := by
    apply Nat.eq_of_mul_eq_mul_right denPositive
    calc
      _ = den * item.1.den := relation
      _ = _ := Nat.mul_comm _ _
  simpa only [PositiveRatio.Equiv, QProb.Equiv, PositiveRatio.toQProb, PositiveRatio.one,
    Nat.mul_one, Nat.one_mul] using cancelled

end Thesis.Probability.RationalAMGM
