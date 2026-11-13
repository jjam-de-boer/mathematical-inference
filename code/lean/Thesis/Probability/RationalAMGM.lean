import Thesis.Probability.FiniteAMGM
import Thesis.Probability.PositiveRatio
import Thesis.Probability.Distros.LawEquivalence

namespace Thesis.Probability.RationalAMGM
open Combinatorics

/-- Multiplicative averaging data; multiplicities are natural and may be zero. -/
def weightedProduct : List (PositiveRatio × Nat) → PositiveRatio
  | [] => PositiveRatio.one
  | (value, weight) :: rest => PositiveRatio.mul (value.pow weight) (weightedProduct rest)

def weightedSum : List (PositiveRatio × Nat) → QProb
  | [] => QProb.zero
  | (value, weight) :: rest => QProb.add (QProb.scale weight value.toQProb) (weightedSum rest)

def totalWeight : List (PositiveRatio × Nat) → Nat
  | [] => 0
  | (_, weight) :: rest => weight + totalWeight rest

def clearedItems (items : List (PositiveRatio × Nat)) (coefficient : PositiveRatio → Nat) : List (Nat × Nat) :=
  items.map (fun item => (coefficient item.1, item.2))

theorem cleared_weight (items : List (PositiveRatio × Nat)) (coefficient : PositiveRatio → Nat) :
    weightTotal (clearedItems items coefficient) = totalWeight items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [clearedItems, List.map_cons, weightTotal, totalWeight] at ih ⊢
      rw [ih]

theorem weightedSum_cleared (items : List (PositiveRatio × Nat)) (den : Nat) (positive : 0 < den)
    (coefficient : PositiveRatio → Nat)
    (same : ∀ item ∈ items, QProb.Equiv item.1.toQProb ⟨coefficient item.1, den, positive⟩) :
    QProb.Equiv (weightedSum items) ⟨Combinatorics.weightedSum (clearedItems items coefficient), den, positive⟩ := by
  induction items with
  | nil => exact QProb.equiv_zero_mk den positive
  | cons item rest ih =>
      have tail := ih (fun other member => same other (List.mem_cons_of_mem _ member))
      have head := QProb.scale_congr item.2 (same item (List.mem_cons_self ..))
      exact QProb.equiv_trans (QProb.add_congr head tail)
        (QProb.add_mk_same_den den positive (item.2 * coefficient item.1)
          (Combinatorics.weightedSum (clearedItems rest coefficient)))

theorem weightedProduct_cleared (items : List (PositiveRatio × Nat)) (den : Nat) (positive : 0 < den)
    (coefficient : PositiveRatio → Nat)
    (same : ∀ item ∈ items, QProb.Equiv item.1.toQProb ⟨coefficient item.1, den, positive⟩) :
    QProb.Equiv (weightedProduct items).toQProb
      ⟨FiniteAMGM.weightedProduct (clearedItems items coefficient), den ^ totalWeight items, Nat.pow_pos positive⟩ := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      have tail := ih (fun other member => same other (List.mem_cons_of_mem _ member))
      have head := same item (List.mem_cons_self ..)
      change item.1.num * den = coefficient item.1 * item.1.den at head
      have powered : QProb.Equiv (item.1.pow item.2).toQProb
          ⟨coefficient item.1 ^ item.2, den ^ item.2, Nat.pow_pos positive⟩ := by
        change item.1.num ^ item.2 * den ^ item.2 = coefficient item.1 ^ item.2 * item.1.den ^ item.2
        simpa only [Nat.mul_pow] using congrArg (fun value => value ^ item.2) head
      have multiplied := QProb.mul_congr powered tail
      simpa only [weightedProduct, PositiveRatio.toQProb, PositiveRatio.mul, QProb.mul,
        clearedItems, List.map_cons, FiniteAMGM.weightedProduct, totalWeight, Nat.pow_add] using multiplied

/-- Construct a common denominator from exactly the supplied occurrences.
The proof uses divisibility of a finite product, never a denominator cap. -/
def commonDenominator (items : List (PositiveRatio × Nat)) : Nat :=
  Distros.observableDenominator items PositiveRatio.toQProb

theorem commonDenominator_pos (items : List (PositiveRatio × Nat)) : 0 < commonDenominator items :=
  Distros.observableDenominator_pos items PositiveRatio.toQProb

def clearedNumerator (den : Nat) (value : PositiveRatio) : Nat := value.num * (den / value.den)

theorem commonDenominator_represents (items : List (PositiveRatio × Nat)) (item : PositiveRatio × Nat)
    (member : item ∈ items) :
    QProb.Equiv item.1.toQProb
      ⟨clearedNumerator (commonDenominator items) item.1, commonDenominator items, commonDenominator_pos items⟩ := by
  have divides := Distros.observableDenominator_dvd items PositiveRatio.toQProb item member
  change item.1.den ∣ commonDenominator items at divides
  change item.1.num * commonDenominator items =
    (item.1.num * (commonDenominator items / item.1.den)) * item.1.den
  rw [Nat.mul_assoc, Nat.div_mul_cancel divides]

/-- Weighted rational AM–GM in its Gibbs form. An arithmetic mean at most
one implies a multiplicative mean at most one. Empty and zero-weight families
are included, without any positivity assumption on total multiplicity. -/
theorem weightedProduct_le_one (items : List (PositiveRatio × Nat))
    (bounded : QProb.LE (weightedSum items) (QProb.ofNat (totalWeight items))) :
    PositiveRatio.LE (weightedProduct items) PositiveRatio.one := by
  let den := commonDenominator items
  let nums := clearedNumerator den
  let cleared := clearedItems items nums
  have represented := commonDenominator_represents items
  have sumSame := weightedSum_cleared items den (commonDenominator_pos items) nums represented
  have prodSame := weightedProduct_cleared items den (commonDenominator_pos items) nums represented
  have weights : weightTotal cleared = totalWeight items := cleared_weight items nums
  have arithmetic : Combinatorics.weightedSum cleared ≤ weightTotal cleared * den := by
    have moved := QProb.le_congr sumSame (QProb.equiv_refl _) bounded
    change Combinatorics.weightedSum cleared * 1 ≤ totalWeight items * den at moved
    simpa only [Nat.mul_one, weights] using moved
  have multiplicative : FiniteAMGM.weightedProduct cleared ≤ den ^ totalWeight items := by
    by_cases zero : totalWeight items = 0
    · have estimate := FiniteAMGM.weighted_inequality cleared
      simpa only [weights, zero, Nat.pow_zero, Nat.one_mul] using estimate
    · simpa only [weights] using FiniteAMGM.weighted_product_le_pow cleared den
        (by rw [weights]; exact Nat.pos_of_ne_zero zero) arithmetic
  have clearedBound : QProb.LE
      ⟨FiniteAMGM.weightedProduct cleared, den ^ totalWeight items, Nat.pow_pos (commonDenominator_pos items)⟩
      PositiveRatio.one.toQProb := by
    simpa only [QProb.LE, PositiveRatio.toQProb, PositiveRatio.one, Nat.mul_one, Nat.one_mul] using multiplicative
  exact QProb.le_congr (QProb.equiv_symm prodSame) (QProb.equiv_refl _) clearedBound

theorem totalWeight_map (values : List A) (argument : A → PositiveRatio) (weight : A → Nat) :
    totalWeight (values.map (fun value => (argument value, weight value))) = (values.map weight).sum := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp only [List.map_cons, totalWeight, List.sum_cons, ih]

theorem weightedSum_map (values : List A) (argument : A → PositiveRatio) (weight : A → Nat) :
    weightedSum (values.map (fun value => (argument value, weight value))) =
      QProb.listSum (values.map (fun value => QProb.scale (weight value) (argument value).toQProb)) := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp only [List.map_cons, weightedSum, QProb.listSum, ih]

end Thesis.Probability.RationalAMGM
