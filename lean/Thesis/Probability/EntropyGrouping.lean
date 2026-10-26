import Thesis.Probability.EntropyValue
import Thesis.Probability.ExactLogLinear

namespace Thesis.Probability

/-- Entropy of a finite vector of masses. Normalization is a separate
hypothesis; this algebraic helper never changes a distribution record. -/
def entropySum (masses : List QProb) : ExactLog :=
  ExactLog.listSum (masses.map entropyTerm)

/-- The finite chain-rule identity for a product mass, including both zero
cases. No analytic logarithm, derivative or positive lower bound is assumed. -/
theorem entropyTerm_mul (p q : QProb) :
    ExactLog.Equiv (entropyTerm (QProb.mul p q))
      (ExactLog.add (ExactLog.scaleRatio q (entropyTerm p))
        (ExactLog.scaleRatio p (entropyTerm q))) := by
  by_cases hp : 0 < p.num
  · by_cases hq : 0 < q.num
    · have hpq : 0 < (QProb.mul p q).num := Nat.mul_pos hp hq
      let a : PositiveRatio := ⟨p.den, p.num, p.den_pos, hp⟩
      let b : PositiveRatio := ⟨q.den, q.num, q.den_pos, hq⟩
      have product : entropyTerm (QProb.mul p q) =
          ExactLog.scaleRatio (QProb.mul p q) (ExactLog.log (PositiveRatio.mul a b)) := by
        simp only [entropyTerm, hpq, ↓reduceDIte]
        rfl
      rw [product, ← ExactLog.log_mul]
      refine ExactLog.equiv_trans (ExactLog.scaleRatio_add_value _ _ _) ?_
      apply ExactLog.add_congr
      · have commuted := ExactLog.scaleRatio_weight_congr (QProb.mul_comm p q) (ExactLog.log a)
        simpa only [entropyTerm, hp, ↓reduceDIte, ← ExactLog.scaleRatio_mul] using commuted
      · simp only [entropyTerm, hq, ↓reduceDIte, ExactLog.scaleRatio_mul]
        exact ExactLog.equiv_refl _
    · have zero : q.num = 0 := Nat.eq_zero_of_not_pos hq
      have productZero : (QProb.mul p q).num = 0 := by simp only [QProb.mul, zero, Nat.mul_zero]
      rw [entropyTerm_zero_num _ productZero, entropyTerm_zero_num q zero]
      have erased : ExactLog.Equiv (ExactLog.scaleRatio q (entropyTerm p)) ExactLog.zero := by
        have weight : QProb.Equiv q QProb.zero := by simp only [QProb.Equiv, QProb.zero, zero, Nat.zero_mul]
        exact ExactLog.equiv_trans (ExactLog.scaleRatio_weight_congr weight _) (ExactLog.scaleRatio_zero_weight _)
      have expanded := ExactLog.add_congr erased (ExactLog.scaleRatio_zero_value p)
      rw [ExactLog.zero_add] at expanded
      exact ExactLog.equiv_symm expanded
  · have zero : p.num = 0 := Nat.eq_zero_of_not_pos hp
    have productZero : (QProb.mul p q).num = 0 := by simp only [QProb.mul, zero, Nat.zero_mul]
    rw [entropyTerm_zero_num _ productZero, entropyTerm_zero_num p zero]
    have erased : ExactLog.Equiv (ExactLog.scaleRatio p (entropyTerm q)) ExactLog.zero := by
      have weight : QProb.Equiv p QProb.zero := by simp only [QProb.Equiv, QProb.zero, zero, Nat.zero_mul]
      exact ExactLog.equiv_trans (ExactLog.scaleRatio_weight_congr weight _) (ExactLog.scaleRatio_zero_weight _)
    have expanded := ExactLog.add_congr (ExactLog.scaleRatio_zero_value q) erased
    rw [ExactLog.zero_add] at expanded
    exact ExactLog.equiv_symm expanded

theorem entropySum_append (first second : List QProb) :
    entropySum (first ++ second) = ExactLog.add (entropySum first) (entropySum second) := by
  simp only [entropySum, List.map_append, ExactLog.listSum_append]

theorem entropySum_flatMap (values : List A) (family : A → List QProb) :
    entropySum (values.flatMap family) =
      ExactLog.listSum (values.map (fun value => entropySum (family value))) := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.flatMap_cons, entropySum_append, List.map_cons, ExactLog.listSum, ih]

theorem entropySum_perm {first second : List QProb} (same : first.Perm second) :
    ExactLog.Equiv (entropySum first) (entropySum second) :=
  ExactLog.listSum_perm (same.map entropyTerm)

theorem entropySum_map_congr (values : List A) (first second : A → QProb)
    (same : ∀ value ∈ values, QProb.Equiv (first value) (second value)) :
    ExactLog.Equiv (entropySum (values.map first)) (entropySum (values.map second)) := by
  simp only [entropySum, List.map_map]
  exact ExactLog.listSum_map_congr values _ _ (fun value member => entropyTerm_congr (same value member))

theorem entropySum_cons_zero (masses : List QProb) :
    entropySum (QProb.zero :: masses) = entropySum masses := by
  simp only [entropySum, List.map_cons, ExactLog.listSum, entropyTerm_zero_num QProb.zero rfl, ExactLog.zero_add]

/-- Scaling a whole conditional vector separates its internal uncertainty
from the uncertainty of selecting that branch. -/
theorem entropySum_scale (weight : QProb) (masses : List QProb) :
    ExactLog.Equiv (entropySum (masses.map (QProb.mul weight)))
      (ExactLog.add (ExactLog.scaleRatio (QProb.listSum masses) (entropyTerm weight))
        (ExactLog.scaleRatio weight (entropySum masses))) := by
  have terms := ExactLog.listSum_map_congr masses
    (fun q => entropyTerm (QProb.mul weight q))
    (fun q => ExactLog.add (ExactLog.scaleRatio q (entropyTerm weight))
      (ExactLog.scaleRatio weight (entropyTerm q))) (fun q _ => entropyTerm_mul weight q)
  have distributed := ExactLog.listSum_map_add masses
    (fun q => ExactLog.scaleRatio q (entropyTerm weight))
    (fun q => ExactLog.scaleRatio weight (entropyTerm q))
  have right := ExactLog.listSum_scaleRatio (masses.map entropyTerm) weight
  rw [List.map_map] at right
  simpa only [entropySum, List.map_map] using ExactLog.equiv_trans terms
    (ExactLog.equiv_trans distributed (ExactLog.add_congr
      (ExactLog.listSum_scaleRatio_weights masses (entropyTerm weight)) right))

theorem entropySum_scale_normalized (weight : QProb) (masses : List QProb)
    (normalized : QProb.Equiv (QProb.listSum masses) QProb.one) :
    ExactLog.Equiv (entropySum (masses.map (QProb.mul weight)))
      (ExactLog.add (entropyTerm weight) (ExactLog.scaleRatio weight (entropySum masses))) := by
  have normalizedWeight := ExactLog.scaleRatio_weight_congr normalized (entropyTerm weight)
  rw [ExactLog.scaleRatio_one] at normalizedWeight
  exact ExactLog.equiv_trans (entropySum_scale weight masses)
    (ExactLog.add_congr normalizedWeight (ExactLog.equiv_refl _))

/-- Shannon grouping for arbitrary finite normalized conditional vectors.
Outer branch weights may be zero; conditional zero cells are retained. The
outer vector need not be normalized for this algebraic identity. -/
theorem entropySum_grouping (branches : List (QProb × List QProb))
    (normalized : ∀ branch ∈ branches, QProb.Equiv (QProb.listSum branch.2) QProb.one) :
    ExactLog.Equiv (entropySum (branches.flatMap (fun branch => branch.2.map (QProb.mul branch.1))))
      (ExactLog.add (entropySum (branches.map Prod.fst))
        (ExactLog.listSum (branches.map (fun branch => ExactLog.scaleRatio branch.1 (entropySum branch.2))))) := by
  induction branches with
  | nil => exact ExactLog.equiv_refl _
  | cons branch rest ih =>
      have tail := ih (fun value member => normalized value (List.mem_cons_of_mem _ member))
      simp only [List.flatMap_cons, List.map_cons, entropySum_append]
      have head := entropySum_scale_normalized branch.1 branch.2 (normalized branch (List.mem_cons_self ..))
      exact ExactLog.equiv_trans (ExactLog.add_congr head tail) (ExactLog.add_four _ _ _ _)

/-- Independent normalized finite choices have additive entropy. This is a
consequence of grouping, not an axiom used to define the entropy formula. -/
theorem entropySum_product (first second : List QProb)
    (normalizedFirst : QProb.Equiv (QProb.listSum first) QProb.one)
    (normalizedSecond : QProb.Equiv (QProb.listSum second) QProb.one) :
    ExactLog.Equiv (entropySum (first.flatMap (fun p => second.map (QProb.mul p))))
      (ExactLog.add (entropySum first) (entropySum second)) := by
  have grouping := entropySum_grouping (first.map (fun p => (p, second))) (by
    intro branch member
    rcases List.mem_map.mp member with ⟨p, _, rfl⟩
    exact normalizedSecond)
  simp only [List.flatMap_map, List.map_map, Function.comp_def] at grouping
  rw [List.map_id'] at grouping
  have constant := ExactLog.scaleRatio_weight_congr normalizedFirst (entropySum second)
  rw [ExactLog.scaleRatio_one] at constant
  exact ExactLog.equiv_trans grouping (ExactLog.add_congr (ExactLog.equiv_refl _)
    (ExactLog.equiv_trans (ExactLog.listSum_scaleRatio_weights first (entropySum second)) constant))

end Thesis.Probability
