import Thesis.Probability.Core
import Thesis.Probability.Distros.Bernoulli

namespace Thesis
namespace Probability
namespace QProb

/-!
# Exact rational switches for an affine probability interval

Given endpoints `base / den` and `(base + gap) / den`, a positive gap permits
the switch probability `(value.num * den - base * value.den) / (value.den * gap)`.
The endpoint inequalities prove this is a probability and that the affine
mixture reconstructs the requested value exactly.  All denominators and
natural subtraction witnesses remain explicit; no real interpolation,
limit, rational rounding, or selection of a parameter is involved.

The finite Bernoulli record reuses the library's existing two-cell distro.
It accepts probability zero or one, retaining zero-weight cells rather than
requiring an artificial strict positivity assumption.  The zero-gap case is
handled separately by equal-endpoint reasoning, never division by zero.
-/

/-- Two opposite rational inequalities imply presentation equivalence by
natural-number antisymmetry, without any propositional decision principle. -/
theorem equiv_of_le_of_le {left right : QProb} (forward : LE left right) (backward : LE right left) :
    Equiv left right := Nat.le_antisymm forward backward

/-- The switch value is computed from literal rational presentations.
Positivity of the gap, not mere nonnegativity, justifies its denominator. -/
def intervalChance (den : Nat) (_denPositive : 0 < den) (base gap : Nat)
    (gapPositive : 0 < gap) (value : QProb) : QProb where
  num := value.num * den - base * value.den
  den := value.den * gap
  den_pos := Nat.mul_pos value.den_pos gapPositive

/-- The upper endpoint bounds the natural subtraction used by the switch.
The lower endpoint is needed later to reconstruct the value, not here to
make the truncated natural numerator nonnegative. -/
theorem intervalChance_le_one (den : Nat) (denPositive : 0 < den) (base gap : Nat)
    (gapPositive : 0 < gap) (value : QProb)
    (upper : LE value ⟨base + gap, den, denPositive⟩) :
    LE (intervalChance den denPositive base gap gapPositive value) one := by
  have cleared : value.num * den ≤ (base + gap) * value.den := upper
  have additive : value.num * den ≤ value.den * gap + base * value.den := by
    calc
      _ ≤ (base + gap) * value.den := cleared
      _ = value.den * gap + base * value.den := by rw [Nat.add_mul]; ac_rfl
  simpa only [LE, intervalChance, one, Nat.mul_one, Nat.one_mul] using
    (Nat.sub_le_of_le_add additive)

/-- Exact affine reconstruction at positive gap.  The lower bound supplies
the nontruncated subtraction identity; fraction equivalence clears positive
denominators without normalizing or changing the requested rational value. -/
theorem intervalChance_reconstruct (den : Nat) (denPositive : 0 < den) (base gap : Nat)
    (gapPositive : 0 < gap) (value : QProb)
    (lower : LE ⟨base, den, denPositive⟩ value) :
    Equiv (add ⟨base, den, denPositive⟩
      (mul ⟨gap, den, denPositive⟩ (intervalChance den denPositive base gap gapPositive value))) value := by
  let needed := value.num * den - base * value.den
  let difference : QProb := ⟨needed, den * value.den, Nat.mul_pos denPositive value.den_pos⟩
  have weighted : Equiv
      (mul ⟨gap, den, denPositive⟩ (intervalChance den denPositive base gap gapPositive value)) difference := by
    change (gap * needed) * (den * value.den) = needed * (den * (value.den * gap))
    ac_rfl
  have clearedLower : base * value.den ≤ value.num * den := lower
  have recovered : base * value.den + needed = value.num * den :=
    Nat.add_sub_of_le clearedLower
  have result : Equiv (add ⟨base, den, denPositive⟩ difference) value := by
    change (base * (den * value.den) + needed * den) * value.den =
      value.num * (den * (den * value.den))
    calc
      _ = (base * value.den + needed) * (den * value.den) := by
        simp only [Nat.add_mul]
        ac_rfl
      _ = (value.num * den) * (den * value.den) := by rw [recovered]
      _ = _ := by ac_rfl
  exact equiv_trans (add_congr (equiv_refl _) weighted) result

/-- A bounded nonnegative rational presentation has a literal finite
Bernoulli record.  The existing distro's two natural weights are retained. -/
def bernoulliRecord (chance : QProb) (bounded : LE chance one) : FiniteProbRecord Bool :=
  let numeratorBound : chance.num ≤ chance.den := by
    simpa only [LE, one, Nat.mul_one, Nat.one_mul] using bounded
  let normalized : chance.den - chance.num + chance.num = chance.den := Nat.sub_add_cancel numeratorBound
  (Distros.bernoulliDistro chance.num (chance.den - chance.num)
    (normalized.symm ▸ chance.den_pos)).record

/-- The record's success probability is exactly the requested fraction,
including its supported-zero and probability-one boundaries. -/
theorem bernoulliRecord_probVal (chance : QProb) (bounded : LE chance one) :
    Equiv ((bernoulliRecord chance bounded).probVal id) chance := by
  have numeratorBound : chance.num ≤ chance.den := by
    simpa only [LE, one, Nat.mul_one, Nat.one_mul] using bounded
  have normalized := Nat.sub_add_cancel numeratorBound
  simp only [bernoulliRecord, Distros.bernoulliDistro, FiniteProbRecord.probVal,
    FiniteProbRecord.eventMass, id_eq, Bool.false_eq_true, if_false, if_true,
    Nat.add_zero, Equiv, normalized]

end QProb
end Probability
end Thesis
