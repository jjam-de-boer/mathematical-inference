import Thesis.Probability.AffineInterval

namespace Thesis
namespace Probability

/-!
# Finite rational mixtures without a common input denominator

Two supplied natural mixing masses specify a probability after normalization
by their positive sum.  The record constructor scales and appends the two
atom lists; it does not form a Cartesian product, expand weights into unit
atoms, or search for a rational denominator.  Repeated labels and zero masses
are retained.  Input records may have unrelated denominators.

The matching rational-value operation is linear in its two endpoints.
Every rational value between two endpoints has explicit natural mixing
masses, including a collapsed interval.  The positive-gap case reuses the
exact affine switch construction; no real interpolation, choice, or decision
about an arbitrary proposition is used.

These are probability-record results.  Mixing arbitrary multi-source causal
models need not preserve source independence.  Causal clients must separately
realize the mixed record in their graph-compatible model class.
-/

namespace QProb

/-- A normalized pair of nonnegative rational values.  Mixing masses are
natural data; their sum, not either individual mass, must be positive. -/
def weightedPair (leftWeight rightWeight : Nat) (positive : 0 < leftWeight + rightWeight)
    (left right : QProb) : QProb where
  num := leftWeight * left.num * right.den + rightWeight * right.num * left.den
  den := (leftWeight + rightWeight) * left.den * right.den
  den_pos := Nat.mul_pos (Nat.mul_pos positive left.den_pos) right.den_pos

theorem weightedPair_eq_sum (leftWeight rightWeight : Nat) (positive : 0 < leftWeight + rightWeight)
    (left right : QProb) :
    Equiv (weightedPair leftWeight rightWeight positive left right)
      (add (mul ⟨leftWeight, leftWeight + rightWeight, positive⟩ left)
        (mul ⟨rightWeight, leftWeight + rightWeight, positive⟩ right)) := by
  simp only [Equiv, weightedPair, add, mul, Nat.add_mul, Nat.mul_add]
  ac_rfl

theorem weightedPair_congr (leftWeight rightWeight : Nat) (positive : 0 < leftWeight + rightWeight)
    {left left' right right' : QProb} (first : Equiv left left') (second : Equiv right right') :
    Equiv (weightedPair leftWeight rightWeight positive left right)
      (weightedPair leftWeight rightWeight positive left' right') :=
  equiv_trans (weightedPair_eq_sum leftWeight rightWeight positive left right)
    (equiv_trans (add_congr (mul_congr (equiv_refl _) first) (mul_congr (equiv_refl _) second))
      (equiv_symm (weightedPair_eq_sum leftWeight rightWeight positive left' right')))

theorem weightedPair_constant (leftWeight rightWeight : Nat) (positive : 0 < leftWeight + rightWeight)
    (value : QProb) : Equiv (weightedPair leftWeight rightWeight positive value value) value := by
  simp only [Equiv, weightedPair, Nat.add_mul, Nat.mul_add]
  ac_rfl

/-- Fixed linear coefficients commute with normalized mixing, including
zero coefficients.  This is useful for whole-law cell constraints. -/
theorem weightedPair_mul_left (leftWeight rightWeight : Nat) (positive : 0 < leftWeight + rightWeight)
    (factor left right : QProb) :
    Equiv (mul factor (weightedPair leftWeight rightWeight positive left right))
      (weightedPair leftWeight rightWeight positive (mul factor left) (mul factor right)) := by
  simp only [Equiv, weightedPair, mul, Nat.add_mul, Nat.mul_add]
  ac_rfl

theorem weightedPair_same_den (leftWeight rightWeight : Nat) (positive : 0 < leftWeight + rightWeight)
    (den : Nat) (denPositive : 0 < den) (left right : Nat) :
    Equiv (weightedPair leftWeight rightWeight positive ⟨left, den, denPositive⟩ ⟨right, den, denPositive⟩)
      ⟨leftWeight * left + rightWeight * right, (leftWeight + rightWeight) * den,
        Nat.mul_pos positive denPositive⟩ := by
  simp only [Equiv, weightedPair, Nat.add_mul, Nat.mul_add]
  ac_rfl

private theorem weightedPair_increment (leftWeight rightWeight : Nat) (positive : 0 < leftWeight + rightWeight)
    (den : Nat) (denPositive : 0 < den) (base gap : Nat) :
    Equiv (weightedPair leftWeight rightWeight positive ⟨base, den, denPositive⟩ ⟨base + gap, den, denPositive⟩)
      (add ⟨base, den, denPositive⟩
        (mul ⟨gap, den, denPositive⟩ ⟨rightWeight, leftWeight + rightWeight, positive⟩)) := by
  simp only [Equiv, weightedPair, add, mul, Nat.add_mul, Nat.mul_add]
  ac_rfl

/-- Explicit rational interpolation, with arbitrary endpoint presentations.
The zero-gap branch uses masses `(1,0)` and never divides by the gap. -/
theorem exists_weightedPair_equiv (lower upper value : QProb)
    (lowerBound : LE lower value) (upperBound : LE value upper) :
    ∃ leftWeight rightWeight, ∃ positive : 0 < leftWeight + rightWeight,
      Equiv (weightedPair leftWeight rightWeight positive lower upper) value := by
  let den := lower.den * upper.den
  have denPositive : 0 < den := Nat.mul_pos lower.den_pos upper.den_pos
  let base := lower.num * upper.den
  let top := upper.num * lower.den
  have lowerPresentation : Equiv (⟨base, den, denPositive⟩ : QProb) lower := by
    change (lower.num * upper.den) * lower.den = lower.num * (lower.den * upper.den)
    ac_rfl
  have upperPresentation : Equiv (⟨top, den, denPositive⟩ : QProb) upper := by
    change (upper.num * lower.den) * upper.den = upper.num * (lower.den * upper.den)
    ac_rfl
  have ordered : base ≤ top := le_trans lowerBound upperBound
  by_cases collapsed : base = top
  · have endpoints : Equiv lower upper := equiv_trans (equiv_symm lowerPresentation)
      (equiv_trans (by rw [collapsed]; exact equiv_refl _) upperPresentation)
    have reverse : LE value lower := le_congr (equiv_refl _) (equiv_symm endpoints) upperBound
    refine ⟨1, 0, by decide, ?_⟩
    have leftOnly : Equiv (weightedPair 1 0 (by decide) lower upper) lower := by
      simp only [Equiv, weightedPair, Nat.one_mul, Nat.zero_mul, Nat.add_zero]
      ac_rfl
    exact equiv_trans leftOnly (equiv_of_le_of_le lowerBound reverse)
  · let gap := top - base
    have gapPositive : 0 < gap := by dsimp [gap]; omega
    have recovered : base + gap = top := Nat.add_sub_of_le ordered
    let chance := intervalChance den denPositive base gap gapPositive value
    have commonLower : LE ⟨base, den, denPositive⟩ value :=
      le_congr (equiv_symm lowerPresentation) (equiv_refl _) lowerBound
    have commonUpper : LE value ⟨base + gap, den, denPositive⟩ := by
      rw [recovered]
      exact le_congr (equiv_refl _) (equiv_symm upperPresentation) upperBound
    have bounded := intervalChance_le_one den denPositive base gap gapPositive value commonUpper
    have numeratorBound : chance.num ≤ chance.den := by
      simpa only [LE, one, Nat.mul_one, Nat.one_mul] using bounded
    have weightsTotal : chance.den - chance.num + chance.num = chance.den := Nat.sub_add_cancel numeratorBound
    have weightsPositive : 0 < chance.den - chance.num + chance.num := weightsTotal.symm ▸ chance.den_pos
    have actualSwitch : Equiv
        (⟨chance.num, chance.den - chance.num + chance.num, weightsPositive⟩ : QProb) chance := by
      change chance.num * chance.den = chance.num * (chance.den - chance.num + chance.num)
      rw [weightsTotal]
    refine ⟨chance.den - chance.num, chance.num, weightsPositive, ?_⟩
    have commonEndpoints : Equiv
        (weightedPair (chance.den - chance.num) chance.num weightsPositive
          ⟨base, den, denPositive⟩ ⟨base + gap, den, denPositive⟩)
        (weightedPair (chance.den - chance.num) chance.num weightsPositive lower upper) := by
      apply weightedPair_congr
      · exact lowerPresentation
      · rw [recovered]; exact upperPresentation
    exact equiv_trans (equiv_symm commonEndpoints)
      (equiv_trans (weightedPair_increment _ _ weightsPositive den denPositive base gap)
        (equiv_trans (add_congr (equiv_refl _) (mul_congr (equiv_refl _) actualSwitch))
          (intervalChance_reconstruct den denPositive base gap gapPositive value commonLower)))

end QProb

namespace FiniteProbRecord

/-- Scale and append two lists.  Their sizes add rather than multiply;
this avoids constructing unused independent copies of both records. -/
def mixture (left right : FiniteProbRecord Ω) (leftWeight rightWeight : Nat)
    (positive : 0 < leftWeight + rightWeight) : FiniteProbRecord Ω where
  atoms := left.atoms.map (fun atom => (atom.1, (leftWeight * right.den) * atom.2)) ++
    right.atoms.map (fun atom => (atom.1, (rightWeight * left.den) * atom.2))
  den := (leftWeight + rightWeight) * left.den * right.den
  den_pos := Nat.mul_pos (Nat.mul_pos positive left.den_pos) right.den_pos
  total_mass := by
    have leftTotal : totalMass (left.atoms.map (fun atom => (atom.1, (leftWeight * right.den) * atom.2))) =
        (leftWeight * right.den) * totalMass left.atoms := totalMass_map_weight left.atoms (fun value => value) _
    have rightTotal : totalMass (right.atoms.map (fun atom => (atom.1, (rightWeight * left.den) * atom.2))) =
        (rightWeight * left.den) * totalMass right.atoms := totalMass_map_weight right.atoms (fun value => value) _
    rw [totalMass_append, leftTotal, rightTotal, left.total_mass, right.total_mass]
    simp only [Nat.add_mul]
    ac_rfl

theorem mixture_eventMass (left right : FiniteProbRecord Ω) (leftWeight rightWeight : Nat)
    (positive : 0 < leftWeight + rightWeight) (event : Event Ω) :
    eventMass (mixture left right leftWeight rightWeight positive).atoms event =
      (leftWeight * right.den) * eventMass left.atoms event +
        (rightWeight * left.den) * eventMass right.atoms event := by
  change eventMass (_ ++ _) event = _
  rw [eventMass_append, eventMass_scale, eventMass_scale]

/-- Every event, not just singleton labels, has exactly its normalized
weighted value.  This is the whole-law linearity used by causal clients. -/
theorem mixture_probVal (left right : FiniteProbRecord Ω) (leftWeight rightWeight : Nat)
    (positive : 0 < leftWeight + rightWeight) (event : Event Ω) :
    QProb.Equiv ((mixture left right leftWeight rightWeight positive).probVal event)
      (QProb.weightedPair leftWeight rightWeight positive (left.probVal event) (right.probVal event)) := by
  change eventMass (mixture left right leftWeight rightWeight positive).atoms event * _ = _
  rw [mixture_eventMass]
  simp only [probVal, mixture, QProb.weightedPair]
  ac_rfl

end FiniteProbRecord
end Probability
end Thesis
