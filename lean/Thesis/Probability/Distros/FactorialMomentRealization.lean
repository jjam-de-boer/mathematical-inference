import Thesis.Probability.Distros.FactorialMomentTable
import Thesis.Probability.Distros.PositiveFactorialPGF

namespace Thesis.Probability.Distros
open Combinatorics

private theorem factorialTableCoefficient_zero (moments : Nat → QProb) :
    SignedRatio.Equiv (factorialTableCoefficient moments 0) (moments 0).toSignedRatio := by
  simp only [factorialTableCoefficient, fallingFactorial, QProb.div, QProb.ofNat, Nat.mul_one]
  exact SignedRatio.equiv_refl _

/-- Actual bounded factorial moments satisfy exactly the candidate probability
constraints. Zero cells need no separate positivity assumption. -/
theorem factorialMomentTable_valid_of_moments (μ : NatDistro Ω) (moments : Nat → QProb) (bound : Nat)
    (support : μ.distro.AlmostSurely (fun x => μ.embed x ≤ bound))
    (momentsAgree : ∀ order, order ≤ bound → QProb.Equiv (factorialMoment μ order) (moments order)) :
    FactorialMomentTableValid moments bound := by
  constructor
  · intro value _
    have same := inverseFactorialTable_of_moments μ moments bound value support momentsAgree
    exact (SignedRatio.nonnegative_congr same).mp (QProb.toSignedRatio_nonnegative _)
  · have zeroMoment := inverseFactorialTable_choose moments bound 0 (Nat.zero_le _)
    have terms := SignedRatio.listSum_map_congr (List.range (bound + 1))
      (fun value => SignedRatio.mul (inverseFactorialTable moments bound value) (QProb.ofNat (binom value 0)).toSignedRatio)
      (inverseFactorialTable moments bound)
      (fun value => by simpa only [binom_zero_right, QProb.ofNat, QProb.toSignedRatio] using
        (SignedRatio.mul_one (inverseFactorialTable moments bound value)))
    exact SignedRatio.equiv_trans (SignedRatio.equiv_symm terms)
      (SignedRatio.equiv_trans zeroMoment (SignedRatio.equiv_trans (factorialTableCoefficient_zero moments)
        (QProb.toSignedRatio_congr (QProb.equiv_trans (QProb.equiv_symm (momentsAgree 0 (Nat.zero_le _))) (factorialMoment_zero μ)))))

/-- Nonnegative candidate masses embed as ordinary probability values.
The construction below is exposed only with the full validity certificate. -/
def factorialTableProbability (moments : Nat → QProb) (bound value : Nat) : QProb :=
  ⟨(inverseFactorialTable moments bound value).num.toNat,
    (inverseFactorialTable moments bound value).den, (inverseFactorialTable moments bound value).den_pos⟩

theorem factorialTableProbability_spec (moments : Nat → QProb) (bound value : Nat)
    (positive : SignedRatio.Nonnegative (inverseFactorialTable moments bound value)) :
    SignedRatio.Equiv (factorialTableProbability moments bound value).toSignedRatio
      (inverseFactorialTable moments bound value) := by
  change ((inverseFactorialTable moments bound value).num.toNat : Int) *
      (inverseFactorialTable moments bound value).den =
    (inverseFactorialTable moments bound value).num * (inverseFactorialTable moments bound value).den
  rw [Int.toNat_of_nonneg positive]

private theorem probability_sum_embedding (values : List QProb) :
    (QProb.listSum values).toSignedRatio = SignedRatio.listSum (values.map QProb.toSignedRatio) := by
  induction values with
  | nil => rfl
  | cons value values ih => rw [QProb.listSum, QProb.toSignedRatio_add, List.map_cons, SignedRatio.listSum, ih]

theorem factorialTableProbability_normalized (moments : Nat → QProb) (bound : Nat)
    (valid : FactorialMomentTableValid moments bound) :
    QProb.Equiv (QProb.listSum ((List.range (bound + 1)).map (factorialTableProbability moments bound))) QProb.one := by
  apply (QProb.toSignedRatio_equiv_iff _ _).mp
  rw [probability_sum_embedding, List.map_map]
  refine SignedRatio.equiv_trans (SignedRatio.listSum_map_congr_on_mem (List.range (bound + 1)) _
    (inverseFactorialTable moments bound) ?_) valid.2
  intro value member
  exact factorialTableProbability_spec moments bound value (valid.1 value (by have upper := List.mem_range.mp member; omega))

/-- The canonical realization keeps one natural-weight atom at every cell
0,...,bound, including zero-mass cells. Its numeric embedding is the identity. -/
def realizedFactorialDistro (moments : Nat → QProb) (bound : Nat) (valid : FactorialMomentTableValid moments bound) : NatDistro Nat :=
  ⟨probabilityGrid bound (factorialTableProbability moments bound) (factorialTableProbability_normalized moments bound valid), id⟩

theorem realizedFactorialDistro_bounded (moments : Nat → QProb) (bound : Nat) (valid : FactorialMomentTableValid moments bound) :
    (realizedFactorialDistro moments bound valid).distro.AlmostSurely (fun value => value ≤ bound) :=
  probabilityGrid_bounded bound (factorialTableProbability moments bound) (factorialTableProbability_normalized moments bound valid)

theorem realizedFactorialDistro_pmf (moments : Nat → QProb) (bound : Nat) (valid : FactorialMomentTableValid moments bound)
    (value : Nat) (within : value ≤ bound) :
    SignedRatio.Equiv ((realizedFactorialDistro moments bound valid).distro.pmf value).toSignedRatio
      (inverseFactorialTable moments bound value) :=
  SignedRatio.equiv_trans (QProb.toSignedRatio_congr (probabilityGrid_pmf bound (factorialTableProbability moments bound) (factorialTableProbability_normalized moments bound valid) value within))
    (factorialTableProbability_spec moments bound value (valid.1 value within))

theorem realizedFactorialDistro_retains (moments : Nat → QProb) (bound : Nat) (valid : FactorialMomentTableValid moments bound)
    (value : Nat) (within : value ≤ bound) :
    ∃ weight, (value, weight) ∈ (realizedFactorialDistro moments bound valid).distro.record.atoms :=
  probabilityGrid_retains bound (factorialTableProbability moments bound) (factorialTableProbability_normalized moments bound valid) value within

/-- Each reconstructed binomial moment equals its supplied table coefficient. -/
theorem realizedFactorialDistro_coefficient (moments : Nat → QProb) (bound : Nat) (valid : FactorialMomentTableValid moments bound)
    (order : Nat) (within : order ≤ bound) :
    SignedRatio.Equiv (factorialPGFCoefficient (realizedFactorialDistro moments bound valid) order).toSignedRatio
      (factorialTableCoefficient moments order) := by
  let μ := realizedFactorialDistro moments bound valid
  have integral := μ.distro.rationalExpectation_bounded_pmf bound (realizedFactorialDistro_bounded moments bound valid)
    (fun value => (QProb.ofNat (binom value order)).toSignedRatio)
  have masses := SignedRatio.listSum_map_congr_on_mem (List.range (bound + 1))
    (fun value => SignedRatio.mul (μ.distro.pmf value).toSignedRatio (QProb.ofNat (binom value order)).toSignedRatio)
    (fun value => SignedRatio.mul (inverseFactorialTable moments bound value) (QProb.ofNat (binom value order)).toSignedRatio)
    (fun value member => SignedRatio.mul_congr
      (realizedFactorialDistro_pmf moments bound valid value (by have upper := List.mem_range.mp member; omega))
      (SignedRatio.equiv_refl _))
  exact SignedRatio.equiv_trans (QProb.toSignedRatio_congr (factorialPGFCoefficient_binom μ order))
    (SignedRatio.equiv_trans (SignedRatio.equiv_symm (μ.distro.rationalExpectation_ofNat (fun value => binom value order)))
      (SignedRatio.equiv_trans integral (SignedRatio.equiv_trans masses (inverseFactorialTable_choose moments bound order within))))

/-- The constructed law realizes every supplied factorial moment through the
bound. No law or moments were assumed to exist when the table was supplied. -/
theorem realizedFactorialDistro_moments (moments : Nat → QProb) (bound : Nat) (valid : FactorialMomentTableValid moments bound)
    (order : Nat) (within : order ≤ bound) :
    QProb.Equiv (factorialMoment (realizedFactorialDistro moments bound valid) order) (moments order) := by
  have same := (QProb.toSignedRatio_equiv_iff _ _).mp (realizedFactorialDistro_coefficient moments bound valid order within)
  have positive := fallingFactorial_pos order order (Nat.le_refl _)
  apply Nat.eq_of_mul_eq_mul_right positive
  change (factorialMoment (realizedFactorialDistro moments bound valid) order).num * (moments order).den *
      fallingFactorial order order =
    (moments order).num * (factorialMoment (realizedFactorialDistro moments bound valid) order).den * fallingFactorial order order
  simpa only [factorialPGFCoefficient, factorialTableCoefficient, QProb.Equiv, QProb.div,
    QProb.ofNat, Nat.mul_one, Nat.mul_assoc] using same

/-- Nonnegative normalized inverted masses are necessary and sufficient for
realizability of a bounded rational factorial-moment table. -/
theorem factorialMomentTable_realizable_iff (moments : Nat → QProb) (bound : Nat) :
    FactorialMomentTableValid moments bound ↔ ∃ μ : Distro Nat,
      μ.AlmostSurely (fun value => value ≤ bound) ∧
      ∀ order, order ≤ bound → QProb.Equiv (factorialMoment (⟨μ, id⟩ : NatDistro Nat) order) (moments order) := by
  constructor
  · intro valid
    exact ⟨(realizedFactorialDistro moments bound valid).distro, realizedFactorialDistro_bounded moments bound valid,
      realizedFactorialDistro_moments moments bound valid⟩
  · rintro ⟨μ, support, momentsAgree⟩
    exact factorialMomentTable_valid_of_moments (⟨μ, id⟩ : NatDistro Nat) moments bound support momentsAgree

/-- Every realization has the canonical realization's full event law.
Uniqueness is in law, rather than equality of raw weighted presentations. -/
theorem realizedFactorialDistro_unique (moments : Nat → QProb) (bound : Nat) (valid : FactorialMomentTableValid moments bound)
    (μ : Distro Nat) (support : μ.AlmostSurely (fun value => value ≤ bound))
    (momentsAgree : ∀ order, order ≤ bound → QProb.Equiv (factorialMoment (⟨μ, id⟩ : NatDistro Nat) order) (moments order)) :
    μ.SameLaw (realizedFactorialDistro moments bound valid).distro := by
  have same := NatDistro.sameLaw_of_factorialMoments_positiveSupport (⟨μ, id⟩ : NatDistro Nat)
    (realizedFactorialDistro moments bound valid) bound support (realizedFactorialDistro_bounded moments bound valid)
    (fun order within => QProb.equiv_trans (momentsAgree order within)
      (QProb.equiv_symm (realizedFactorialDistro_moments moments bound valid order within)))
  exact (NatDistro.sameLaw_iff_events _ _).mp same

end Thesis.Probability.Distros
