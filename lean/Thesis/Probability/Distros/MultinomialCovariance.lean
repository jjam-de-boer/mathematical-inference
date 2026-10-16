import Thesis.Probability.Distros.MultinomialAggregation
import Thesis.Probability.Distros.SignedMoments
namespace Thesis.Probability.Distros
open Combinatorics


def colourIndicator (index colour : Nat) : Nat := if colour = index then 1 else 0

theorem colourCounts_cons_coordinate (length head index : Nat) (word : List Nat) (within : index < length) :
    (colourCounts length (head :: word)).getD index 0 =
      colourIndicator index head + (colourCounts length word).getD index 0 := by
  rw [colourCounts, getD_modify_add _ head index 1 (by simpa only [colourCounts_length] using within)]
  exact Nat.add_comm _ _

theorem categorical_indicator_integral (weights : List Nat) (positive : 0 < weights.sum)
    (index : Nat) (within : index < weights.length) :
    natIntegral (listCategoricalDistro weights positive).record.atoms
      (fun colour => colourIndicator index colour.val) = weights.getD index 0 := by
  have functions : (fun colour : Fin weights.length => colourIndicator index colour.val) =
      (fun colour => if FiniteProbRecord.singletonEvent (⟨index, within⟩ : Fin weights.length) colour then 1 else 0) := by
    funext colour
    simp only [colourIndicator, FiniteProbRecord.singletonEvent]
    by_cases eq : colour.val = index
    · have he : colour = (⟨index, within⟩ : Fin weights.length) := Fin.ext eq
      simp only [he, decide_true, if_true]
    · have he : colour ≠ (⟨index, within⟩ : Fin weights.length) := fun h => eq (congrArg Fin.val h)
      simp only [eq, he, decide_false, Bool.false_eq_true, if_false]
  rw [functions, natIntegral_indicator]
  exact eventMass_finWeighted_singleton _ _ _

theorem categoricalWord_coordinate_integral (weights : List Nat) (positive : 0 < weights.sum)
    (n index : Nat) (within : index < weights.length) :
    natIntegral (categoricalWordDistro weights positive n).record.atoms
      (fun word => (colourCounts weights.length word).getD index 0) * weights.sum =
      n * weights.getD index 0 * weights.sum ^ n := by
  have same := (multinomial_categorical_correspondence n weights positive).expectNat
    (fun counts => counts.getD index 0)
  have mean := multinomial_coordinate_mean n weights positive index within
  rw [mean_expectNat] at mean
  have result := QProb.equiv_trans same mean
  rw [categoricalOccupancyDistro, Distro.expectNat_map] at result
  change _ * weights.sum = n * weights.getD index 0 * (categoricalWordDistro weights positive n).record.den at result
  rw [categoricalWord_den] at result
  exact result

theorem categoricalWord_cross_integral (weights : List Nat) (positive : 0 < weights.sum)
    (n i j : Nat) (hi : i < weights.length) (hj : j < weights.length) (different : i ≠ j) :
    natIntegral (categoricalWordDistro weights positive n).record.atoms
      (fun word => (colourCounts weights.length word).getD i 0 * (colourCounts weights.length word).getD j 0) *
        (weights.sum * weights.sum) = n * (n - 1) * weights.getD i 0 * weights.getD j 0 * weights.sum ^ n := by
  have replicate_zero (index : Nat) (length : Nat) : (List.replicate length 0).getD index 0 = 0 := by
    induction length generalizing index with
    | zero => exact List.getD_nil
    | succ length ih => cases index <;> simp only [List.replicate_succ, List.getD_cons_zero, List.getD_cons_succ, ih]
  induction n with
  | zero => simp only [categoricalWordDistro, Distro.pointMass, natIntegral, colourCounts, replicate_zero,
      Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
      let atoms := (categoricalWordDistro weights positive n).record.atoms
      let left := natIntegral atoms (fun word => (colourCounts weights.length word).getD i 0)
      let right := natIntegral atoms (fun word => (colourCounts weights.length word).getD j 0)
      let cross := natIntegral atoms (fun word =>
        (colourCounts weights.length word).getD i 0 * (colourCounts weights.length word).getD j 0)
      have point (pair : Fin weights.length × List Nat) :
          (colourCounts weights.length (pair.1.val :: pair.2)).getD i 0 *
            (colourCounts weights.length (pair.1.val :: pair.2)).getD j 0 =
          colourIndicator i pair.1.val * (colourCounts weights.length pair.2).getD j 0 +
          colourIndicator j pair.1.val * (colourCounts weights.length pair.2).getD i 0 +
          (colourCounts weights.length pair.2).getD i 0 * (colourCounts weights.length pair.2).getD j 0 := by
        rw [colourCounts_cons_coordinate _ _ i _ hi, colourCounts_cons_coordinate _ _ j _ hj]
        have exclusive : colourIndicator i pair.1.val * colourIndicator j pair.1.val = 0 := by
          simp only [colourIndicator]
          split <;> split <;> simp_all only [Nat.one_mul, Nat.mul_zero, Nat.zero_mul] <;> omega
        simp only [Nat.add_mul, Nat.mul_add]
        rw [exclusive, Nat.zero_add]
        ac_rfl
      have recurrence : natIntegral (categoricalWordDistro weights positive (n + 1)).record.atoms
          (fun word => (colourCounts weights.length word).getD i 0 * (colourCounts weights.length word).getD j 0) =
          weights.getD i 0 * right + weights.getD j 0 * left + weights.sum * cross := by
        change natIntegral
          ((FiniteProbRecord.weightedCartesian (listCategoricalDistro weights positive).record.atoms atoms).map
            (fun source => (source.1.1.val :: source.1.2, source.2))) _ = _
        rw [natIntegral_map _ (fun pair : Fin weights.length × List Nat => pair.1.val :: pair.2)
          (fun word => (colourCounts weights.length word).getD i 0 * (colourCounts weights.length word).getD j 0)]
        rw [natIntegral_congr _ _ _ point, natIntegral_add, natIntegral_add]
        rw [natIntegral_product _ _ (fun colour : Fin weights.length => colourIndicator i colour.val)
            (fun word => (colourCounts weights.length word).getD j 0),
          natIntegral_product _ _ (fun colour : Fin weights.length => colourIndicator j colour.val)
            (fun word => (colourCounts weights.length word).getD i 0),
          natIntegral_product_right _ _ (fun word => (colourCounts weights.length word).getD i 0 *
            (colourCounts weights.length word).getD j 0),
          categorical_indicator_integral weights positive i hi, categorical_indicator_integral weights positive j hj,
          (listCategoricalDistro weights positive).record.total_mass, listCategorical_den]
      have lm : left * weights.sum = n * weights.getD i 0 * weights.sum ^ n :=
        categoricalWord_coordinate_integral weights positive n i hi
      have rm : right * weights.sum = n * weights.getD j 0 * weights.sum ^ n :=
        categoricalWord_coordinate_integral weights positive n j hj
      change cross * (weights.sum * weights.sum) = _ at ih
      rw [recurrence]
      calc
        _ = weights.sum * (cross * (weights.sum * weights.sum)) +
            weights.getD i 0 * weights.sum * (right * weights.sum) +
            weights.getD j 0 * weights.sum * (left * weights.sum) := by
              simp only [Nat.add_mul]; ac_rfl
        _ = (n * (n - 1) + n + n) * weights.getD i 0 * weights.getD j 0 * weights.sum ^ (n + 1) := by
              rw [ih, lm, rm, Nat.pow_succ]
              simp only [Nat.add_mul]; ac_rfl
        _ = _ := by
          have count : n * (n - 1) + n + n = (n + 1) * ((n + 1) - 1) := by
            rw [nat_falling_square]
            simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
          rw [count]

/-- Distinct coordinate cross moments; the covariance below is signed. -/
theorem multinomial_crossMoment (trials : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (i j : Nat) (hi : i < weights.length) (hj : j < weights.length) (different : i ≠ j) :
    QProb.Equiv ((multinomialDistro trials weights positive).expectNat
      (fun counts => counts.getD i 0 * counts.getD j 0))
      ⟨trials * (trials - 1) * weights.getD i 0 * weights.getD j 0, weights.sum * weights.sum,
        Nat.mul_pos positive positive⟩ := by
  refine QProb.equiv_trans (QProb.equiv_symm
    ((multinomial_categorical_correspondence trials weights positive).expectNat _)) ?_
  rw [categoricalOccupancyDistro, Distro.expectNat_map]
  change _ * (weights.sum * weights.sum) = _ * (categoricalWordDistro weights positive trials).record.den
  rw [categoricalWord_den]
  exact categoricalWord_cross_integral weights positive trials i j hi hj different

/-- Off-diagonal covariance is nonpositive, with an integer numerator and
a positive denominator. It is strictly negative when the trial count and
both coordinate weights are positive; otherwise it is zero. -/
theorem multinomial_covariance (trials : Nat) (weights : List Nat) (positive : 0 < weights.sum)
    (i j : Nat) (hi : i < weights.length) (hj : j < weights.length) (different : i ≠ j) :
    SignedMoment.Equiv ((multinomialDistro trials weights positive).covariance
      (fun counts => counts.getD i 0) (fun counts => counts.getD j 0))
      ⟨-((trials * weights.getD i 0 * weights.getD j 0 : Nat) : Int), weights.sum * weights.sum,
        Nat.mul_pos positive positive⟩ := by
  let μ := multinomialDistro trials weights positive
  let D : Int := μ.record.den
  let S : Int := weights.sum
  let A : Int := weights.getD i 0
  let B : Int := weights.getD j 0
  let F : Int := natIntegral μ.record.atoms (fun counts => counts.getD i 0)
  let G : Int := natIntegral μ.record.atoms (fun counts => counts.getD j 0)
  let H : Int := natIntegral μ.record.atoms (fun counts => counts.getD i 0 * counts.getD j 0)
  have fm := multinomial_coordinate_mean trials weights positive i hi
  have gm := multinomial_coordinate_mean trials weights positive j hj
  have hm := multinomial_crossMoment trials weights positive i j hi hj different
  rw [mean_expectNat] at fm gm
  change _ * weights.sum = trials * weights.getD i 0 * μ.record.den at fm
  change _ * weights.sum = trials * weights.getD j 0 * μ.record.den at gm
  change _ * (weights.sum * weights.sum) = trials * (trials - 1) * weights.getD i 0 * weights.getD j 0 * μ.record.den at hm
  have f : F * S = (trials : Int) * A * D := by
    have h := congrArg (fun x : Nat => (x : Int)) fm
    simpa only [Int.natCast_mul] using h
  have g : G * S = (trials : Int) * B * D := by
    have h := congrArg (fun x : Nat => (x : Int)) gm
    simpa only [Int.natCast_mul] using h
  have h : H * (S * S) = ((trials * (trials - 1) : Nat) : Int) * A * B * D := by
    have h := congrArg (fun x : Nat => (x : Int)) hm
    simpa only [Int.natCast_mul] using h
  change (D * H - F * G) * ((weights.sum * weights.sum : Nat) : Int) =
    -((trials * weights.getD i 0 * weights.getD j 0 : Nat) : Int) * ((μ.record.den * μ.record.den : Nat) : Int)
  simp only [Int.natCast_mul]
  change (D * H - F * G) * (S * S) = -((trials : Int) * A * B) * (D * D)
  calc
    _ = D * (H * (S * S)) - (F * S) * (G * S) := by
      rw [Int.sub_mul]
      congr 1 <;> ac_rfl
    _ = (((trials * (trials - 1) : Nat) : Int) - (trials : Int) * (trials : Int)) * A * B * (D * D) := by
      rw [f, g, h]
      rw [Int.sub_mul, Int.sub_mul, Int.sub_mul]
      congr 1 <;> ac_rfl
    _ = _ := by
      have balance := congrArg (fun x : Nat => (x : Int)) (nat_falling_square trials)
      simp only [Int.natCast_add, Int.natCast_mul] at balance
      have count : ((trials * (trials - 1) : Nat) : Int) - (trials : Int) * (trials : Int) = -(trials : Int) := by
        simp only [Int.natCast_mul]; omega
      rw [count]
      simp only [Int.neg_mul]

end Thesis.Probability.Distros
