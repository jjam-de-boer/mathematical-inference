import Thesis.Probability.Distros.Sampling
import Thesis.Probability.Distros.BinomialMoments

namespace Thesis.Probability.Distros

open Combinatorics

/-! Moments of finite sampling without replacement. -/

def hyperIntegral (marked unmarked draws : Nat) (f : Nat → Nat) : Nat :=
  natSum (draws + 1) (fun k => f k * binom marked k * binom unmarked (draws - k))

theorem hyperIntegral_first (marked unmarked draws : Nat) :
    hyperIntegral (marked + 1) unmarked (draws + 1) id =
      (marked + 1) * binom (marked + unmarked) draws := by
  unfold hyperIntegral
  rw [natSum_head]
  have ht : natSum (draws + 1) (fun k =>
      (k + 1) * binom (marked + 1) (k + 1) * binom unmarked (draws + 1 - (k + 1))) =
        (marked + 1) * natSum (draws + 1) (fun k => binom marked k * binom unmarked (draws - k)) := by
    rw [← natSum_mul_left]
    apply natSum_congr
    intro k _
    simp only [Nat.succ_sub_succ, binom_succ_mul, Nat.mul_assoc]
  simp only [id, Nat.zero_mul, Nat.zero_add]
  rw [ht, vandermonde]

theorem hyperIntegral_factorial_second (marked unmarked draws : Nat) :
    hyperIntegral (marked + 2) unmarked (draws + 2) (fun k => k * (k - 1)) =
      (marked + 2) * (marked + 1) * binom (marked + unmarked) draws := by
  unfold hyperIntegral
  rw [natSum_head]
  have ht : natSum (draws + 1 + 1) (fun k =>
      (k + 1) * ((k + 1) - 1) * binom (marked + 1 + 1) (k + 1) *
        binom unmarked (draws + 1 + 1 - (k + 1))) =
      (marked + 2) * hyperIntegral (marked + 1) unmarked (draws + 1) id := by
    unfold hyperIntegral
    rw [← natSum_mul_left]
    apply natSum_congr
    intro k _
    simp only [Nat.succ_sub_succ, Nat.sub_zero, id]
    calc
      _ = k * ((k + 1) * binom (marked + 1 + 1) (k + 1)) * binom unmarked (draws + 1 - k) := by ac_rfl
      _ = _ := by rw [binom_succ_mul]; ac_rfl
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [ht, hyperIntegral_first]
  ac_rfl

theorem hyperIntegral_zero_marked (unmarked draws : Nat) (f : Nat → Nat) (hf : f 0 = 0) :
    hyperIntegral 0 unmarked draws f = 0 := by
  unfold hyperIntegral
  apply Eq.trans (b := natSum (draws + 1) (fun _ => 0)) ?_ (natSum_zero_fun _)
  apply natSum_congr
  intro k _
  cases k with
  | zero => simp only [hf, Nat.zero_mul]
  | succ k =>
      change f (k + 1) * binom 0 (k + 1) * binom unmarked (draws - (k + 1)) = 0
      simp only [binom_zero_succ, Nat.mul_zero, Nat.zero_mul]

theorem hyperIntegral_one_marked_falling (unmarked draws : Nat) :
    hyperIntegral 1 unmarked draws (fun k => k * (k - 1)) = 0 := by
  unfold hyperIntegral
  apply Eq.trans (b := natSum (draws + 1) (fun _ => 0)) ?_ (natSum_zero_fun _)
  apply natSum_congr
  intro k _
  cases k with
  | zero => simp only [Nat.zero_mul]
  | succ k =>
      cases k with
      | zero => simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_mul]
      | succ k =>
          rw [binom_eq_zero_of_lt (show 1 < k + 1 + 1 by omega)]
          simp only [Nat.mul_zero, Nat.zero_mul]

theorem hypergeometric_first_scaled (marked total draws : Nat) (hmarked : marked ≤ total) :
    total * hyperIntegral marked (total - marked) draws id = draws * marked * binom total draws := by
  cases draws with
  | zero => simp only [hyperIntegral, natSum, id, Nat.zero_mul, Nat.add_zero, Nat.mul_zero]
  | succ draws =>
      cases marked with
      | zero => rw [hyperIntegral_zero_marked _ _ id rfl]; simp only [Nat.mul_zero, Nat.zero_mul]
      | succ marked =>
          cases total with
          | zero => omega
          | succ total =>
              have hm : marked ≤ total := Nat.le_of_succ_le_succ hmarked
              rw [Nat.succ_sub_succ, hyperIntegral_first, Nat.add_sub_of_le hm]
              calc
                _ = (marked + 1) * ((total + 1) * binom total draws) := by ac_rfl
                _ = _ := by rw [← binom_succ_mul]; ac_rfl

theorem hypergeometric_factorial_second_scaled (marked total draws : Nat)
    (hmarked : marked ≤ total) :
    total * (total - 1) * hyperIntegral marked (total - marked) draws (fun k => k * (k - 1)) =
      draws * (draws - 1) * marked * (marked - 1) * binom total draws := by
  cases draws with
  | zero => simp only [hyperIntegral, natSum, Nat.zero_mul, Nat.add_zero, Nat.mul_zero]
  | succ draws =>
      cases draws with
      | zero => simp only [hyperIntegral, natSum, Nat.sub_self, Nat.mul_zero, Nat.zero_mul,
          Nat.add_zero, Nat.zero_add]
      | succ draws =>
          cases marked with
          | zero => rw [hyperIntegral_zero_marked _ _ _ (by rfl)]; simp only [Nat.mul_zero, Nat.zero_mul]
          | succ marked =>
              cases marked with
              | zero => rw [hyperIntegral_one_marked_falling]; simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_mul]
              | succ marked =>
                  cases total with
                  | zero => omega
                  | succ total =>
                      cases total with
                      | zero => omega
                      | succ total =>
                          have hm : marked ≤ total := by omega
                          have hu : total + 1 + 1 - (marked + 1 + 1) = total - marked := by omega
                          rw [hu, hyperIntegral_factorial_second, Nat.add_sub_of_le hm]
                          simp only [Nat.add_sub_cancel]
                          have hfirst := binom_succ_mul (total + 1) (draws + 1)
                          have hsecond := binom_succ_mul total draws
                          calc
                            _ = (marked + 2) * (marked + 1) * (total + 2) *
                                ((total + 1) * binom total draws) := by ac_rfl
                            _ = (marked + 2) * (marked + 1) * (draws + 1) *
                                ((total + 2) * binom (total + 1) (draws + 1)) := by rw [← hsecond]; ac_rfl
                            _ = _ := by rw [← hfirst]; ac_rfl

theorem hyperIntegral_second_split (marked unmarked draws : Nat) :
    hyperIntegral marked unmarked draws (fun k => k * k) =
      hyperIntegral marked unmarked draws (fun k => k * (k - 1)) + hyperIntegral marked unmarked draws id := by
  unfold hyperIntegral
  rw [← natSum_add]
  apply natSum_congr
  intro k _
  dsimp only [id]
  rw [← Nat.add_mul, ← Nat.add_mul, nat_falling_square]

theorem hypergeometric_rawMoment_num (marked total draws power : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws) :
    (rawMoment (hypergeometricNatDistro marked total draws hmarked positive) power).num =
      hyperIntegral marked (total - marked) draws (fun k => k ^ power) := by
  rw [rawMoment_expectNat]
  change natIntegral (finWeighted (draws + 1) (hypergeometricWeight marked total draws))
      (fun k => k.val ^ power) = _
  rw [natIntegral_finWeighted (draws + 1) (hypergeometricWeight marked total draws) (fun k => k ^ power)]
  unfold hyperIntegral
  apply natSum_congr
  intro k hk
  simp only [finWeight, dif_pos hk, hypergeometricWeight]
  ac_rfl

theorem hypergeometric_draws_le_total (total draws : Nat) (positive : 0 < binom total draws) :
    draws ≤ total := by
  by_cases h : draws ≤ total
  · exact h
  · have hz : binom total draws = 0 := binom_eq_zero_of_lt (by omega)
    rw [hz] at positive
    omega

theorem hypergeometric_mean (marked total draws : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws) (htotal : 0 < total) :
    QProb.Equiv (mean (hypergeometricNatDistro marked total draws hmarked positive))
      ⟨draws * marked, total, htotal⟩ := by
  have hn := hypergeometric_rawMoment_num marked total draws 1 hmarked positive
  simp only [Nat.pow_one] at hn
  change (rawMoment (hypergeometricNatDistro marked total draws hmarked positive) 1).num * total =
    draws * marked * (hypergeometricDistro marked total draws hmarked positive).record.den
  rw [hn, hypergeometric_den, Nat.mul_comm _ total]
  exact hypergeometric_first_scaled marked total draws hmarked

theorem hypergeometric_secondMoment (marked total draws : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws) (htotal : 1 < total) :
    QProb.Equiv (secondMoment (hypergeometricNatDistro marked total draws hmarked positive))
      ⟨draws * (draws - 1) * marked * (marked - 1) + draws * marked * (total - 1),
        total * (total - 1), Nat.mul_pos (by omega) (by omega)⟩ := by
  have hn := hypergeometric_rawMoment_num marked total draws 2 hmarked positive
  have square (k : Nat) : k ^ 2 = k * k := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  simp only [square] at hn
  rw [hyperIntegral_second_split] at hn
  change (rawMoment (hypergeometricNatDistro marked total draws hmarked positive) 2).num *
      (total * (total - 1)) =
    (draws * (draws - 1) * marked * (marked - 1) + draws * marked * (total - 1)) *
      (hypergeometricDistro marked total draws hmarked positive).record.den
  rw [hn, hypergeometric_den]
  have hf := hypergeometric_factorial_second_scaled marked total draws hmarked
  have hm := congrArg (fun value => value * (total - 1))
    (hypergeometric_first_scaled marked total draws hmarked)
  dsimp only at hm
  calc
    _ = total * (total - 1) * hyperIntegral marked (total - marked) draws (fun k => k * (k - 1)) +
        (total * hyperIntegral marked (total - marked) draws id) * (total - 1) := by
      rw [Nat.add_mul]; ac_rfl
    _ = _ := by rw [hf, hm]; simp only [Nat.add_mul]; ac_rfl

theorem finite_population_balance (marked total draws : Nat)
    (hmarked : marked ≤ total) (hdraws : draws ≤ total) (htotal : 0 < total)
    (hmpositive : 0 < marked) (hdpositive : 0 < draws) :
    (total - marked) * (total - draws) + draws * marked * (total - 1) =
      total * ((draws - 1) * (marked - 1) + (total - 1)) := by
  cases marked with
  | zero => omega
  | succ marked =>
      cases draws with
      | zero => omega
      | succ draws =>
          have hm : total - (marked + 1) + marked = total - 1 := by omega
          have hd : total - (draws + 1) + draws = total - 1 := by omega
          have ht : total = total - 1 + 1 := by omega
          have rectangle : (total - (marked + 1)) * (total - (draws + 1)) +
              (total - 1) * draws + (total - 1) * marked =
                (total - 1) * (total - 1) + marked * draws := by
            calc
              _ = (total - (marked + 1)) * (total - (draws + 1)) +
                  ((total - (marked + 1)) + marked) * draws +
                  ((total - (draws + 1)) + draws) * marked := by rw [hm, hd]
              _ = ((total - (marked + 1)) + marked) *
                  ((total - (draws + 1)) + draws) + marked * draws := by
                simp only [Nat.add_mul, Nat.mul_add]; ac_rfl
              _ = _ := by rw [hm, hd]
          simp only [Nat.add_sub_cancel]
          calc
            _ = ((total - (marked + 1)) * (total - (draws + 1)) +
                (total - 1) * draws + (total - 1) * marked) +
                  draws * marked * (total - 1) + (total - 1) := by
              simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_assoc]; ac_rfl
            _ = (total - 1 + 1) * (draws * marked + (total - 1)) := by
              rw [rectangle]
              simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_assoc]
              rw [Nat.mul_comm draws marked]
              ac_rfl
            _ = _ := by rw [← ht]

theorem hypergeometric_variance (marked total draws : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws) (htotal : 1 < total) :
    QProb.Equiv (variance (hypergeometricNatDistro marked total draws hmarked positive))
      ⟨draws * marked * (total - marked) * (total - draws), total * total * (total - 1),
        Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)⟩ := by
  have hdraws := hypergeometric_draws_le_total total draws positive
  have hp : 0 < total := by omega
  let D := total * total * (total - 1)
  have hD : 0 < D := Nat.mul_pos (Nat.mul_pos hp hp) (by omega)
  have hmean : QProb.Equiv
      (QProb.mul (mean (hypergeometricNatDistro marked total draws hmarked positive))
        (mean (hypergeometricNatDistro marked total draws hmarked positive)))
      ⟨draws * marked * (draws * marked) * (total - 1), D, hD⟩ := by
    refine QProb.equiv_trans (QProb.mul_congr (hypergeometric_mean marked total draws hmarked positive hp)
      (hypergeometric_mean marked total draws hmarked positive hp)) ?_
    simp only [QProb.Equiv, QProb.mul, D]
    ac_rfl
  have hnum : draws * marked * (total - marked) * (total - draws) +
      draws * marked * (draws * marked) * (total - 1) =
        (draws * (draws - 1) * marked * (marked - 1) + draws * marked * (total - 1)) * total := by
    by_cases hm : marked = 0
    · simp only [hm, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
    · by_cases hn : draws = 0
      · simp only [hn, Nat.zero_mul, Nat.zero_add]
      · have hc := finite_population_balance marked total draws hmarked hdraws hp
          (by omega) (by omega)
        calc
          _ = draws * marked * ((total - marked) * (total - draws) + draws * marked * (total - 1)) := by
            simp only [Nat.mul_add]; ac_rfl
          _ = _ := by
            rw [hc]
            simp only [Nat.mul_add, Nat.add_mul]
            ac_rfl
  apply variance_eq_of_balance
  refine QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) hmean) ?_
  refine QProb.equiv_trans (QProb.add_mk_same_den D hD
    (draws * marked * (total - marked) * (total - draws))
    (draws * marked * (draws * marked) * (total - 1))) ?_
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (hypergeometric_secondMoment marked total draws hmarked positive htotal))
  change (draws * marked * (total - marked) * (total - draws) +
      draws * marked * (draws * marked) * (total - 1)) * (total * (total - 1)) =
    (draws * (draws - 1) * marked * (marked - 1) + draws * marked * (total - 1)) * D
  rw [hnum]
  unfold D
  ac_rfl

/-- Empty valid urns have zero draws and the zero count. -/
theorem hypergeometric_empty_moments (marked draws : Nat) (hmarked : marked ≤ 0)
    (positive : 0 < binom 0 draws) :
    QProb.Equiv (mean (hypergeometricNatDistro marked 0 draws hmarked positive)) QProb.zero ∧
      QProb.Equiv (variance (hypergeometricNatDistro marked 0 draws hmarked positive)) QProb.zero := by
  have hm : marked = 0 := by omega
  have hn : draws = 0 := by have h := hypergeometric_draws_le_total 0 draws positive; omega
  subst marked
  subst draws
  exact ⟨by decide +revert, by decide +revert⟩

/-- A one-cell urn has a deterministic count, so its variance is zero. -/
theorem hypergeometric_one_moments (marked draws : Nat) (hmarked : marked ≤ 1)
    (positive : 0 < binom 1 draws) :
    QProb.Equiv (mean (hypergeometricNatDistro marked 1 draws hmarked positive)) (QProb.ofNat (draws * marked)) ∧
      QProb.Equiv (variance (hypergeometricNatDistro marked 1 draws hmarked positive)) QProb.zero := by
  constructor
  · exact hypergeometric_mean marked 1 draws hmarked positive (by decide)
  · have hm : marked = 0 ∨ marked = 1 := by omega
    have hn : draws = 0 ∨ draws = 1 := by
      have h := hypergeometric_draws_le_total 1 draws positive
      omega
    rcases hm with hm | hm <;> rcases hn with hn | hn <;>
      subst marked <;> subst draws <;> decide +revert

end Thesis.Probability.Distros
