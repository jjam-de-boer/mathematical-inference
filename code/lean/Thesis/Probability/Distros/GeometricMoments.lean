import Thesis.Probability.Distros.Sampling
import Thesis.Probability.Distros.BinomialMoments

namespace Thesis.Probability.Distros

open Combinatorics

/-! Closed finite waiting-time moments, with the Bernoulli total retained. -/

def geomIntegral (cap b d : Nat) (f : Nat → Nat) : Nat :=
  natSum (cap + 1) (fun k => f k * b ^ k * d ^ (cap - k))

theorem geomIntegral_add (cap b d : Nat) (f g : Nat → Nat) :
    geomIntegral cap b d (fun k => f k + g k) = geomIntegral cap b d f + geomIntegral cap b d g := by
  simp only [geomIntegral, Nat.add_mul, natSum_add]

theorem geomIntegral_scale (cap b d factor : Nat) (f : Nat → Nat) :
    geomIntegral cap b d (fun k => factor * f k) = factor * geomIntegral cap b d f := by
  simp only [geomIntegral, Nat.mul_assoc, natSum_mul_left]

/-- Finite summation by parts, with both boundary terms retained. -/
theorem geomIntegral_telescope (cap b d : Nat) (f : Nat → Nat) :
    d * geomIntegral cap b d f + f (cap + 1) * b ^ (cap + 1) =
      f 0 * d ^ (cap + 1) + b * geomIntegral cap b d (fun k => f (k + 1)) := by
  let term := fun k => f k * b ^ k * d ^ (cap + 1 - k)
  have upper : natSum (cap + 1) term = d * geomIntegral cap b d f := by
    unfold geomIntegral
    rw [← natSum_mul_left]
    apply natSum_congr
    intro k hk
    have hs : cap + 1 - k = (cap - k) + 1 := by omega
    simp only [term, hs, Nat.pow_succ]
    ac_rfl
  have lower : natSum (cap + 1) (fun k => term (k + 1)) =
      b * geomIntegral cap b d (fun k => f (k + 1)) := by
    unfold geomIntegral
    rw [← natSum_mul_left]
    apply natSum_congr
    intro k _
    simp only [term, Nat.add_sub_add_right, Nat.pow_succ]
    ac_rfl
  calc
    _ = natSum (cap + 1 + 1) term := by
      rw [natSum_succ, upper]
      simp only [term, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    _ = _ := by
      rw [natSum_head, lower]
      simp only [term, Nat.pow_zero, Nat.mul_one, Nat.sub_zero]

theorem geomIntegral_first_balance (cap a b : Nat) :
    a * geomIntegral cap b (a + b) id + (cap + 1) * b ^ (cap + 1) =
      b * geomSumHomog b (a + b) cap := by
  have shift : geomIntegral cap b (a + b) (fun k => k + 1) =
      geomIntegral cap b (a + b) id + geomSumHomog b (a + b) cap := by
    simp only [geomIntegral, Nat.add_mul, Nat.one_mul, natSum_add, geomSumHomog, id]
  have h := geomIntegral_telescope cap b (a + b) id
  simp only [id, Nat.zero_mul, Nat.zero_add] at h
  rw [shift] at h
  simp only [Nat.add_mul, Nat.mul_add] at h ⊢
  omega

theorem geomIntegral_second_balance (cap a b : Nat) :
    a * geomIntegral cap b (a + b) (fun k => k * k) + (cap + 1) * (cap + 1) * b ^ (cap + 1) =
      b * (2 * geomIntegral cap b (a + b) id + geomSumHomog b (a + b) cap) := by
  have square (k : Nat) : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
    have ht : 2 * k = k + k := by omega
    rw [ht]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    ac_rfl
  have shift : geomIntegral cap b (a + b) (fun k => (k + 1) * (k + 1)) =
      geomIntegral cap b (a + b) (fun k => k * k) +
        2 * geomIntegral cap b (a + b) id + geomSumHomog b (a + b) cap := by
    simp only [square, geomIntegral, geomSumHomog, Nat.add_mul, Nat.one_mul,
      natSum_add, Nat.mul_assoc, natSum_mul_left, id]
  have h := geomIntegral_telescope cap b (a + b) (fun k => k * k)
  simp only [Nat.zero_mul, Nat.zero_add] at h
  rw [shift] at h
  simp only [Nat.add_mul, Nat.mul_add] at h ⊢
  omega

theorem geomIntegral_first_closed (cap a b : Nat) :
    a * a * geomIntegral cap b (a + b) id + (b + (cap + 1) * a) * b ^ (cap + 1) =
      b * (a + b) ^ (cap + 1) := by
  calc
    _ = a * (a * geomIntegral cap b (a + b) id + (cap + 1) * b ^ (cap + 1)) +
        b * b ^ (cap + 1) := by simp only [Nat.add_mul, Nat.mul_add]; ac_rfl
    _ = b * (a * geomSumHomog b (a + b) cap + b ^ (cap + 1)) := by
      rw [geomIntegral_first_balance]
      simp only [Nat.mul_add]
      ac_rfl
    _ = _ := by rw [geomSumHomog_bernoulli]

theorem geomIntegral_second_closed (cap a b : Nat) :
    a * a * a * geomIntegral cap b (a + b) (fun k => k * k) +
      (b * (a + b + b) + (cap + 1) * (cap + 1) * (a * a) + 2 * (cap + 1) * a * b) *
        b ^ (cap + 1) = b * (a + b + b) * (a + b) ^ (cap + 1) := by
  have reduced : a * a * geomIntegral cap b (a + b) (fun k => k * k) +
      (a * (cap + 1) * (cap + 1) + 2 * (cap + 1) * b) * b ^ (cap + 1) =
        b * (a + b + b) * geomSumHomog b (a + b) cap := by
    calc
      _ = a * (a * geomIntegral cap b (a + b) (fun k => k * k) +
          (cap + 1) * (cap + 1) * b ^ (cap + 1)) + 2 * b * ((cap + 1) * b ^ (cap + 1)) := by
        simp only [Nat.add_mul, Nat.mul_add]; ac_rfl
      _ = 2 * b * (a * geomIntegral cap b (a + b) id + (cap + 1) * b ^ (cap + 1)) +
          a * b * geomSumHomog b (a + b) cap := by
        rw [geomIntegral_second_balance]
        simp only [Nat.mul_add]; ac_rfl
      _ = _ := by
        rw [geomIntegral_first_balance]
        have ht : 2 * b = b + b := by omega
        rw [ht]
        simp only [Nat.add_mul, Nat.mul_add]
        ac_rfl
  calc
    _ = a * (a * a * geomIntegral cap b (a + b) (fun k => k * k) +
        (a * (cap + 1) * (cap + 1) + 2 * (cap + 1) * b) * b ^ (cap + 1)) +
          b * (a + b + b) * b ^ (cap + 1) := by
      simp only [Nat.add_mul, Nat.mul_add]; ac_rfl
    _ = b * (a + b + b) * (a * geomSumHomog b (a + b) cap + b ^ (cap + 1)) := by
      rw [reduced]
      simp only [Nat.mul_add]; ac_rfl
    _ = _ := by rw [geomSumHomog_bernoulli]

theorem geometric_total_difference (cap a b : Nat) :
    (a + b) ^ (cap + 1) - b ^ (cap + 1) = a * geomSumHomog b (a + b) cap := by
  rw [← geomSumHomog_bernoulli, Nat.add_sub_cancel_right]

theorem geometric_total_difference_pos (cap a b : Nat) (positive : 0 < a) :
    0 < (a + b) ^ (cap + 1) - b ^ (cap + 1) := by
  rw [geometric_total_difference]
  exact Nat.mul_pos positive (geomSumHomog_pos _ _ _ (Nat.add_pos_left positive b))

def geometricMeanClosed (cap a b : Nat) (positive : 0 < a) : QProb :=
  ⟨b * (a + b) ^ (cap + 1) - (b + (cap + 1) * a) * b ^ (cap + 1),
    a * ((a + b) ^ (cap + 1) - b ^ (cap + 1)),
    Nat.mul_pos positive (geometric_total_difference_pos cap a b positive)⟩

def geometricSecondMomentClosed (cap a b : Nat) (positive : 0 < a) : QProb :=
  ⟨b * (a + b + b) * (a + b) ^ (cap + 1) -
      (b * (a + b + b) + (cap + 1) * (cap + 1) * (a * a) + 2 * (cap + 1) * a * b) *
        b ^ (cap + 1),
    a * a * ((a + b) ^ (cap + 1) - b ^ (cap + 1)),
    Nat.mul_pos (Nat.mul_pos positive positive) (geometric_total_difference_pos cap a b positive)⟩

theorem geometric_rawMoment_num (cap a b power : Nat) (positive : 0 < a) :
    (rawMoment (geometricNatDistro cap a b positive) power).num =
      a * geomIntegral cap b (a + b) (fun k => k ^ power) := by
  rw [rawMoment_expectNat]
  change natIntegral (finWeighted (cap + 1) (geometricWeight cap a b)) (fun k => k.val ^ power) = _
  rw [natIntegral_finWeighted (cap + 1) (geometricWeight cap a b) (fun k => k ^ power)]
  unfold geomIntegral
  rw [← natSum_mul_left]
  apply natSum_congr
  intro k hk
  simp only [finWeight, dif_pos hk, geometricWeight]
  ac_rfl

theorem geometric_mean (cap a b : Nat) (positive : 0 < a) :
    QProb.Equiv (mean (geometricNatDistro cap a b positive)) (geometricMeanClosed cap a b positive) := by
  have hn := geometric_rawMoment_num cap a b 1 positive
  simp only [Nat.pow_one] at hn
  have hc : (geometricMeanClosed cap a b positive).num =
      a * a * geomIntegral cap b (a + b) id := by
    change b * (a + b) ^ (cap + 1) - (b + (cap + 1) * a) * b ^ (cap + 1) = _
    rw [← geomIntegral_first_closed, Nat.add_sub_cancel_right]
  change (rawMoment (geometricNatDistro cap a b positive) 1).num *
      (a * ((a + b) ^ (cap + 1) - b ^ (cap + 1))) =
    (geometricMeanClosed cap a b positive).num * (geometricDistro cap a b positive).record.den
  rw [hn, hc, geometric_total_difference, geometric_den]
  ac_rfl

theorem geometric_secondMoment (cap a b : Nat) (positive : 0 < a) :
    QProb.Equiv (secondMoment (geometricNatDistro cap a b positive))
      (geometricSecondMomentClosed cap a b positive) := by
  have hn := geometric_rawMoment_num cap a b 2 positive
  simp only [Nat.pow_succ, Nat.pow_zero] at hn
  have hc : (geometricSecondMomentClosed cap a b positive).num =
      a * a * a * geomIntegral cap b (a + b) (fun k => k * k) := by
    change b * (a + b + b) * (a + b) ^ (cap + 1) -
      (b * (a + b + b) + (cap + 1) * (cap + 1) * (a * a) + 2 * (cap + 1) * a * b) * b ^ (cap + 1) = _
    rw [← geomIntegral_second_closed, Nat.add_sub_cancel_right]
  change (rawMoment (geometricNatDistro cap a b positive) 2).num *
      (a * a * ((a + b) ^ (cap + 1) - b ^ (cap + 1))) =
    (geometricSecondMomentClosed cap a b positive).num * (geometricDistro cap a b positive).record.den
  rw [hn, hc, geometric_total_difference, geometric_den]
  ac_rfl

theorem geometricCensored_rawMoment_num (cap a b power : Nat) (positive : 0 < a) :
    (rawMoment (geometricCensoredNatDistro cap a b positive) power).num =
      a * geomIntegral cap b (a + b) (fun k => k ^ power) + cap ^ power * b ^ (cap + 1) := by
  rw [rawMoment_expectNat]
  change natIntegral (finWeighted (cap + 1) (geometricCensoredWeight cap a b)) (fun k => k.val ^ power) = _
  rw [natIntegral_finWeighted (cap + 1) (geometricCensoredWeight cap a b) (fun k => k ^ power)]
  have ordinary := geometric_rawMoment_num cap a b power positive
  rw [rawMoment_expectNat] at ordinary
  change natIntegral (finWeighted (cap + 1) (geometricWeight cap a b)) (fun k => k.val ^ power) = _ at ordinary
  rw [natIntegral_finWeighted (cap + 1) (geometricWeight cap a b) (fun k => k ^ power)] at ordinary
  rw [← ordinary, natSum_succ, natSum_succ (n := cap)
    (fun k => finWeight (geometricWeight cap a b) k * k ^ power)]
  have hp : natSum cap (fun k => finWeight (geometricCensoredWeight cap a b) k * k ^ power) =
      natSum cap (fun k => finWeight (geometricWeight cap a b) k * k ^ power) := by
    apply natSum_congr
    intro k hk
    simp only [finWeight, dif_pos (Nat.lt_succ_of_lt hk), geometricCensoredWeight, if_pos hk]
  have hl : finWeight (geometricCensoredWeight cap a b) cap =
      finWeight (geometricWeight cap a b) cap + b ^ (cap + 1) := by
    simp only [finWeight, dif_pos (Nat.lt_succ_self cap), geometricCensoredWeight,
      Nat.lt_irrefl, if_false]
  rw [hp, hl, Nat.add_mul]
  ac_rfl

theorem geometricCensored_first_closed (cap a b : Nat) :
    a * (a * geomIntegral cap b (a + b) id + cap * b ^ (cap + 1)) +
      (a + b) * b ^ (cap + 1) = b * (a + b) ^ (cap + 1) := by
  have h := geomIntegral_first_closed cap a b
  calc
    _ = a * a * geomIntegral cap b (a + b) id + (b + (cap + 1) * a) * b ^ (cap + 1) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      ac_rfl
    _ = _ := h

theorem geometricCensored_second_closed (cap a b : Nat) :
    a * a * (a * geomIntegral cap b (a + b) (fun k => k * k) + cap * cap * b ^ (cap + 1)) +
      (a + b) * ((2 * cap + 1) * a + 2 * b) * b ^ (cap + 1) =
        b * (a + b + b) * (a + b) ^ (cap + 1) := by
  have hcoeff : a * a * (cap * cap) + (a + b) * ((2 * cap + 1) * a + 2 * b) =
      b * (a + b + b) + (cap + 1) * (cap + 1) * (a * a) + 2 * (cap + 1) * a * b := by
    have twice (x : Nat) : 2 * x = x + x := by omega
    simp only [twice, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_assoc]
    ac_rfl
  calc
    _ = a * a * a * geomIntegral cap b (a + b) (fun k => k * k) +
        (a * a * (cap * cap) + (a + b) * ((2 * cap + 1) * a + 2 * b)) * b ^ (cap + 1) := by
      simp only [Nat.add_mul, Nat.mul_add]; ac_rfl
    _ = _ := by rw [hcoeff, geomIntegral_second_closed]

def geometricCensoredMeanClosed (cap a b : Nat) (positive : 0 < a) : QProb :=
  ⟨b * (a + b) ^ (cap + 1) - (a + b) * b ^ (cap + 1),
    a * (a + b) ^ (cap + 1), Nat.mul_pos positive (Nat.pow_pos (Nat.add_pos_left positive b))⟩

def geometricCensoredSecondMomentClosed (cap a b : Nat) (positive : 0 < a) : QProb :=
  ⟨b * (a + b + b) * (a + b) ^ (cap + 1) -
      (a + b) * ((2 * cap + 1) * a + 2 * b) * b ^ (cap + 1),
    a * a * (a + b) ^ (cap + 1),
    Nat.mul_pos (Nat.mul_pos positive positive) (Nat.pow_pos (Nat.add_pos_left positive b))⟩

theorem geometricCensored_mean (cap a b : Nat) (positive : 0 < a) :
    QProb.Equiv (mean (geometricCensoredNatDistro cap a b positive))
      (geometricCensoredMeanClosed cap a b positive) := by
  have hn := geometricCensored_rawMoment_num cap a b 1 positive
  simp only [Nat.pow_one] at hn
  have hc : (geometricCensoredMeanClosed cap a b positive).num =
      a * (a * geomIntegral cap b (a + b) id + cap * b ^ (cap + 1)) := by
    change b * (a + b) ^ (cap + 1) - (a + b) * b ^ (cap + 1) = _
    rw [← geometricCensored_first_closed, Nat.add_sub_cancel_right]
  change (rawMoment (geometricCensoredNatDistro cap a b positive) 1).num *
      (a * (a + b) ^ (cap + 1)) =
    (geometricCensoredMeanClosed cap a b positive).num * (geometricCensoredDistro cap a b positive).record.den
  rw [hn, hc, geometricCensored_den]
  ac_rfl

theorem geometricCensored_secondMoment (cap a b : Nat) (positive : 0 < a) :
    QProb.Equiv (secondMoment (geometricCensoredNatDistro cap a b positive))
      (geometricCensoredSecondMomentClosed cap a b positive) := by
  have hn := geometricCensored_rawMoment_num cap a b 2 positive
  have square (k : Nat) : k ^ 2 = k * k := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  simp only [square] at hn
  have hc : (geometricCensoredSecondMomentClosed cap a b positive).num =
      a * a * (a * geomIntegral cap b (a + b) (fun k => k * k) + cap * cap * b ^ (cap + 1)) := by
    change b * (a + b + b) * (a + b) ^ (cap + 1) -
      (a + b) * ((2 * cap + 1) * a + 2 * b) * b ^ (cap + 1) = _
    rw [← geometricCensored_second_closed, Nat.add_sub_cancel_right]
  change (rawMoment (geometricCensoredNatDistro cap a b positive) 2).num *
      (a * a * (a + b) ^ (cap + 1)) =
    (geometricCensoredSecondMomentClosed cap a b positive).num * (geometricCensoredDistro cap a b positive).record.den
  rw [hn, hc, geometricCensored_den]
  ac_rfl

def geometricVarianceClosed (cap a b : Nat) (positive : 0 < a) : QProb :=
  QProb.sub (geometricSecondMomentClosed cap a b positive)
    (QProb.mul (geometricMeanClosed cap a b positive) (geometricMeanClosed cap a b positive))
    (closedMoments_cauchy (geometricNatDistro cap a b positive) _ _
      (geometric_mean cap a b positive) (geometric_secondMoment cap a b positive))

theorem geometric_variance (cap a b : Nat) (positive : 0 < a) :
    QProb.Equiv (variance (geometricNatDistro cap a b positive))
      (geometricVarianceClosed cap a b positive) :=
  variance_closed_moments _ _ _ (geometric_mean cap a b positive) (geometric_secondMoment cap a b positive)

def geometricCensoredVarianceClosed (cap a b : Nat) (positive : 0 < a) : QProb :=
  QProb.sub (geometricCensoredSecondMomentClosed cap a b positive)
    (QProb.mul (geometricCensoredMeanClosed cap a b positive) (geometricCensoredMeanClosed cap a b positive))
    (closedMoments_cauchy (geometricCensoredNatDistro cap a b positive) _ _
      (geometricCensored_mean cap a b positive) (geometricCensored_secondMoment cap a b positive))

theorem geometricCensored_variance (cap a b : Nat) (positive : 0 < a) :
    QProb.Equiv (variance (geometricCensoredNatDistro cap a b positive))
      (geometricCensoredVarianceClosed cap a b positive) :=
  variance_closed_moments _ _ _ (geometricCensored_mean cap a b positive) (geometricCensored_secondMoment cap a b positive)

end Thesis.Probability.Distros
