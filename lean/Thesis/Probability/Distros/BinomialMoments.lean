import Thesis.Probability.Distros.Binomial
import Thesis.Probability.Distros.Moments

namespace Thesis.Probability.Distros

open Combinatorics

theorem bernoulli_secondMoment (a b : Nat) (positive : 0 < b + a) :
    secondMoment (bernoulliNatDistro a b positive) = mean (bernoulliNatDistro a b positive) := by
  simp [secondMoment, mean, rawMoment_expectNat, Distro.expectNat,
    bernoulliNatDistro, bernoulliDistro, natIntegral]

theorem bernoulli_variance (a b : Nat) (positive : 0 < b + a) :
    QProb.Equiv (variance (bernoulliNatDistro a b positive))
      ⟨a * b, (b + a) * (b + a), Nat.mul_pos positive positive⟩ := by
  apply variance_eq_of_balance
  refine QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _)
    (QProb.mul_congr (bernoulli_mean a b positive) (bernoulli_mean a b positive))) ?_
  rw [bernoulli_secondMoment]
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (bernoulli_mean a b positive))
  simp only [QProb.Equiv, QProb.add, QProb.mul, Nat.add_mul, Nat.mul_add]
  ac_rfl

theorem binomial_mean_ratio (n a b : Nat) (positive : 0 < b + a) :
    QProb.Equiv (mean (binomialNatDistro n a b positive)) ⟨n * a, b + a, positive⟩ := by
  refine QProb.equiv_trans (binomial_mean n a b positive) ?_
  cases n with
  | zero => simp only [QProb.Equiv, Nat.zero_mul]
  | succ n =>
      simp only [QProb.Equiv, Nat.add_sub_cancel, Nat.pow_succ]
      ac_rfl

theorem nat_falling_square (k : Nat) : k * (k - 1) + k = k * k := by
  cases k with
  | zero => rfl
  | succ k =>
      simp only [Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one, Nat.succ_mul]

theorem binomTerm_factorial_second (n a b : Nat) :
    natSum (n + 1) (fun k => k * (k - 1) * binomTerm n a b k) =
      n * (n - 1) * (a * a) * (a + b) ^ (n - 2) := by
  cases n with
  | zero => simp only [natSum, Nat.zero_mul, Nat.add_zero]
  | succ n =>
      rw [natSum_head]
      have ht : natSum (n + 1) (fun k => (k + 1) * ((k + 1) - 1) * binomTerm (n + 1) a b (k + 1)) =
          (n + 1) * a * natSum (n + 1) (fun k => k * binomTerm n a b k) := by
        rw [← natSum_mul_left]
        apply natSum_congr
        intro k _
        simp only [Nat.add_sub_cancel]
        calc
          _ = k * ((k + 1) * binomTerm (n + 1) a b (k + 1)) := by ac_rfl
          _ = _ := by rw [binomTerm_succ_mul]; ac_rfl
      rw [ht, binomTerm_weighted_sum]
      have hexp : n + 1 - 2 = n - 1 := by omega
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_sub_cancel, hexp]
      ac_rfl

theorem binomTerm_second_moment (n a b : Nat) :
    natSum (n + 1) (fun k => k * k * binomTerm n a b k) =
      n * (n - 1) * (a * a) * (a + b) ^ (n - 2) + n * a * (a + b) ^ (n - 1) := by
  have h := natSum_congr (n := n + 1)
    (f := fun k => k * k * binomTerm n a b k)
    (g := fun k => k * (k - 1) * binomTerm n a b k + k * binomTerm n a b k)
    (fun k _ => by
      change k * k * binomTerm n a b k =
        k * (k - 1) * binomTerm n a b k + k * binomTerm n a b k
      rw [← Nat.add_mul, nat_falling_square])
  rw [h, natSum_add, binomTerm_factorial_second, binomTerm_weighted_sum]

theorem binomial_secondMoment (n a b : Nat) (positive : 0 < b + a) :
    QProb.Equiv (secondMoment (binomialNatDistro n a b positive))
      ⟨n * (n - 1) * (a * a) + n * a * (b + a), (b + a) * (b + a),
        Nat.mul_pos positive positive⟩ := by
  have hn : (secondMoment (binomialNatDistro n a b positive)).num =
      natSum (n + 1) (fun k => k * k * binomTerm n a b k) := by
    rw [secondMoment, rawMoment_expectNat]
    change natIntegral (finWeighted (n + 1) (binomialWeight n a b)) (fun k => k.val ^ 2) = _
    rw [natIntegral_finWeighted (n + 1) (binomialWeight n a b) (fun k => k ^ 2)]
    apply natSum_congr
    intro k hk
    simp only [finWeight, dif_pos hk, binomialWeight, Nat.pow_succ, Nat.pow_zero]
    ac_rfl
  change (secondMoment (binomialNatDistro n a b positive)).num * ((b + a) * (b + a)) =
    (n * (n - 1) * (a * a) + n * a * (b + a)) * (binomialDistro n a b positive).record.den
  rw [hn, binomTerm_second_moment, binomialDistro_den]
  have hd : a + b = b + a := Nat.add_comm _ _
  rw [hd]
  cases n with
  | zero => simp only [Nat.zero_mul, Nat.zero_add]
  | succ n =>
      cases n with
      | zero => simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.zero_add,
          Nat.mul_one, Nat.one_mul, Nat.pow_succ, Nat.pow_zero]; ac_rfl
      | succ n =>
          have ht : n + 1 + 1 - 2 = n := by omega
          have ho : n + 1 + 1 - 1 = n + 1 := by omega
          rw [ht, ho]
          simp only [Nat.pow_succ, Nat.add_mul, Nat.mul_add]
          ac_rfl

theorem binomial_variance (n a b : Nat) (positive : 0 < b + a) :
    QProb.Equiv (variance (binomialNatDistro n a b positive))
      ⟨n * a * b, (b + a) * (b + a), Nat.mul_pos positive positive⟩ := by
  apply variance_eq_of_balance
  refine QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _)
    (QProb.mul_congr (binomial_mean_ratio n a b positive) (binomial_mean_ratio n a b positive))) ?_
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (binomial_secondMoment n a b positive))
  have h : n * (n - 1) + n = n * n := nat_falling_square n
  have hn : n * (n - 1) * (a * a) + n * a * (b + a) = n * a * b + n * a * (n * a) := by
    calc
      _ = n * a * b + (n * (n - 1) + n) * (a * a) := by
        simp only [Nat.mul_add, Nat.add_mul]; ac_rfl
      _ = _ := by rw [h]; ac_rfl
  refine QProb.equiv_trans
    (QProb.add_mk_same_den ((b + a) * (b + a)) (Nat.mul_pos positive positive)
      (n * a * b) (n * a * (n * a))) ?_
  change (n * a * b + n * a * (n * a)) * ((b + a) * (b + a)) =
    (n * (n - 1) * (a * a) + n * a * (b + a)) * ((b + a) * (b + a))
  rw [hn]

end Thesis.Probability.Distros
