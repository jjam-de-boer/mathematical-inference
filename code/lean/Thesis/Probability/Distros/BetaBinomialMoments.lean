import Thesis.Probability.Distros.BetaBinomial
import Thesis.Probability.Distros.BinomialMoments

namespace Thesis.Probability.Distros

open Combinatorics

theorem betaBinomialTerm_factorial_second (n a b : Nat) :
    natSum (n + 1) (fun k => k * (k - 1) * betaBinomialTerm n a b k) =
      n * (n - 1) * a * (a + 1) * risingFactorial (a + b + 2) (n - 2) := by
  cases n with
  | zero => simp only [natSum, Nat.zero_mul, Nat.add_zero]
  | succ n =>
      rw [natSum_head]
      have ht : natSum (n + 1) (fun k =>
          (k + 1) * ((k + 1) - 1) * betaBinomialTerm (n + 1) a b (k + 1)) =
          (n + 1) * a * natSum (n + 1) (fun k => k * betaBinomialTerm n (a + 1) b k) := by
        rw [← natSum_mul_left]
        apply natSum_congr
        intro k _
        simp only [Nat.add_sub_cancel]
        calc
          _ = k * ((k + 1) * betaBinomialTerm (n + 1) a b (k + 1)) := by ac_rfl
          _ = _ := by rw [betaBinomialTerm_succ_mul]; ac_rfl
      rw [ht, betaBinomialTerm_first_moment]
      have hexp : n + 1 - 2 = n - 1 := by omega
      have hs : a + 1 + b + 1 = a + b + 2 := by omega
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_sub_cancel, hexp, hs]
      ac_rfl

theorem betaBinomialTerm_second_moment (n a b : Nat) :
    natSum (n + 1) (fun k => k * k * betaBinomialTerm n a b k) =
      n * (n - 1) * a * (a + 1) * risingFactorial (a + b + 2) (n - 2) +
        n * a * risingFactorial (a + b + 1) (n - 1) := by
  have h := natSum_congr (n := n + 1)
    (f := fun k => k * k * betaBinomialTerm n a b k)
    (g := fun k => k * (k - 1) * betaBinomialTerm n a b k + k * betaBinomialTerm n a b k)
    (fun k _ => by
      change k * k * betaBinomialTerm n a b k =
        k * (k - 1) * betaBinomialTerm n a b k + k * betaBinomialTerm n a b k
      rw [← Nat.add_mul, nat_falling_square])
  rw [h, natSum_add, betaBinomialTerm_factorial_second, betaBinomialTerm_first_moment]

theorem betaBinomial_secondMoment (n a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    QProb.Equiv (secondMoment (betaBinomialNatDistro n a b ha hb))
      ⟨n * (n - 1) * a * (a + 1) + n * a * (a + b + 1),
        (a + b) * (a + b + 1), Nat.mul_pos (Nat.add_pos_left ha b) (Nat.succ_pos _)⟩ := by
  have hn : (secondMoment (betaBinomialNatDistro n a b ha hb)).num =
      natSum (n + 1) (fun k => k * k * betaBinomialTerm n a b k) := by
    rw [secondMoment, rawMoment_expectNat]
    change natIntegral (finWeighted (n + 1) (betaBinomialWeight n a b)) (fun k => k.val ^ 2) = _
    rw [natIntegral_finWeighted (n + 1) (betaBinomialWeight n a b) (fun k => k ^ 2)]
    apply natSum_congr
    intro k hk
    simp only [finWeight, dif_pos hk, betaBinomialWeight, betaBinomialTerm, Nat.pow_succ, Nat.pow_zero]
    ac_rfl
  change (secondMoment (betaBinomialNatDistro n a b ha hb)).num * ((a + b) * (a + b + 1)) =
    (n * (n - 1) * a * (a + 1) + n * a * (a + b + 1)) *
      (betaBinomialDistro n a b ha hb).record.den
  rw [hn, betaBinomialTerm_second_moment, betaBinomial_den]
  cases n with
  | zero => simp only [Nat.zero_mul, Nat.zero_add]
  | succ n =>
      cases n with
      | zero =>
          simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.zero_add,
            Nat.mul_one, Nat.one_mul, risingFactorial, Nat.add_zero]
          ac_rfl
      | succ n =>
          have ht : n + 1 + 1 - 2 = n := by omega
          have ho : n + 1 + 1 - 1 = n + 1 := by omega
          have hs : a + b + 1 + 1 = a + b + 2 := by omega
          rw [ht, ho]
          rw [risingFactorial_head, risingFactorial_head, risingFactorial_head, hs]
          simp only [Nat.add_mul, Nat.mul_add]
          ac_rfl

theorem betaBinomial_variance (n a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    QProb.Equiv (variance (betaBinomialNatDistro n a b ha hb))
      ⟨n * a * b * (a + b + n), (a + b) * (a + b) * (a + b + 1),
        Nat.mul_pos (Nat.mul_pos (Nat.add_pos_left ha b) (Nat.add_pos_left ha b)) (Nat.succ_pos _)⟩ := by
  let D := (a + b) * (a + b) * (a + b + 1)
  have hD : 0 < D := Nat.mul_pos
    (Nat.mul_pos (Nat.add_pos_left ha b) (Nat.add_pos_left ha b)) (Nat.succ_pos _)
  have hmean : QProb.Equiv
      (QProb.mul (mean (betaBinomialNatDistro n a b ha hb))
        (mean (betaBinomialNatDistro n a b ha hb)))
      ⟨n * a * (n * a) * (a + b + 1), D, hD⟩ := by
    refine QProb.equiv_trans (QProb.mul_congr (betaBinomial_mean n a b ha hb)
      (betaBinomial_mean n a b ha hb)) ?_
    simp only [QProb.Equiv, QProb.mul, D]
    ac_rfl
  have hnum : n * a * b * (a + b + n) + n * a * (n * a) * (a + b + 1) =
      (n * (n - 1) * a * (a + 1) + n * a * (a + b + 1)) * (a + b) := by
    have hf : n * (n - 1) + n = n * n := nat_falling_square n
    symm
    calc
      _ = (n * (n - 1) + n) * (a * a) * (a + b) + n * a * b * (a + b) +
          (n * (n - 1) + n) * a * (a + b) := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
        ac_rfl
      _ = _ := by
        rw [hf]
        simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
        ac_rfl
  apply variance_eq_of_balance
  refine QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) hmean) ?_
  refine QProb.equiv_trans (QProb.add_mk_same_den D hD
    (n * a * b * (a + b + n)) (n * a * (n * a) * (a + b + 1))) ?_
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (betaBinomial_secondMoment n a b ha hb))
  change (n * a * b * (a + b + n) + n * a * (n * a) * (a + b + 1)) *
    ((a + b) * (a + b + 1)) =
      (n * (n - 1) * a * (a + 1) + n * a * (a + b + 1)) * D
  rw [hnum]
  unfold D
  ac_rfl

end Thesis.Probability.Distros
