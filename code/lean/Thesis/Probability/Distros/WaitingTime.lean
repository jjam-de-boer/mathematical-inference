import Thesis.Probability.Distros.Sampling
import Thesis.Probability.Distros.LimitAnalogs

namespace Thesis
namespace Probability
namespace Distros

/-!
Consistency bridges for finite Bernoulli waiting-time laws.  All generating
functions retain the original trial total when the failure weight is
multiplied by the generating argument.
-/

open Combinatorics

/-- The common trial denominator gives exactly the Bernoulli probability
of `k` failures followed by success, before conditioning on the window. -/
theorem geometricWeight_trials (cap a b : Nat) (ha : 0 < a)
    (k : Fin (cap + 1)) :
    QProb.Equiv
      ⟨geometricWeight cap a b k, (a + b) ^ (cap + 1),
        Nat.pow_pos (Nat.add_pos_left ha _)⟩
      (QProb.mul ⟨a, a + b, Nat.add_pos_left ha _⟩
        (qpow ⟨b, a + b, Nat.add_pos_left ha _⟩ k.val)) := by
  have hk : k.val ≤ cap := Nat.le_of_lt_succ k.isLt
  have hsplit : (a + b) ^ (cap + 1) =
      (a + b) ^ (cap - k.val) * (a + b) ^ (k.val + 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  simp only [QProb.Equiv, QProb.mul, qpow_num, qpow_den, geometricWeight]
  rw [hsplit, Nat.pow_succ]
  ac_rfl

theorem geometricWeight_bernoulli (cap a b : Nat) (ha : 0 < a)
    (k : Fin (cap + 1)) :
    QProb.Equiv
      ⟨geometricWeight cap a b k, (a + b) ^ (cap + 1),
        Nat.pow_pos (Nat.add_pos_left ha _)⟩
      (QProb.mul
        ((bernoulliDistro a b (Nat.add_pos_right b ha)).pmf true)
        (qpow ((bernoulliDistro a b (Nat.add_pos_right b ha)).pmf false) k.val)) := by
  have ht : QProb.Equiv
      ((bernoulliDistro a b (Nat.add_pos_right b ha)).pmf true)
      ⟨a, a + b, Nat.add_pos_left ha _⟩ :=
    QProb.equiv_trans (bernoulli_pmf_true a b _) (by simp [QProb.Equiv, Nat.add_comm])
  have hf : QProb.Equiv
      ((bernoulliDistro a b (Nat.add_pos_right b ha)).pmf false)
      ⟨b, a + b, Nat.add_pos_left ha _⟩ :=
    QProb.equiv_trans (bernoulli_pmf_false a b _) (by simp [QProb.Equiv, Nat.add_comm])
  exact QProb.equiv_trans (geometricWeight_trials cap a b ha k)
    (QProb.equiv_symm (QProb.mul_congr ht (qpow_congr hf k.val)))

/-- Every stopped occupancy term has its correct Bernoulli trial mass on
the common horizon, including the suffix that is no longer inspected. -/
theorem negativeBinomialWeight_trials (r cap a b : Nat) (ha : 0 < a)
    (k : Fin (cap + 1)) :
    QProb.Equiv
      ⟨negativeBinomialWeight r cap a b k, (a + b) ^ (cap + r),
        Nat.pow_pos (Nat.add_pos_left ha _)⟩
      (QProb.scale (binom (k.val + r - 1) k.val)
        (QProb.mul (qpow ⟨a, a + b, Nat.add_pos_left ha _⟩ r)
          (qpow ⟨b, a + b, Nat.add_pos_left ha _⟩ k.val))) := by
  have hk : k.val ≤ cap := Nat.le_of_lt_succ k.isLt
  have hsplit : (a + b) ^ (cap + r) =
      (a + b) ^ (cap - k.val) * ((a + b) ^ r * (a + b) ^ k.val) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  simp only [QProb.Equiv, QProb.scale, QProb.mul, qpow_num, qpow_den,
    negativeBinomialWeight]
  rw [hsplit]
  ac_rfl

theorem negativeBinomialWeight_bernoulli (r cap a b : Nat) (ha : 0 < a)
    (k : Fin (cap + 1)) :
    QProb.Equiv
      ⟨negativeBinomialWeight r cap a b k, (a + b) ^ (cap + r),
        Nat.pow_pos (Nat.add_pos_left ha _)⟩
      (QProb.scale (binom (k.val + r - 1) k.val)
        (QProb.mul
          (qpow ((bernoulliDistro a b (Nat.add_pos_right b ha)).pmf true) r)
          (qpow ((bernoulliDistro a b (Nat.add_pos_right b ha)).pmf false) k.val))) := by
  have ht : QProb.Equiv
      ((bernoulliDistro a b (Nat.add_pos_right b ha)).pmf true)
      ⟨a, a + b, Nat.add_pos_left ha _⟩ :=
    QProb.equiv_trans (bernoulli_pmf_true a b _) (by simp [QProb.Equiv, Nat.add_comm])
  have hf : QProb.Equiv
      ((bernoulliDistro a b (Nat.add_pos_right b ha)).pmf false)
      ⟨b, a + b, Nat.add_pos_left ha _⟩ :=
    QProb.equiv_trans (bernoulli_pmf_false a b _) (by simp [QProb.Equiv, Nat.add_comm])
  exact QProb.equiv_trans (negativeBinomialWeight_trials r cap a b ha k)
    (QProb.equiv_symm
      (QProb.scale_congr _ (QProb.mul_congr (qpow_congr ht r) (qpow_congr hf k.val))))

theorem negativeBinomialWeight_one (cap a b : Nat) :
    negativeBinomialWeight 1 cap a b = geometricWeight cap a b := by
  funext k
  simp [negativeBinomialWeight, geometricWeight, binom_self]

theorem negativeBinomialCensorTail_one (cap a b : Nat) :
    negativeBinomialCensorTail 1 cap a b = b ^ (cap + 1) := by
  simp [negativeBinomialCensorTail, natSum, binom_zero_right]

theorem negativeBinomialCensoredWeight_one (cap a b : Nat) :
    negativeBinomialCensoredWeight 1 cap a b = geometricCensoredWeight cap a b := by
  funext k
  simp [negativeBinomialCensoredWeight, geometricCensoredWeight,
    negativeBinomialWeight_one, negativeBinomialCensorTail_one]

/-- One-success negative binomial is literally the same finite law. -/
theorem negativeBinomial_one_eq_geometric (cap a b : Nat) (ha : 0 < a) :
    negativeBinomialDistro 1 cap a b (Nat.succ_pos _) ha =
      geometricDistro cap a b ha := by
  simp [negativeBinomialDistro, geometricDistro, negativeBinomialWeight_one]

theorem negativeBinomialCensored_one_eq_geometric (cap a b : Nat) (ha : 0 < a) :
    negativeBinomialCensoredDistro 1 cap a b (Nat.succ_pos _) ha =
      geometricCensoredDistro cap a b ha := by
  simp [negativeBinomialCensoredDistro, geometricCensoredDistro,
    negativeBinomialCensoredWeight_one]

theorem negativeBinomialNat_one_eq_geometric (cap a b : Nat) (ha : 0 < a) :
    negativeBinomialNatDistro 1 cap a b (Nat.succ_pos _) ha =
      geometricNatDistro cap a b ha := by
  simp [negativeBinomialNatDistro, geometricNatDistro, negativeBinomial_one_eq_geometric]

theorem negativeBinomialCensoredNat_one_eq_geometric (cap a b : Nat) (ha : 0 < a) :
    negativeBinomialCensoredNatDistro 1 cap a b (Nat.succ_pos _) ha =
      geometricCensoredNatDistro cap a b ha := by
  simp [negativeBinomialCensoredNatDistro, geometricCensoredNatDistro,
    negativeBinomialCensored_one_eq_geometric]

theorem negativeBinomial_one_event (cap a b : Nat) (ha : 0 < a)
    (event : Event (Fin (cap + 1))) :
    QProb.Equiv
      ((negativeBinomialDistro 1 cap a b (Nat.succ_pos _) ha).record.probVal event)
      ((geometricDistro cap a b ha).record.probVal event) := by
  rw [negativeBinomial_one_eq_geometric]
  exact QProb.equiv_refl _

theorem negativeBinomialCensored_one_event (cap a b : Nat) (ha : 0 < a)
    (event : Event (Fin (cap + 1))) :
    QProb.Equiv
      ((negativeBinomialCensoredDistro 1 cap a b (Nat.succ_pos _) ha).record.probVal event)
      ((geometricCensoredDistro cap a b ha).record.probVal event) := by
  rw [negativeBinomialCensored_one_eq_geometric]
  exact QProb.equiv_refl _

theorem negativeBinomial_one_pmf (cap a b : Nat) (ha : 0 < a) (k : Fin (cap + 1)) :
    QProb.Equiv
      ((negativeBinomialDistro 1 cap a b (Nat.succ_pos _) ha).pmf k)
      ((geometricDistro cap a b ha).pmf k) := by
  rw [negativeBinomial_one_eq_geometric]
  exact QProb.equiv_refl _

theorem negativeBinomialCensored_one_pmf (cap a b : Nat) (ha : 0 < a)
    (k : Fin (cap + 1)) :
    QProb.Equiv
      ((negativeBinomialCensoredDistro 1 cap a b (Nat.succ_pos _) ha).pmf k)
      ((geometricCensoredDistro cap a b ha).pmf k) := by
  rw [negativeBinomialCensored_one_eq_geometric]
  exact QProb.equiv_refl _

theorem negativeBinomial_one_pgf (cap a b : Nat) (ha : 0 < a) (s : QProb) :
    QProb.Equiv
      (pgf (negativeBinomialNatDistro 1 cap a b (Nat.succ_pos _) ha) s)
      (pgf (geometricNatDistro cap a b ha) s) := by
  rw [negativeBinomialNat_one_eq_geometric]
  exact QProb.equiv_refl _

theorem negativeBinomialCensored_one_pgf (cap a b : Nat) (ha : 0 < a) (s : QProb) :
    QProb.Equiv
      (pgf (negativeBinomialCensoredNatDistro 1 cap a b (Nat.succ_pos _) ha) s)
      (pgf (geometricCensoredNatDistro cap a b ha) s) := by
  rw [negativeBinomialCensoredNat_one_eq_geometric]
  exact QProb.equiv_refl _

end Distros
end Probability
end Thesis
