import Thesis.Probability.Distros.BetaBinomial
import Thesis.Probability.Distros.BetaBinomialMoments
import Thesis.Probability.Distros.FactorialMoments
import Thesis.Probability.Distros.PointMass

namespace Thesis.Probability.Distros
open Combinatorics

/-!
Positive-total variants of censored waiting times and beta-binomial.
The existing strict constructors are definitionally equal on their domains.
Zero success weight censors at the cap; a zero beta-binomial colour count
is a point mass at zero or at the trial total.  The reinforced-urn
correspondence and all-order beta-binomial moments include these endpoints.
-/

/-- Right censoring is defined whenever the Bernoulli total is positive. -/
def geometricCensoredDistroOfTotal (cap a b : Nat) (positive : 0 < a + b) : Distro (Fin (cap + 1)) :=
  ⟨ofFinWeights (cap + 1) (geometricCensoredWeight cap a b) (by
    rw [geometricCensoredWeight_sum]
    exact Nat.pow_pos positive)⟩

def geometricCensoredNatDistroOfTotal (cap a b : Nat) (positive : 0 < a + b) : NatDistro (Fin (cap + 1)) :=
  ⟨geometricCensoredDistroOfTotal cap a b positive, Fin.val⟩

def negativeBinomialCensoredDistroOfTotal (r cap a b : Nat) (shape : 0 < r)
    (positive : 0 < a + b) : Distro (Fin (cap + 1)) :=
  ⟨ofFinWeights (cap + 1) (negativeBinomialCensoredWeight r cap a b) (by
    rw [negativeBinomialCensoredWeight_sum, negativeBinomialCensored_exhaustion a b r cap shape]
    exact Nat.pow_pos positive)⟩

def negativeBinomialCensoredNatDistroOfTotal (r cap a b : Nat) (shape : 0 < r)
    (positive : 0 < a + b) : NatDistro (Fin (cap + 1)) :=
  ⟨negativeBinomialCensoredDistroOfTotal r cap a b shape positive, Fin.val⟩

theorem betaBinomialWeight_sum (n a b : Nat) :
    natSum (n + 1) (finWeight (betaBinomialWeight n a b)) = risingFactorial (a + b) n := by
  have h : natSum (n + 1) (finWeight (betaBinomialWeight n a b)) =
      natSum (n + 1) (betaBinomialTerm n a b) := by
    apply natSum_congr
    intro k hk
    simp only [finWeight, dif_pos hk, betaBinomialWeight, betaBinomialTerm]
  rw [h, risingFactorial_vandermonde]

/-- Beta-binomial, including either deterministic one-colour endpoint. -/
def betaBinomialDistroOfTotal (n a b : Nat) (positive : 0 < a + b) : Distro (Fin (n + 1)) :=
  ⟨ofFinWeights (n + 1) (betaBinomialWeight n a b) (by
    rw [betaBinomialWeight_sum]
    exact risingFactorial_pos _ _ positive)⟩

def betaBinomialNatDistroOfTotal (n a b : Nat) (positive : 0 < a + b) : NatDistro (Fin (n + 1)) :=
  ⟨betaBinomialDistroOfTotal n a b positive, Fin.val⟩

theorem geometricCensoredOfTotal_eq (cap a b : Nat) (positive : 0 < a) :
    geometricCensoredDistroOfTotal cap a b (Nat.add_pos_left positive b) =
      geometricCensoredDistro cap a b positive := rfl

theorem negativeBinomialCensoredOfTotal_eq (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a) :
    negativeBinomialCensoredDistroOfTotal r cap a b shape (Nat.add_pos_left positive b) =
      negativeBinomialCensoredDistro r cap a b shape positive := rfl

theorem betaBinomialOfTotal_eq (n a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    betaBinomialDistroOfTotal n a b (Nat.add_pos_left ha b) = betaBinomialDistro n a b ha hb := rfl

theorem geometricCensoredOfTotal_den (cap a b : Nat) (positive : 0 < a + b) :
    (geometricCensoredDistroOfTotal cap a b positive).record.den = (a + b) ^ (cap + 1) := by
  change FiniteProbRecord.totalMass (finWeighted (cap + 1) (geometricCensoredWeight cap a b)) = _
  rw [totalMass_finWeighted, geometricCensoredWeight_sum]

theorem negativeBinomialCensoredOfTotal_den (r cap a b : Nat) (shape : 0 < r) (positive : 0 < a + b) :
    (negativeBinomialCensoredDistroOfTotal r cap a b shape positive).record.den = (a + b) ^ (cap + r) := by
  change FiniteProbRecord.totalMass (finWeighted (cap + 1) (negativeBinomialCensoredWeight r cap a b)) = _
  rw [totalMass_finWeighted, negativeBinomialCensoredWeight_sum,
    negativeBinomialCensored_exhaustion a b r cap shape]

theorem betaBinomialOfTotal_den (n a b : Nat) (positive : 0 < a + b) :
    (betaBinomialDistroOfTotal n a b positive).record.den = risingFactorial (a + b) n := by
  change FiniteProbRecord.totalMass (finWeighted (n + 1) (betaBinomialWeight n a b)) = _
  rw [totalMass_finWeighted, betaBinomialWeight_sum]

theorem geometricCensoredOfTotal_zero (cap b : Nat) (positive : 0 < b) :
    (geometricCensoredDistroOfTotal cap 0 b (by omega)).SameLaw (Distro.pointMass (Fin.last cap)) := by
  apply ofFinWeights_pointMass
  intro k ne
  have bound : k.val < cap := by
    have hk := k.isLt
    have different : k.val ≠ cap := fun h => ne (Fin.ext h)
    omega
  simp only [geometricCensoredWeight, if_pos bound, geometricWeight, Nat.zero_mul]

theorem negativeBinomialCensoredOfTotal_zero (r cap b : Nat) (shape : 0 < r) (positive : 0 < b) :
    (negativeBinomialCensoredDistroOfTotal r cap 0 b shape (by omega)).SameLaw
      (Distro.pointMass (Fin.last cap)) := by
  apply ofFinWeights_pointMass
  intro k ne
  have bound : k.val < cap := by
    have hk := k.isLt
    have different : k.val ≠ cap := fun h => ne (Fin.ext h)
    omega
  simp only [negativeBinomialCensoredWeight, if_pos bound, negativeBinomialWeight,
    Nat.zero_pow shape, Nat.mul_zero, Nat.zero_mul]

theorem risingFactorial_zero_base (n : Nat) (positive : 0 < n) : risingFactorial 0 n = 0 := by
  cases n with
  | zero => omega
  | succ n => rw [risingFactorial_head]; exact Nat.zero_mul _

theorem betaBinomialOfTotal_zero_left (n b : Nat) (positive : 0 < b) :
    (betaBinomialDistroOfTotal n 0 b (by omega)).SameLaw
      (Distro.pointMass (⟨0, Nat.succ_pos n⟩ : Fin (n + 1))) := by
  apply ofFinWeights_pointMass
  intro k ne
  have nonzero : 0 < k.val := by
    have different : k.val ≠ 0 := fun h => ne (Fin.ext h)
    omega
  simp only [betaBinomialWeight, risingFactorial_zero_base k.val nonzero, Nat.mul_zero, Nat.zero_mul]

theorem betaBinomialOfTotal_zero_right (n a : Nat) (positive : 0 < a) :
    (betaBinomialDistroOfTotal n a 0 (by omega)).SameLaw (Distro.pointMass (Fin.last n)) := by
  apply ofFinWeights_pointMass
  intro k ne
  have nonzero : 0 < n - k.val := by
    have hk := k.isLt
    have different : k.val ≠ n := fun h => ne (Fin.ext h)
    omega
  simp only [betaBinomialWeight, risingFactorial_zero_base (n - k.val) nonzero, Nat.mul_zero]

/-- The reinforced-urn correspondence includes both one-colour endpoints. -/
theorem polyaUrn_total_correspondence (n a b : Nat) (positive : 0 < a + b) :
    (polyaUrnDistro n a b positive).SameLaw (betaBinomialDistroOfTotal n a b positive) := by
  apply Distro.sameLaw_of_singletons _ _ (List.finRange (n + 1))
    (finRange_nodup _) (fun value => List.mem_finRange value)
  intro k
  have hm := polyaUrn_mass n a b positive k
  change FiniteProbRecord.eventMass _ _ * (betaBinomialDistroOfTotal n a b positive).record.den =
    FiniteProbRecord.eventMass (finWeighted (n + 1) (betaBinomialWeight n a b))
      (FiniteProbRecord.singletonEvent k) * risingFactorial (a + b) n
  rw [hm, betaBinomialOfTotal_den, eventMass_finWeighted_singleton]

theorem betaBinomialOfTotal_factorialMoment (n a b order : Nat) (positive : 0 < a + b) :
    QProb.Equiv (factorialMoment (betaBinomialNatDistroOfTotal n a b positive) order)
      ⟨fallingFactorial n order * risingFactorial a order, risingFactorial (a + b) order,
        risingFactorial_pos _ _ (positive)⟩ := by
  have hn : (factorialMoment (betaBinomialNatDistroOfTotal n a b positive) order).num =
      natSum (n + 1) (fun k => fallingFactorial k order * betaBinomialTerm n a b k) := by
    change natIntegral (finWeighted (n + 1) (betaBinomialWeight n a b))
      (fun k => fallingFactorial k.val order) = _
    rw [natIntegral_finWeighted (n + 1) (betaBinomialWeight n a b) (fun k => fallingFactorial k order)]
    apply natSum_congr
    intro k hk
    simp only [finWeight, dif_pos hk, betaBinomialWeight, betaBinomialTerm]
    ac_rfl
  change (factorialMoment (betaBinomialNatDistroOfTotal n a b positive) order).num * risingFactorial (a + b) order =
    (fallingFactorial n order * risingFactorial a order) * (betaBinomialDistroOfTotal n a b positive).record.den
  rw [hn, betaBinomialTerm_factorial_moment, betaBinomialOfTotal_den]
  by_cases within : order ≤ n
  · have product : risingFactorial (a + b) n =
        risingFactorial (a + b) order * risingFactorial (a + b + order) (n - order) := by
      simpa only [Nat.add_sub_of_le within] using risingFactorial_add (a + b) order (n - order)
    rw [product]
    ac_rfl
  · rw [fallingFactorial_eq_zero n order (by omega)]
    simp only [Nat.zero_mul]

theorem betaBinomialOfTotal_mean (n a b : Nat) (positive : 0 < a + b) :
    QProb.Equiv (mean (betaBinomialNatDistroOfTotal n a b positive))
      ⟨n * a, a + b, positive⟩ := by
  by_cases ha : a = 0
  · subst a
    refine QProb.equiv_trans
      ((betaBinomialOfTotal_zero_left n b (by omega)).pointMass_moments Fin.val).1 ?_
    simp only [QProb.Equiv, QProb.ofNat, Nat.mul_zero, Nat.zero_mul, Nat.mul_one]
  · by_cases hb : b = 0
    · subst b
      refine QProb.equiv_trans
        ((betaBinomialOfTotal_zero_right n a (by omega)).pointMass_moments Fin.val).1 ?_
      simp only [QProb.Equiv, QProb.ofNat, Nat.add_zero, Nat.mul_one, Fin.val_last]
    · exact betaBinomial_mean n a b (by omega) (by omega)

theorem betaBinomialOfTotal_variance (n a b : Nat) (positive : 0 < a + b) :
    QProb.Equiv (variance (betaBinomialNatDistroOfTotal n a b positive))
      ⟨n * a * b * (a + b + n), (a + b) * (a + b) * (a + b + 1),
        Nat.mul_pos (Nat.mul_pos positive positive) (Nat.succ_pos _)⟩ := by
  by_cases ha : a = 0
  · subst a
    refine QProb.equiv_trans
      ((betaBinomialOfTotal_zero_left n b (by omega)).pointMass_moments Fin.val).2.1 ?_
    simp only [QProb.Equiv, QProb.zero, Nat.mul_zero, Nat.zero_mul]
  · by_cases hb : b = 0
    · subst b
      refine QProb.equiv_trans
        ((betaBinomialOfTotal_zero_right n a (by omega)).pointMass_moments Fin.val).2.1 ?_
      simp only [QProb.Equiv, QProb.zero, Nat.mul_zero, Nat.zero_mul]
    · exact betaBinomial_variance n a b (by omega) (by omega)

theorem geometricCensoredOfTotal_zero_moments (cap b : Nat) (positive : 0 < b) :
    QProb.Equiv (mean (geometricCensoredNatDistroOfTotal cap 0 b (by omega))) (QProb.ofNat cap) ∧
    QProb.Equiv (variance (geometricCensoredNatDistroOfTotal cap 0 b (by omega))) QProb.zero ∧
    (∀ s : QProb, QProb.Equiv (pgf (geometricCensoredNatDistroOfTotal cap 0 b (by omega)) s) (qpow s cap)) := by
  simpa only [geometricCensoredNatDistroOfTotal, Fin.val_last] using
    (geometricCensoredOfTotal_zero cap b positive).pointMass_moments Fin.val

theorem negativeBinomialCensoredOfTotal_zero_moments (r cap b : Nat) (shape : 0 < r) (positive : 0 < b) :
    QProb.Equiv (mean (negativeBinomialCensoredNatDistroOfTotal r cap 0 b shape (by omega))) (QProb.ofNat cap) ∧
    QProb.Equiv (variance (negativeBinomialCensoredNatDistroOfTotal r cap 0 b shape (by omega))) QProb.zero ∧
    (∀ s : QProb, QProb.Equiv
      (pgf (negativeBinomialCensoredNatDistroOfTotal r cap 0 b shape (by omega)) s) (qpow s cap)) := by
  simpa only [negativeBinomialCensoredNatDistroOfTotal, Fin.val_last] using
    (negativeBinomialCensoredOfTotal_zero r cap b shape positive).pointMass_moments Fin.val

end Thesis.Probability.Distros
