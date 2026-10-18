import Thesis.Probability.Distros.PositiveSupport
import Thesis.Probability.Distros.MultivariateFactorialPGF
import Thesis.Probability.Distros.DepletingHistory

namespace Thesis.Probability.Distros
open Combinatorics

theorem depletingCountsWithin_sum_le (counts stocks : List Nat) (within : depletingCountsWithin counts stocks) :
    counts.sum ≤ stocks.sum := by
  have balance := depletingState_sum stocks counts within
  omega

/-- Coordinatewise comparison and equal totals force identical vectors. -/
theorem depletingCountsWithin_eq_of_sum (counts stocks : List Nat) (within : depletingCountsWithin counts stocks)
    (total : counts.sum = stocks.sum) : counts = stocks := by
  induction counts generalizing stocks with
  | nil => cases stocks with
      | nil => rfl
      | cons stock stocks => exact False.elim within
  | cons count counts ih => cases stocks with
      | nil => exact False.elim within
      | cons stock stocks =>
          have tailBound := depletingCountsWithin_sum_le counts stocks within.2
          have headBound : count ≤ stock := within.1
          have head : count = stock := by simp only [List.sum_cons] at total; omega
          have tail : counts.sum = stocks.sum := by simp only [List.sum_cons, head] at total; omega
          rw [head, ih stocks within.2 tail]

theorem jointFalling_self (orders : List Nat) : jointFalling orders orders = orderFactorial orders := by
  induction orders with
  | nil => rfl
  | cons order orders ih => simp only [jointFalling, orderFactorial, ih]

/-- At equal total order the falling kernel is a singleton indicator times
the product of coordinate factorials. Mismatched dimensions also vanish. -/
theorem jointFalling_same_total (orders counts : List Nat) (total : orders.sum = counts.sum) :
    jointFalling orders counts = if counts = orders then orderFactorial orders else 0 := by
  by_cases same : counts = orders
  · subst counts
    simp [jointFalling_self]
  · rw [if_neg same]
    by_cases zero : jointFalling orders counts = 0
    · exact zero
    · have within := jointFalling_positive_within orders counts (Nat.pos_of_ne_zero zero)
      exact False.elim (same (depletingCountsWithin_eq_of_sum orders counts within total).symm)

/-- Highest-total-order moments isolate one count-vector mass. Only positive
atoms need have the fixed total; zero-weight outliers remain in the record. -/
theorem Distro.jointFactorialMoment_highest (μ : Distro (List Nat)) (total : Nat) (orders : List Nat)
    (fixed : μ.AlmostSurely (fun counts => counts.sum = total)) (orderTotal : orders.sum = total) :
    QProb.Equiv (jointFactorialMoment μ orders) (QProb.scale (orderFactorial orders) (μ.pmf orders)) := by
  have integral := μ.expectNat_congr_positive (jointFalling orders)
    (fun counts => (if FiniteProbRecord.singletonEvent orders counts then 1 else 0) * orderFactorial orders)
    (fun atom member weight => by
      change jointFalling orders atom.1 =
        (if FiniteProbRecord.singletonEvent orders atom.1 then 1 else 0) * orderFactorial orders
      rw [jointFalling_same_total orders atom.1 (orderTotal.trans (fixed atom member weight).symm)]
      by_cases same : atom.1 = orders
      · simp only [same, if_pos rfl, FiniteProbRecord.singletonEvent, decide_true, Nat.one_mul]
      · simp only [same, if_false, FiniteProbRecord.singletonEvent, decide_false, Nat.zero_mul])
  unfold jointFactorialMoment
  rw [integral]
  refine QProb.equiv_trans (μ.expectNat_scale _ _) (QProb.scale_congr _ ?_)
  simp only [Distro.expectNat, natIntegral_indicator, Distro.pmf, FiniteProbRecord.probVal]
  exact QProb.equiv_refl _

/-- The PMF is the highest-order mixed moment divided by coordinate factorials.
No ambient finiteness, positive cell probability, or positive trial count is assumed. -/
theorem Distro.pmf_of_highestFactorialMoment (μ : Distro (List Nat)) (total : Nat) (orders : List Nat)
    (fixed : μ.AlmostSurely (fun counts => counts.sum = total)) (orderTotal : orders.sum = total) :
    QProb.Equiv (μ.pmf orders)
      (QProb.div (jointFactorialMoment μ orders) (QProb.ofNat (orderFactorial orders)) (orderFactorial_pos orders)) := by
  apply QProb.equiv_symm
  refine QProb.equiv_trans (QProb.div_congr (μ.jointFactorialMoment_highest total orders fixed orderTotal)
    (QProb.equiv_refl _) (orderFactorial_pos orders) (orderFactorial_pos orders)) ?_
  simp only [QProb.Equiv, QProb.div, QProb.scale, QProb.ofNat]
  ac_rfl

/-- Fixed-length laws with almost-sure total N are determined by mixed
moments whose total order is exactly N. Rectangular lower orders are unnecessary. -/
theorem Distro.sameLaw_of_highestFactorialMoments (μ ν : Distro (List Nat)) (length total : Nat)
    (hμ : μ.AlmostSurely (fun counts => counts.length = length ∧ counts.sum = total))
    (hν : ν.AlmostSurely (fun counts => counts.length = length ∧ counts.sum = total))
    (same : ∀ orders, orders.length = length → orders.sum = total →
      QProb.Equiv (jointFactorialMoment μ orders) (jointFactorialMoment ν orders)) : μ.SameLaw ν := by
  apply Distro.sameLaw_of_pmf
  intro orders
  by_cases valid : orders.length = length ∧ orders.sum = total
  · exact QProb.equiv_trans (μ.pmf_of_highestFactorialMoment total orders (fun atom member weight => (hμ atom member weight).2) valid.2)
      (QProb.equiv_trans (QProb.div_congr (same orders valid.1 valid.2) (QProb.equiv_refl _) _ _)
        (QProb.equiv_symm (ν.pmf_of_highestFactorialMoment total orders (fun atom member weight => (hν atom member weight).2) valid.2)))
  · have left := μ.pmf_zero_of_almostSure_ne orders (fun atom member weight same => valid (same ▸ hμ atom member weight))
    have right := ν.pmf_zero_of_almostSure_ne orders (fun atom member weight same => valid (same ▸ hν atom member weight))
    exact QProb.equiv_trans left (QProb.equiv_symm right)

/-- Closed multinomial PMF recovered from the mixed highest-order formula. -/
theorem multinomial_pmf_highestOrder (n : Nat) (weights counts : List Nat) (positive : 0 < weights.sum)
    (dimension : counts.length = weights.length) (total : counts.sum = n) :
    QProb.Equiv ((multinomialDistro n weights positive).pmf counts)
      (QProb.div (⟨fallingFactorial n n * natMonomial weights counts, weights.sum ^ n, Nat.pow_pos positive⟩ : QProb)
        (QProb.ofNat (orderFactorial counts)) (orderFactorial_pos counts)) := by
  refine QProb.equiv_trans (Distro.pmf_of_highestFactorialMoment _ n counts
    (fun atom member _ => (multinomialAtoms_support n weights atom member).2) total) ?_
  apply QProb.div_congr _ (QProb.equiv_refl _) _ _
  simpa only [total] using multinomial_jointFactorialMoment n weights counts positive dimension

/-- The same PMF extraction works at every natural reinforcement increment. -/
theorem reinforcedCount_pmf_highestOrder (n increment : Nat) (alphas counts : List Nat) (positive : 0 < alphas.sum)
    (dimension : counts.length = alphas.length) (total : counts.sum = n) :
    QProb.Equiv ((reinforcedCountDistro n alphas increment positive).pmf counts)
      (QProb.div (⟨fallingFactorial n n * stepKernel increment alphas counts,
        stepRising alphas.sum increment n, stepRising_pos _ _ _ positive⟩ : QProb)
        (QProb.ofNat (orderFactorial counts)) (orderFactorial_pos counts)) := by
  refine QProb.equiv_trans (Distro.pmf_of_highestFactorialMoment _ n counts
    (fun atom member _ => (reinforcedCount_support n alphas increment atom member).2) total) ?_
  apply QProb.div_congr _ (QProb.equiv_refl _) _ _
  simpa only [total] using reinforcedCount_jointFactorialMoment n increment alphas counts positive dimension

/-- Sampling without replacement yields its PMF through the same generic
highest-order identity, including empty populations and zero draws. -/
theorem multivariateHypergeometric_pmf_highestOrder (n : Nat) (stocks counts : List Nat)
    (positive : 0 < binom stocks.sum n) (dimension : counts.length = stocks.length) (total : counts.sum = n) :
    QProb.Equiv ((multivariateHypergeometricDistro n stocks positive).pmf counts)
      (QProb.div (⟨fallingFactorial n n * jointFalling counts stocks,
        fallingFactorial stocks.sum n, fallingFactorial_pos _ _ (hypergeometric_draws_le_total _ _ positive)⟩ : QProb)
        (QProb.ofNat (orderFactorial counts)) (orderFactorial_pos counts)) := by
  refine QProb.equiv_trans (Distro.pmf_of_highestFactorialMoment _ n counts
    (fun atom member _ => (multivariateHypergeometric_support n stocks atom member).2) total) ?_
  apply QProb.div_congr _ (QProb.equiv_refl _) _ _
  simpa only [total] using multivariateHypergeometric_jointFactorialMoment n stocks counts positive dimension
    (by rw [total]; exact hypergeometric_draws_le_total _ _ positive)

end Thesis.Probability.Distros
