import Thesis.Probability.Distros.PositiveSupport
import Thesis.Probability.Distros.MultivariateFactorialPGF

namespace Thesis.Probability.Distros
open Combinatorics

/-- Bounded numeric factorial expansion needs the bound only almost surely.
Every original atom, including a zero-weight outlier, remains in the record. -/
theorem pgf_factorial_expansion_positiveSupport (μ : NatDistro Ω) (bound : Nat)
    (support : μ.distro.AlmostSurely (fun x => μ.embed x ≤ bound)) (t : QProb) :
    QProb.Equiv (pgf μ (QProb.add t QProb.one))
      (QProb.listSum ((List.range (bound + 1)).map (fun r =>
        QProb.mul (factorialPGFCoefficient μ r) (qpow t r)))) := by
  rw [pgf_expectation]
  refine QProb.equiv_trans (μ.distro.expectation_congr_positive
    (fun x => qpow (QProb.add t QProb.one) (μ.embed x))
    (fun x => QProb.listSum ((List.range (bound + 1)).map (fun r => QProb.scale (binom (μ.embed x) r) (qpow t r))))
    (fun atom member weight => qpow_add_one_bounded _ bound (support atom member weight) t)) ?_
  refine QProb.equiv_trans (μ.distro.expectation_listSum (List.range (bound + 1))
    (fun r x => QProb.scale (binom (μ.embed x) r) (qpow t r))) ?_
  apply QProb.listSum_map_congr
  intro r
  refine QProb.equiv_trans (μ.distro.expectation_congr _
    (fun x => QProb.mul (qpow t r) (QProb.ofNat (binom (μ.embed x) r))) (fun x => ?_)) ?_
  · simp only [QProb.Equiv, QProb.scale, QProb.mul, QProb.ofNat, Nat.mul_one]
    ac_rfl
  · exact QProb.equiv_trans (μ.distro.expectation_scale _ _)
      (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) (μ.distro.expectation_nat _))
        (QProb.equiv_trans (QProb.mul_comm _ _)
          (QProb.mul_congr (QProb.equiv_symm (factorialPGFCoefficient_binom μ r)) (QProb.equiv_refl _))))

/-- The multivariate factorial expansion needs shape and bounds only on
positive-weight atoms. No record or declared-domain normalization is performed. -/
theorem multivariatePGF_factorial_expansion_positiveSupport (μ : Distro (List Nat)) (args : List QProb) (bound : Nat)
    (support : μ.AlmostSurely (fun counts => counts.length = args.length ∧ ∀ count ∈ counts, count ≤ bound)) :
    QProb.Equiv (multivariatePGF μ (args.map (fun t => QProb.add t QProb.one)))
      (QProb.listSum ((factorialBox args.length bound).map (fun orders =>
        QProb.mul (multivariateFactorialCoefficient μ orders) (multivariateMonomial args orders)))) := by
  refine QProb.equiv_trans (μ.expectation_congr_positive
    (multivariateMonomial (args.map (fun t => QProb.add t QProb.one)))
    (fun counts => QProb.listSum ((factorialBox args.length bound).map (fun orders =>
      QProb.scale (jointChoose orders counts) (multivariateMonomial args orders))))
    (fun atom member weight => multivariateMonomial_add_one args atom.1 bound (support atom member weight).1 (support atom member weight).2)) ?_
  refine QProb.equiv_trans (μ.expectation_listSum (factorialBox args.length bound)
    (fun orders counts => QProb.scale (jointChoose orders counts) (multivariateMonomial args orders))) ?_
  apply QProb.listSum_map_congr
  intro orders
  refine QProb.equiv_trans (μ.expectation_congr _
    (fun counts => QProb.mul (multivariateMonomial args orders) (QProb.ofNat (jointChoose orders counts))) (fun counts => ?_)) ?_
  · simp only [QProb.Equiv, QProb.scale, QProb.mul, QProb.ofNat, Nat.mul_one]
    ac_rfl
  · exact QProb.equiv_trans (μ.expectation_scale _ _)
      (QProb.equiv_trans (QProb.mul_congr (QProb.equiv_refl _) (μ.expectation_nat _))
        (QProb.equiv_trans (QProb.mul_comm _ _)
          (QProb.mul_congr (QProb.equiv_symm (multivariateFactorialCoefficient_choose μ orders)) (QProb.equiv_refl _))))

/-- Numeric laws are reconstructed from bounded factorial moments even when
recorded zero-weight outcomes lie above the supplied support bound. -/
theorem NatDistro.sameLaw_of_factorialMoments_positiveSupport (μ : NatDistro Ω) (ν : NatDistro X) (bound : Nat)
    (hμ : μ.distro.AlmostSurely (fun x => μ.embed x ≤ bound))
    (hν : ν.distro.AlmostSurely (fun x => ν.embed x ≤ bound))
    (same : ∀ order, order ≤ bound → QProb.Equiv (factorialMoment μ order) (factorialMoment ν order)) : μ.SameLaw ν := by
  let base := μ.distro.record.den * ν.distro.record.den
  let t := QProb.ofNat base
  have arguments : QProb.Equiv (QProb.add t QProb.one) (QProb.ofNat (base + 1)) := by
    simp only [t, QProb.Equiv, QProb.add, QProb.ofNat, QProb.one, Nat.mul_one]
  have expansion := qprob_listSum_map_congr_on_mem (List.range (bound + 1))
    (fun r => QProb.mul (factorialPGFCoefficient μ r) (qpow t r))
    (fun r => QProb.mul (factorialPGFCoefficient ν r) (qpow t r)) (fun r member =>
      QProb.mul_congr (QProb.div_congr (same r (by have h := List.mem_range.mp member; omega))
        (QProb.equiv_refl _) _ _) (QProb.equiv_refl _))
  have left := pgf_factorial_expansion_positiveSupport μ bound hμ t
  have right := pgf_factorial_expansion_positiveSupport ν bound hν t
  rw [pgf_expectation] at left right
  apply NatDistro.sameLaw_of_pgf_largeNat μ ν
  rw [pgf_expectation, pgf_expectation]
  exact QProb.equiv_trans
    (μ.distro.expectation_congr _ _ (fun x => qpow_congr (QProb.equiv_symm arguments) (μ.embed x)))
    (QProb.equiv_trans left
      (QProb.equiv_trans expansion (QProb.equiv_trans (QProb.equiv_symm right)
        (ν.distro.expectation_congr _ _ (fun x => qpow_congr arguments (ν.embed x))))))

end Thesis.Probability.Distros
