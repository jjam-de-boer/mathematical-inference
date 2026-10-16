import Thesis.Probability.Distros.FactorialMoments
import Thesis.Probability.Distros.PGFUniqueness

namespace Thesis.Probability.Distros
open Combinatorics

/-- The coefficient E[(X)_r]/r! in the finite expansion about one. -/
def factorialPGFCoefficient (μ : NatDistro Ω) (order : Nat) : QProb :=
  QProb.div (factorialMoment μ order) (QProb.ofNat (fallingFactorial order order))
    (fallingFactorial_pos order order (Nat.le_refl _))

theorem factorialPGFCoefficient_binom (μ : NatDistro Ω) (order : Nat) :
    QProb.Equiv (factorialPGFCoefficient μ order) (μ.distro.expectNat (fun x => binom (μ.embed x) order)) := by
  have falling : factorialMoment μ order =
      μ.distro.expectNat (fun x => binom (μ.embed x) order * fallingFactorial order order) := by
    apply μ.distro.expectNat_congr_on_support
    intro atom _
    rw [fallingFactorial_binom]
    exact Nat.mul_comm _ _
  unfold factorialPGFCoefficient
  rw [falling]
  refine QProb.equiv_trans (QProb.div_congr (μ.distro.expectNat_scale _ _)
    (QProb.equiv_refl _) (fallingFactorial_pos order order (Nat.le_refl _))
    (fallingFactorial_pos order order (Nat.le_refl _))) ?_
  simp only [QProb.Equiv, QProb.div, QProb.scale, QProb.ofNat]
  ac_rfl

/-- Finite sums can be exchanged with rational expectation. -/
theorem Distro.expectation_listSum (μ : Distro Ω) (values : List X) (f : X → Ω → QProb) :
    QProb.Equiv (μ.expectation (fun x => QProb.listSum (values.map (fun i => f i x))))
      (QProb.listSum (values.map (fun i => μ.expectation (f i)))) := by
  induction values with
  | nil => exact μ.expectation_constant QProb.zero
  | cons value values ih =>
      exact QProb.equiv_trans (μ.expectation_add _ _) (QProb.add_congr (QProb.equiv_refl _) ih)

private theorem qprob_range_extend (n bound : Nat) (within : n ≤ bound) (f : Nat → QProb)
    (zero : ∀ k, n ≤ k → k < bound → QProb.Equiv (f k) QProb.zero) :
    QProb.Equiv (QProb.listSum ((List.range bound).map f)) (QProb.listSum ((List.range n).map f)) := by
  induction bound generalizing n with
  | zero =>
      have equal : n = 0 := by omega
      subst n
      exact QProb.equiv_refl _
  | succ bound ih =>
      by_cases equal : n = bound + 1
      · subst n; exact QProb.equiv_refl _
      · have smaller : n ≤ bound := by omega
        rw [List.range_succ, List.map_append]
        refine QProb.equiv_trans (QProb.listSum_append _ _) ?_
        have last : QProb.Equiv (QProb.listSum [f bound]) QProb.zero :=
          QProb.equiv_trans (QProb.add_zero _) (zero bound smaller (Nat.lt_succ_self _))
        exact QProb.equiv_trans
          (QProb.add_congr (ih n smaller (fun k lower upper => zero k lower (by omega))) last)
          (QProb.add_zero _)

private theorem qpow_one_value (n : Nat) : QProb.Equiv (qpow QProb.one n) QProb.one := by
  simp only [QProb.Equiv, qpow_num, qpow_den, QProb.one, Nat.one_pow, Nat.mul_one]

/-- The bounded binomial expansion pads only with proved zero coefficients. -/
theorem qpow_add_one_bounded (n bound : Nat) (within : n ≤ bound) (t : QProb) :
    QProb.Equiv (qpow (QProb.add t QProb.one) n)
      (QProb.listSum ((List.range (bound + 1)).map (fun r => QProb.scale (binom n r) (qpow t r)))) := by
  refine QProb.equiv_trans (QProb.equiv_symm (qprob_binomial_theorem t QProb.one n)) ?_
  refine QProb.equiv_trans (QProb.listSum_map_congr (List.range (n + 1)) _ _ (fun r =>
    QProb.scale_congr _ (QProb.equiv_trans
      (QProb.mul_congr (QProb.equiv_refl _) (qpow_one_value _)) (QProb.mul_one _)))) ?_
  apply QProb.equiv_symm
  apply qprob_range_extend (n + 1) (bound + 1) (by omega)
  intro r lower _
  simp only [binom_eq_zero_of_lt (by omega : n < r), QProb.Equiv, QProb.scale, QProb.zero, Nat.zero_mul]

/-- The exact finite Taylor/binomial expansion
G(1+t) = sum_{r=0}^bound E[(X)_r] t^r / r!.
Every nonnegative rational `t` is allowed; no analytic differentiation,
convergence, or choice of reduced rational representatives is required. -/
theorem pgf_factorial_expansion (μ : NatDistro Ω) (bound : Nat)
    (support : ∀ atom ∈ μ.distro.record.atoms, μ.embed atom.1 ≤ bound) (t : QProb) :
    QProb.Equiv (pgf μ (QProb.add t QProb.one))
      (QProb.listSum ((List.range (bound + 1)).map (fun r =>
        QProb.mul (factorialPGFCoefficient μ r) (qpow t r)))) := by
  refine QProb.equiv_trans (pgf_expectation μ (QProb.add t QProb.one)) ?_
  refine QProb.equiv_trans (μ.distro.expectation_congr_on_support
    (fun x => qpow (QProb.add t QProb.one) (μ.embed x))
    (fun x => QProb.listSum ((List.range (bound + 1)).map (fun r => QProb.scale (binom (μ.embed x) r) (qpow t r))))
    (fun atom member => qpow_add_one_bounded _ bound (support atom member) t)) ?_
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

/-- Matching factorial moments through a common finite support bound
reconstructs the complete numeric law and therefore all event probabilities. -/
theorem NatDistro.sameLaw_of_factorialMoments (μ : NatDistro Ω) (ν : NatDistro X) (bound : Nat)
    (hμ : ∀ atom ∈ μ.distro.record.atoms, μ.embed atom.1 ≤ bound)
    (hν : ∀ atom ∈ ν.distro.record.atoms, ν.embed atom.1 ≤ bound)
    (same : ∀ order, order ≤ bound → QProb.Equiv (factorialMoment μ order) (factorialMoment ν order)) : μ.SameLaw ν := by
  let base := μ.distro.record.den * ν.distro.record.den
  let t := QProb.ofNat base
  have arguments : QProb.Equiv (QProb.add t QProb.one) (QProb.ofNat (base + 1)) := by
    simp only [t, QProb.Equiv, QProb.add, QProb.ofNat, QProb.one, Nat.mul_one, Nat.one_mul]
  have expansion := qprob_listSum_map_congr_on_mem (List.range (bound + 1))
    (fun r => QProb.mul (factorialPGFCoefficient μ r) (qpow t r))
    (fun r => QProb.mul (factorialPGFCoefficient ν r) (qpow t r)) (fun r member =>
      QProb.mul_congr (QProb.div_congr (same r (by have h := List.mem_range.mp member; omega))
        (QProb.equiv_refl _) _ _) (QProb.equiv_refl _))
  apply NatDistro.sameLaw_of_pgf_largeNat μ ν
  exact QProb.equiv_trans
    (μ.distro.expectation_congr _ _ (fun x => qpow_congr (QProb.equiv_symm arguments) (μ.embed x)))
    (QProb.equiv_trans (pgf_factorial_expansion μ bound hμ t)
      (QProb.equiv_trans expansion (QProb.equiv_trans (QProb.equiv_symm (pgf_factorial_expansion ν bound hν t))
        (ν.distro.expectation_congr _ _ (fun x => qpow_congr arguments (ν.embed x))))))

/-- All factorial moments characterize every finite numeric law. -/
theorem NatDistro.sameLaw_iff_factorialMoments (μ : NatDistro Ω) (ν : NatDistro X) :
    μ.SameLaw ν ↔ ∀ order, QProb.Equiv (factorialMoment μ order) (factorialMoment ν order) := by
  constructor
  · exact fun same order => same.factorialMoment order
  · intro same
    let bound := max (observableBound μ.distro.record.atoms μ.embed) (observableBound ν.distro.record.atoms ν.embed)
    exact NatDistro.sameLaw_of_factorialMoments μ ν bound
      (fun atom member => Nat.le_trans (observableBound_mem _ _ atom member) (Nat.le_max_left _ _))
      (fun atom member => Nat.le_trans (observableBound_mem _ _ atom member) (Nat.le_max_right _ _))
      (fun order _ => same order)

end Thesis.Probability.Distros
