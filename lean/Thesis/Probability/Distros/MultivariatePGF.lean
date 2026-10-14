import Thesis.Probability.Distros.Multinomial
import Thesis.Probability.Distros.Moments

namespace Thesis.Probability.Distros

open Combinatorics

/-! Multivariate generating functions of finite occupancy vectors. -/

theorem multinomialAtoms_support (trials : Nat) (weights : List Nat)
    (atom : List Nat × Nat) (member : atom ∈ multinomialAtoms trials weights) :
    atom.1.length = weights.length ∧ atom.1.sum = trials := by
  induction weights generalizing trials atom with
  | nil =>
      cases trials with
      | zero =>
          change atom ∈ [([], 1)] at member
          have he := List.mem_singleton.mp member
          cases he
          exact ⟨rfl, rfl⟩
      | succ trials =>
          have hn : trials + 1 ≠ 0 := Nat.ne_of_gt (Nat.succ_pos trials)
          simp only [multinomialAtoms, if_neg hn, List.not_mem_nil] at member
  | cons weight rest ih =>
      simp only [multinomialAtoms, List.mem_flatMap, List.mem_map] at member
      rcases member with ⟨used, hused, source, hsource, he⟩
      cases he
      have hs := ih (trials - used) source hsource
      have hu : used ≤ trials := Nat.le_of_lt_succ (List.mem_range.mp hused)
      exact ⟨congrArg Nat.succ hs.1, by simp only [List.sum_cons, hs.2, Nat.add_sub_of_le hu]⟩

/-- A dimension mismatch has value zero. -/
def multivariateMonomial : List QProb → List Nat → QProb
  | [], [] => QProb.one
  | arg :: args, count :: counts => QProb.mul (qpow arg count) (multivariateMonomial args counts)
  | _, _ => QProb.zero

def multivariatePGF (μ : Distro (List Nat)) (args : List QProb) : QProb :=
  μ.expectation (multivariateMonomial args)

/-- Unnormalised categorical linear form `∑ weightᵢ argᵢ`. -/
def weightedArgument : List Nat → List QProb → QProb
  | weight :: weights, arg :: args => QProb.add (QProb.scale weight arg) (weightedArgument weights args)
  | _, _ => QProb.zero

theorem sum_map_range_natSum (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = natSum n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      rfl

theorem qprob_binomial_term (p q : QProb) (n k : Nat) (hk : k ≤ n) :
    QProb.Equiv (QProb.scale (binom n k) (QProb.mul (qpow p k) (qpow q (n - k))))
      ⟨binomTerm n (p.num * q.den) (q.num * p.den) k,
        (p.den * q.den) ^ n, Nat.pow_pos (Nat.mul_pos p.den_pos q.den_pos)⟩ := by
  have hp : p.den ^ n = p.den ^ k * p.den ^ (n - k) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  have hq : q.den ^ n = q.den ^ k * q.den ^ (n - k) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  simp only [QProb.Equiv, QProb.scale, QProb.mul, qpow_num, qpow_den,
    binomTerm, Nat.mul_pow]
  rw [hp, hq]
  ac_rfl

/-- The binomial theorem over arbitrary nonnegative rational presentations. -/
theorem qprob_binomial_theorem (p q : QProb) (n : Nat) :
    QProb.Equiv
      (QProb.listSum ((List.range (n + 1)).map (fun k =>
        QProb.scale (binom n k) (QProb.mul (qpow p k) (qpow q (n - k))))))
      (qpow (QProb.add p q) n) := by
  let D := (p.den * q.den) ^ n
  have hD : 0 < D := Nat.pow_pos (Nat.mul_pos p.den_pos q.den_pos)
  refine QProb.equiv_trans (QProb.listSum_map_congr (List.range (n + 1)) _
    (fun k => (⟨binomTerm n (p.num * q.den) (q.num * p.den) k, D, hD⟩ : QProb))
    (fun k => ?_)) ?_
  · by_cases hk : k ≤ n
    · exact qprob_binomial_term p q n k hk
    · have hz : binom n k = 0 := binom_eq_zero_of_lt (by omega)
      simp only [QProb.Equiv, QProb.scale, binomTerm, hz, Nat.zero_mul]
  · have hmap : (List.range (n + 1)).map
        (fun k => (⟨binomTerm n (p.num * q.den) (q.num * p.den) k, D, hD⟩ : QProb)) =
        ((List.range (n + 1)).map (binomTerm n (p.num * q.den) (q.num * p.den))).map
          (fun value => (⟨value, D, hD⟩ : QProb)) := by simp only [List.map_map, Function.comp_def]
    rw [hmap]
    refine QProb.equiv_trans (QProb.listSum_mk_same_den D hD _) ?_
    rw [sum_map_range_natSum, binomial_theorem]
    simp only [QProb.Equiv, qpow_num, qpow_den, QProb.add, D]

theorem rationalIntegral_weight_map (atoms : List (Ω × Nat)) (encode : Ω → X)
    (factor : Nat) (f : X → QProb) :
    QProb.Equiv
      (rationalIntegral (atoms.map (fun atom => (encode atom.1, factor * atom.2))) f)
      (QProb.scale factor (rationalIntegral atoms (fun value => f (encode value)))) := by
  simp only [rationalIntegral, List.map_map, Function.comp_def]
  refine QProb.equiv_trans (QProb.listSum_map_congr atoms _
    (fun atom => QProb.mul (QProb.ofNat factor) (QProb.scale atom.2 (f (encode atom.1))))
    (fun atom => ?_)) ?_
  · simp only [QProb.Equiv, QProb.scale, QProb.mul, QProb.ofNat, Nat.one_mul]
    ac_rfl
  · refine QProb.equiv_trans (q := QProb.mul (QProb.ofNat factor)
      (QProb.listSum (atoms.map (fun atom => QProb.scale atom.2 (f (encode atom.1)))))) ?_ ?_
    · simpa only [List.map_map, Function.comp_def] using QProb.equiv_symm
        (QProb.mul_listSum (QProb.ofNat factor)
          (atoms.map (fun atom => QProb.scale atom.2 (f (encode atom.1)))))
    · simp only [QProb.Equiv, QProb.mul, QProb.ofNat, QProb.scale, Nat.one_mul]

theorem rationalIntegral_mul_left (atoms : List (Ω × Nat)) (factor : QProb) (f : Ω → QProb) :
    QProb.Equiv (rationalIntegral atoms (fun value => QProb.mul factor (f value)))
      (QProb.mul factor (rationalIntegral atoms f)) := by
  refine QProb.equiv_trans (QProb.listSum_map_congr atoms _
    (fun atom => QProb.mul factor (QProb.scale atom.2 (f atom.1)))
    (fun atom => ?_)) ?_
  · simp only [QProb.Equiv, QProb.scale, QProb.mul]; ac_rfl
  · simpa only [rationalIntegral, List.map_map, Function.comp_def] using
      QProb.equiv_symm (QProb.mul_listSum factor
        (atoms.map (fun atom => QProb.scale atom.2 (f atom.1))))

theorem multinomial_generating_integral (trials : Nat) (weights : List Nat) (args : List QProb)
    (dimension : args.length = weights.length) :
    QProb.Equiv (rationalIntegral (multinomialAtoms trials weights) (multivariateMonomial args))
      (qpow (weightedArgument weights args) trials) := by
  induction weights generalizing trials args with
  | nil =>
      cases args with
      | cons arg args => simp only [List.length_cons, List.length_nil] at dimension; omega
      | nil =>
          cases trials with
          | zero =>
              simp [multinomialAtoms, rationalIntegral, multivariateMonomial,
                qpow, QProb.listSum, QProb.Equiv, QProb.add, QProb.scale,
                QProb.one, QProb.zero]
          | succ trials =>
              have hn : trials + 1 ≠ 0 := Nat.ne_of_gt (Nat.succ_pos trials)
              simp only [multinomialAtoms, if_neg hn, rationalIntegral, List.map_nil,
                QProb.listSum, weightedArgument, QProb.Equiv, QProb.zero, qpow_num,
                Nat.zero_pow (Nat.succ_pos trials), Nat.zero_mul]
  | cons weight rest ih =>
      cases args with
      | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
      | cons arg args =>
          have hd : args.length = rest.length := Nat.succ.inj dimension
          have row (used : Nat) : QProb.Equiv
              (rationalIntegral
                ((multinomialAtoms (trials - used) rest).map (fun atom =>
                  (used :: atom.1, binom trials used * weight ^ used * atom.2)))
                (multivariateMonomial (arg :: args)))
              (QProb.scale (binom trials used)
                (QProb.mul (qpow (QProb.scale weight arg) used)
                  (qpow (weightedArgument rest args) (trials - used)))) := by
            refine QProb.equiv_trans (rationalIntegral_weight_map _
              (fun counts => used :: counts) (binom trials used * weight ^ used) _) ?_
            refine QProb.equiv_trans (QProb.scale_congr _
              (rationalIntegral_mul_left _ (qpow arg used) (multivariateMonomial args))) ?_
            refine QProb.equiv_trans (QProb.scale_congr _ (QProb.mul_congr (QProb.equiv_refl _)
              (ih (trials - used) args hd))) ?_
            simp only [QProb.Equiv, QProb.scale, QProb.mul, qpow_num, qpow_den, Nat.mul_pow]
            ac_rfl
          simp only [multinomialAtoms, rationalIntegral, List.map_flatMap]
          refine QProb.equiv_trans (QProb.listSum_flatMap (List.range (trials + 1)) _) ?_
          exact QProb.equiv_trans (QProb.listSum_map_congr (List.range (trials + 1)) _ _ row)
            (qprob_binomial_theorem (QProb.scale weight arg) (weightedArgument rest args) trials)

theorem div_qpow_ofNat (p : QProb) (d n : Nat) (positive : 0 < d) :
    QProb.Equiv (QProb.div (qpow p n) (QProb.ofNat (d ^ n)) (Nat.pow_pos positive))
      (qpow (QProb.div p (QProb.ofNat d) positive) n) := by
  simp only [QProb.Equiv, QProb.div, QProb.ofNat, qpow_num, qpow_den,
    Nat.mul_pow, Nat.mul_one]

/-- The multivariate multinomial PGF is the trial power of its categorical
linear form, for any matching list of nonnegative rational arguments. -/
theorem multinomial_multivariate_pgf (trials : Nat) (weights : List Nat)
    (positive : 0 < weights.sum) (args : List QProb)
    (dimension : args.length = weights.length) :
    QProb.Equiv (multivariatePGF (multinomialDistro trials weights positive) args)
      (qpow (QProb.div (weightedArgument weights args) (QProb.ofNat weights.sum) positive) trials) := by
  have hd : QProb.Equiv (QProb.ofNat (multinomialDistro trials weights positive).record.den)
      (QProb.ofNat (weights.sum ^ trials)) := by
    simp only [QProb.Equiv, QProb.ofNat, multinomial_den, Nat.mul_one]
  have h := QProb.div_congr (multinomial_generating_integral trials weights args dimension)
    hd (multinomialDistro trials weights positive).record.den_pos (Nat.pow_pos positive)
  exact QProb.equiv_trans h (div_qpow_ofNat (weightedArgument weights args) weights.sum trials positive)

def weightedNatArgument : List Nat → List Nat → Nat
  | weight :: weights, arg :: args => weight * arg + weightedNatArgument weights args
  | _, _ => 0

theorem weightedArgument_ofNat (weights args : List Nat) :
    QProb.Equiv (weightedArgument weights (args.map QProb.ofNat))
      (QProb.ofNat (weightedNatArgument weights args)) := by
  induction weights generalizing args with
  | nil => exact QProb.equiv_refl _
  | cons weight weights ih =>
      cases args with
      | nil => exact QProb.equiv_refl _
      | cons arg args =>
          refine QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl _) (ih args)) ?_
          simp only [weightedNatArgument, QProb.Equiv, QProb.add, QProb.scale,
            QProb.ofNat, Nat.mul_one]

/-- Whole-number arguments are an inexpensive specialization of the
general rational theorem. -/
theorem multinomial_multivariate_pgf_ofNat (trials : Nat) (weights : List Nat)
    (positive : 0 < weights.sum) (args : List Nat)
    (dimension : args.length = weights.length) :
    QProb.Equiv (multivariatePGF (multinomialDistro trials weights positive) (args.map QProb.ofNat))
      ⟨weightedNatArgument weights args ^ trials, weights.sum ^ trials, Nat.pow_pos positive⟩ := by
  refine QProb.equiv_trans (multinomial_multivariate_pgf trials weights positive
    (args.map QProb.ofNat) (by simpa only [List.length_map] using dimension)) ?_
  refine QProb.equiv_trans (qpow_congr (QProb.div_congr (weightedArgument_ofNat weights args)
    (QProb.equiv_refl _) positive positive) trials) ?_
  simp only [QProb.Equiv, qpow_num, qpow_den, QProb.div, QProb.ofNat, Nat.mul_one, Nat.one_mul]

end Thesis.Probability.Distros
