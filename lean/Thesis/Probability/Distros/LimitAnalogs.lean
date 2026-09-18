import Thesis.Probability.Distros.Binomial

namespace Thesis
namespace Probability
namespace Distros

/-!
Finite counterparts of the classical limiting distros.

No constructor here is a real density.  Each named object is a finite urn,
presented as a `Distro` or `NatDistro`.

* `discreteGaussianDistro` is the lattice Gaussian on the centred window
  `Fin (2 * radius + 1)`, with weight `base^(k - radius)²`.  This is the
  finite object whose un-normalised shape is the Gaussian kernel
  `q^{x²}` on a lattice, without introducing `ℝ`.
* `deMoivreLatticeDistro` is the de Moivre special case: a binomial success
  count.  Its large-`n` shape is the ordinary Gaussian, but it is a
  binomial distro, not an alias of the `q^{k²}` window.
* `chiSquaredDistro` is the law of the sum of squared centred coordinates
  of `df` independent lattice Gaussians — the finite counterpart of χ² with
  `df` degrees of freedom.  The two-fold constructor is `df = 2`.
* `betaBinomialDistro` is the Pólya / beta-binomial urn, the finite
  counterpart of a beta mixture of Bernoulli trials.
* `negativeBinomialDistro` is a truncated negative binomial, the finite
  counterpart of a gamma-Poisson mixture.  The `0 < successes` hypothesis
  is used as the `r - 1` shift in the Pascal-triangle term.  Its
  whole-number PGF is the ratio of `nbSum` generating sums after
  substituting `falseWeight * s`.  The same closed form holds at a general
  nonnegative rational after homogenising `nbSum` against `s.den`.  The
  right-censored sibling keeps ordinary occupancy weights on
  `{0, …, cap - 1}` and lumps the tail
  `falseWeight^{cap+1} ∑_{s < r} C(cap + s, s) trueWeight^s` onto the last
  cell.
-/

open Combinatorics

theorem radius_lt_window (radius : Nat) :
    radius < 2 * radius + 1 := by
  omega

/-- Lattice Gaussian weight `base^(k - radius)²` on the centred window
of length `2 * radius + 1`. -/
def discreteGaussianWeight (radius base : Nat)
    (k : Fin (2 * radius + 1)) : Nat :=
  base ^ natSqDiff k.val radius

theorem discreteGaussianWeight_center (radius base : Nat) :
    discreteGaussianWeight radius base ⟨radius, radius_lt_window radius⟩ = 1 := by
  simp [discreteGaussianWeight, natSqDiff]

theorem discreteGaussianWeight_sum_pos (radius base : Nat) :
    0 < natSum (2 * radius + 1)
        (finWeight (discreteGaussianWeight radius base)) := by
  have hterm :
      0 < finWeight (discreteGaussianWeight radius base) radius := by
    have hlt : radius < 2 * radius + 1 := radius_lt_window radius
    simp [finWeight, hlt, discreteGaussianWeight_center]
  exact natSum_pos_of_term (radius_lt_window radius) hterm

/-- Lattice Gaussian distro: `q^{k²}` on a finite centred window. -/
def discreteGaussianDistro (radius base : Nat) :
    Distro (Fin (2 * radius + 1)) where
  record :=
    ofFinWeights (2 * radius + 1) (discreteGaussianWeight radius base)
      (discreteGaussianWeight_sum_pos radius base)

/-- Lattice Gaussian as a Nat-valued distro, embedding by the window index. -/
def discreteGaussianNatDistro (radius base : Nat) :
    NatDistro (Fin (2 * radius + 1)) :=
  ofFin (2 * radius)
    (discreteGaussianDistro radius base).record

theorem discreteGaussian_den (radius base : Nat) :
    (discreteGaussianDistro radius base).record.den =
      natSum (2 * radius + 1)
        (finWeight (discreteGaussianWeight radius base)) := by
  simp [discreteGaussianDistro, ofFinWeights, totalMass_finWeighted]

theorem discreteGaussian_pmf (radius base : Nat)
    (k : Fin (2 * radius + 1)) :
    QProb.Equiv
      ((discreteGaussianDistro radius base).pmf k)
      ⟨discreteGaussianWeight radius base k,
        (discreteGaussianDistro radius base).record.den,
        (discreteGaussianDistro radius base).record.den_pos⟩ := by
  simp [Distro.pmf, discreteGaussianDistro, ofFinWeights,
    FiniteProbRecord.probVal, QProb.Equiv, eventMass_finWeighted_singleton]

/-- The lattice Gaussian is symmetric about `radius`, so its Nat-shifted
mean is the window centre.  Variance of this embedding is the variance of
the signed lattice coordinate. -/
theorem discreteGaussian_mean (radius base : Nat) :
    QProb.Equiv
      (mean (discreteGaussianNatDistro radius base))
      (QProb.ofNat radius) := by
  have hden := discreteGaussian_den radius base
  have hsym :
      forall k, k ≤ 2 * radius →
        (base : Nat) ^ natSqDiff (2 * radius - k) radius =
          base ^ natSqDiff k radius := by
    intro k hk
    rw [natSqDiff_reflect radius k hk]
  have hcenter :=
    natSum_symm_center radius
      (fun k => base ^ natSqDiff k radius) hsym
  have hsum :
      weightedSum (natAtoms (discreteGaussianNatDistro radius base)) =
        radius *
          natSum (2 * radius + 1)
            (finWeight (discreteGaussianWeight radius base)) := by
    simp [natAtoms, discreteGaussianNatDistro, ofFin, discreteGaussianDistro,
      ofFinWeights]
    have hfin :=
      weightedSum_finWeighted (2 * radius + 1)
        (discreteGaussianWeight radius base)
    rw [hfin]
    have hcongr :
        natSum (2 * radius + 1) (fun k =>
            k * finWeight (discreteGaussianWeight radius base) k) =
          natSum (2 * radius + 1) (fun k =>
            k * base ^ natSqDiff k radius) := by
      apply natSum_congr
      intro k hk
      simp [finWeight, discreteGaussianWeight, hk]
    have htotal :
        natSum (2 * radius + 1)
            (finWeight (discreteGaussianWeight radius base)) =
          natSum (2 * radius + 1) (fun k =>
            base ^ natSqDiff k radius) := by
      apply natSum_congr
      intro k hk
      simp [finWeight, discreteGaussianWeight, hk]
    rw [hcongr, hcenter, htotal]
  simp [mean, rawMoment, QProb.Equiv, QProb.ofNat, weightedPowSum_one]
  rw [hsum]
  exact congrArg (fun d => radius * d) hden.symm

/-- de Moivre lattice law: binomial success count, the classical finite
Gaussian precursor.  It is recorded separately from the `q^{k²}` window. -/
def deMoivreLatticeDistro (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    NatDistro (Fin (trials + 1)) :=
  binomialNatDistro trials trueWeight falseWeight positive

/-- One more squared coordinate still fits in the `df + 1` window. -/
theorem natSqDiff_cons_lt (df radius : Nat)
    (s : Fin (df * radius * radius + 1))
    (x : Fin (2 * radius + 1)) :
    s.val + natSqDiff x.val radius <
      (df + 1) * radius * radius + 1 := by
  have hs : s.val ≤ df * radius * radius := Nat.le_of_lt_succ s.isLt
  have hx := natSqDiff_window radius x.val x.isLt
  have hsum := Nat.add_le_add hs hx
  have hmul :
      df * radius * radius + radius * radius =
        (df + 1) * radius * radius := by
    have hleft : df * radius * radius = df * (radius * radius) :=
      Nat.mul_assoc df radius radius
    have hright : (df + 1) * radius * radius =
        (df + 1) * (radius * radius) :=
      Nat.mul_assoc (df + 1) radius radius
    rw [hleft, hright, Nat.succ_mul]
  exact Nat.lt_succ_of_le (Nat.le_trans hsum (Nat.le_of_eq hmul))

/-- Independent product of `df` lattice Gaussians, mapped to the sum of
squared centred coordinates.  The `df = 0` record is the unit urn on `{0}`. -/
def chiSquaredRecord (df radius base : Nat) :
    FiniteProbRecord (Fin (df * radius * radius + 1)) :=
  match df with
  | 0 =>
      { atoms := [(⟨0, by simp⟩, 1)]
        den := 1
        den_pos := Nat.succ_pos 0
        total_mass := rfl }
  | df + 1 =>
      ((chiSquaredRecord df radius base).product
          (discreteGaussianDistro radius base).record).map
        fun pair =>
          ⟨pair.1.val + natSqDiff pair.2.val radius,
            natSqDiff_cons_lt df radius pair.1 pair.2⟩

/-- Chi-squared counterpart: sum of squared centred coordinates of `df`
independent lattice Gaussians. -/
def chiSquaredDistro (df radius base : Nat) :
    NatDistro (Fin (df * radius * radius + 1)) :=
  ofFin (df * radius * radius) (chiSquaredRecord df radius base)

theorem chiSquaredRecord_den (df radius base : Nat) :
    (chiSquaredRecord df radius base).den =
      (discreteGaussianDistro radius base).record.den ^ df := by
  induction df with
  | zero =>
      simp [chiSquaredRecord, Nat.pow_zero]
  | succ df ih =>
      simp [chiSquaredRecord, FiniteProbRecord.map, FiniteProbRecord.product, ih]
      exact (Nat.pow_succ _ _).symm

theorem chiSquared_den (df radius base : Nat) :
    (chiSquaredDistro df radius base).distro.record.den =
      (discreteGaussianDistro radius base).record.den ^ df := by
  simpa [chiSquaredDistro, ofFin] using
    chiSquaredRecord_den df radius base

/-- Beta-binomial / Pólya weights. -/
def betaBinomialWeight (trials α β : Nat) (k : Fin (trials + 1)) : Nat :=
  binom trials k.val * risingFactorial α k.val *
    risingFactorial β (trials - k.val)

theorem risingFactorial_pos (a k : Nat) (ha : 0 < a) :
    0 < risingFactorial a k := by
  induction k with
  | zero => simp [risingFactorial]
  | succ k ih =>
      simp [risingFactorial]
      exact Nat.mul_pos (Nat.add_pos_left ha k) ih

/-- Beta-binomial distro, the finite Pólya-urn counterpart of a beta mixture. -/
def betaBinomialDistro (trials α β : Nat)
    (_hα : 0 < α) (hβ : 0 < β) : Distro (Fin (trials + 1)) where
  record :=
    have hpos : 0 < natSum (trials + 1)
        (finWeight (betaBinomialWeight trials α β)) := by
      have h0 :
          0 < finWeight (betaBinomialWeight trials α β) 0 := by
        simp [finWeight, betaBinomialWeight, binom_zero_right,
          risingFactorial_zero]
        exact risingFactorial_pos β trials hβ
      have hle :
          finWeight (betaBinomialWeight trials α β) 0 ≤
            natSum (trials + 1)
              (finWeight (betaBinomialWeight trials α β)) := by
        rw [natSum_head]
        exact Nat.le_add_right _ _
      exact Nat.lt_of_lt_of_le h0 hle
    ofFinWeights (trials + 1) (betaBinomialWeight trials α β) hpos

def betaBinomialNatDistro (trials α β : Nat)
    (hα : 0 < α) (hβ : 0 < β) : NatDistro (Fin (trials + 1)) :=
  ofFin trials (betaBinomialDistro trials α β hα hβ).record

theorem betaBinomial_pmf (trials α β : Nat)
    (hα : 0 < α) (hβ : 0 < β) (k : Fin (trials + 1)) :
    QProb.Equiv
      ((betaBinomialDistro trials α β hα hβ).pmf k)
      ⟨betaBinomialWeight trials α β k,
        (betaBinomialDistro trials α β hα hβ).record.den,
        (betaBinomialDistro trials α β hα hβ).record.den_pos⟩ := by
  simp [Distro.pmf, betaBinomialDistro, ofFinWeights, FiniteProbRecord.probVal,
    QProb.Equiv, eventMass_finWeighted_singleton]

/-- Truncated negative-binomial weights: failures before `successes`
true outcomes, restricted to `{0, ..., cap}`. -/
def negativeBinomialWeight (successes cap trueWeight falseWeight : Nat)
    (k : Fin (cap + 1)) : Nat :=
  binom (k.val + successes - 1) k.val *
    trueWeight ^ successes * falseWeight ^ k.val

/-- The truncated negative-binomial normaliser is a success-power times
the generating sum `nbSum`.  The `0 < successes` hypothesis is the
`r - 1` shift that matches the Pascal triangle to `nbSum`. -/
theorem negativeBinomialWeight_sum
    (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) :
    natSum (cap + 1)
        (finWeight (negativeBinomialWeight successes cap
          trueWeight falseWeight)) =
      trueWeight ^ successes *
        nbSum successes falseWeight (cap + 1) := by
  have hpred :=
    nbSum_pred successes falseWeight (cap + 1) hsuccesses
  have hcongr :
      natSum (cap + 1)
          (finWeight (negativeBinomialWeight successes cap
            trueWeight falseWeight)) =
        natSum (cap + 1) (fun k =>
          trueWeight ^ successes *
            (binom (k + (successes - 1)) k * falseWeight ^ k)) := by
    apply natSum_congr
    intro k hk
    have hshift : k + successes - 1 = k + (successes - 1) :=
      Nat.add_sub_assoc (Nat.succ_le_of_lt hsuccesses) k
    simp [finWeight, negativeBinomialWeight, hk, hshift]
    ac_rfl
  rw [hcongr, natSum_mul_left, ← hpred]

/-- Truncated negative binomial, the finite gamma-Poisson counterpart. -/
def negativeBinomialDistro (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    Distro (Fin (cap + 1)) where
  record :=
    have hpos : 0 < natSum (cap + 1)
        (finWeight (negativeBinomialWeight successes cap
          trueWeight falseWeight)) := by
      rw [negativeBinomialWeight_sum successes cap trueWeight falseWeight
        hsuccesses]
      exact Nat.mul_pos (Nat.pow_pos htrue)
        (nbSum_pos successes falseWeight (cap + 1) hsuccesses
          (Nat.succ_pos cap))
    ofFinWeights (cap + 1)
      (negativeBinomialWeight successes cap trueWeight falseWeight) hpos

def negativeBinomialNatDistro (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    NatDistro (Fin (cap + 1)) :=
  ofFin cap (negativeBinomialDistro successes cap trueWeight falseWeight
    hsuccesses htrue).record

theorem negativeBinomial_pmf (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight)
    (k : Fin (cap + 1)) :
    QProb.Equiv
      ((negativeBinomialDistro successes cap trueWeight falseWeight
        hsuccesses htrue).pmf k)
      ⟨negativeBinomialWeight successes cap trueWeight falseWeight k,
        (negativeBinomialDistro successes cap trueWeight falseWeight
          hsuccesses htrue).record.den,
        (negativeBinomialDistro successes cap trueWeight falseWeight
          hsuccesses htrue).record.den_pos⟩ := by
  simp [Distro.pmf, negativeBinomialDistro, ofFinWeights,
    FiniteProbRecord.probVal, QProb.Equiv, eventMass_finWeighted_singleton]

/-- The constructor denominator is the same `nbSum` normaliser. -/
theorem negativeBinomial_den
    (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    (negativeBinomialDistro successes cap trueWeight falseWeight
        hsuccesses htrue).record.den =
      trueWeight ^ successes *
        nbSum successes falseWeight (cap + 1) := by
  simp [negativeBinomialDistro, ofFinWeights, totalMass_finWeighted]
  exact negativeBinomialWeight_sum successes cap trueWeight falseWeight
    hsuccesses

/-- Scaling the truncated negative-binomial weight by `s^k` substitutes
`falseWeight * s` for the failure weight. -/
theorem negativeBinomialWeight_scale_pow
    (successes cap trueWeight falseWeight s : Nat)
    (k : Fin (cap + 1)) :
    negativeBinomialWeight successes cap trueWeight falseWeight k * s ^ k.val =
      negativeBinomialWeight successes cap trueWeight (falseWeight * s) k := by
  simp [negativeBinomialWeight, Nat.mul_pow]
  ac_rfl

/-- The truncated negative-binomial PGF, evaluated at a whole number `s`,
is the ratio of `nbSum` generating sums after substituting
`falseWeight * s`. -/
theorem negativeBinomial_pgf_ofNat
    (successes cap trueWeight falseWeight s : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    QProb.Equiv
      (pgf (negativeBinomialNatDistro successes cap trueWeight falseWeight
          hsuccesses htrue)
        (QProb.ofNat s))
      ⟨trueWeight ^ successes *
          nbSum successes (falseWeight * s) (cap + 1),
        trueWeight ^ successes *
          nbSum successes falseWeight (cap + 1),
        Nat.mul_pos (Nat.pow_pos htrue)
          (nbSum_pos successes falseWeight (cap + 1) hsuccesses
            (Nat.succ_pos cap))⟩ := by
  have hatoms :
      (negativeBinomialNatDistro successes cap trueWeight falseWeight
          hsuccesses htrue).distro.record.atoms =
        finWeighted (cap + 1)
          (negativeBinomialWeight successes cap trueWeight falseWeight) := by
    simp [negativeBinomialNatDistro, ofFin, negativeBinomialDistro,
      ofFinWeights]
  have hnum :
      QProb.Equiv
        (QProb.listSum
          ((negativeBinomialNatDistro successes cap trueWeight falseWeight
              hsuccesses htrue).distro.record.atoms.map fun atom =>
            QProb.scale atom.2
              (qpow (QProb.ofNat s)
                ((negativeBinomialNatDistro successes cap trueWeight falseWeight
                    hsuccesses htrue).embed atom.1))))
        (QProb.ofNat
          (trueWeight ^ successes *
            nbSum successes (falseWeight * s) (cap + 1))) := by
    rw [hatoms]
    have hsum :=
      listSum_scale_qpow_finWeighted (cap + 1)
        (negativeBinomialWeight successes cap trueWeight falseWeight) s
    have hterm :
        natSum (cap + 1) (fun i =>
            finWeight (negativeBinomialWeight successes cap trueWeight
              falseWeight) i * s ^ i) =
          trueWeight ^ successes *
            nbSum successes (falseWeight * s) (cap + 1) := by
      have hcongr :
          natSum (cap + 1) (fun i =>
              finWeight (negativeBinomialWeight successes cap trueWeight
                falseWeight) i * s ^ i) =
            natSum (cap + 1)
              (finWeight (negativeBinomialWeight successes cap trueWeight
                (falseWeight * s))) := by
        apply natSum_congr
        intro i hi
        simp [finWeight, hi]
        exact negativeBinomialWeight_scale_pow successes cap trueWeight
          falseWeight s ⟨i, hi⟩
      rw [hcongr, negativeBinomialWeight_sum successes cap trueWeight
        (falseWeight * s) hsuccesses]
    exact QProb.equiv_trans hsum (by
      simp [QProb.Equiv, QProb.ofNat]
      exact hterm)
  have hden :
      QProb.Equiv
        (QProb.ofNat
          (negativeBinomialNatDistro successes cap trueWeight falseWeight
            hsuccesses htrue).distro.record.den)
        (QProb.ofNat
          (trueWeight ^ successes *
            nbSum successes falseWeight (cap + 1))) := by
    simp [QProb.Equiv, QProb.ofNat]
    exact negativeBinomial_den successes cap trueWeight falseWeight
      hsuccesses htrue
  have hdiv :=
    QProb.div_congr hnum hden
      (negativeBinomialNatDistro successes cap trueWeight falseWeight
        hsuccesses htrue).distro.record.den_pos
      (Nat.mul_pos (Nat.pow_pos htrue)
        (nbSum_pos successes falseWeight (cap + 1) hsuccesses
          (Nat.succ_pos cap)))
  refine QProb.equiv_trans (by simpa [pgf] using hdiv) ?_
  simp [QProb.div, QProb.ofNat, QProb.Equiv]

/-- Homogenising a truncated negative-binomial weight against a common
denominator power substitutes `falseWeight * num` in the generating base. -/
theorem negativeBinomialWeight_homogenize
    (successes cap trueWeight falseWeight num den : Nat)
    (k : Fin (cap + 1)) :
    negativeBinomialWeight successes cap trueWeight falseWeight k *
        num ^ k.val * den ^ (cap - k.val) =
      trueWeight ^ successes *
        binom (k.val + successes - 1) k.val *
          (falseWeight * num) ^ k.val * den ^ (cap - k.val) := by
  simp [negativeBinomialWeight, Nat.mul_pow]
  ac_rfl

/-- The truncated negative-binomial PGF at a nonnegative rational `s` is
the ratio of a homogenised `nbSum` to the ordinary `nbSum` normaliser. -/
theorem negativeBinomial_pgf
    (successes cap trueWeight falseWeight : Nat) (s : QProb)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    QProb.Equiv
      (pgf (negativeBinomialNatDistro successes cap trueWeight falseWeight
          hsuccesses htrue)
        s)
      (QProb.div
        ⟨trueWeight ^ successes *
            nbSumHomog successes (falseWeight * s.num) s.den cap,
          s.den ^ cap,
          Nat.pow_pos s.den_pos⟩
        (QProb.ofNat
          (trueWeight ^ successes *
            nbSum successes falseWeight (cap + 1)))
        (Nat.mul_pos (Nat.pow_pos htrue)
          (nbSum_pos successes falseWeight (cap + 1) hsuccesses
            (Nat.succ_pos cap)))) := by
  have hatoms :
      (negativeBinomialNatDistro successes cap trueWeight falseWeight
          hsuccesses htrue).distro.record.atoms =
        finWeighted (cap + 1)
          (negativeBinomialWeight successes cap trueWeight falseWeight) := by
    simp [negativeBinomialNatDistro, ofFin, negativeBinomialDistro,
      ofFinWeights]
  have hnum :
      QProb.Equiv
        (QProb.listSum
          ((negativeBinomialNatDistro successes cap trueWeight falseWeight
              hsuccesses htrue).distro.record.atoms.map fun atom =>
            QProb.scale atom.2
              (qpow s
                ((negativeBinomialNatDistro successes cap trueWeight falseWeight
                    hsuccesses htrue).embed atom.1))))
        ⟨trueWeight ^ successes *
            nbSumHomog successes (falseWeight * s.num) s.den cap,
          s.den ^ cap,
          Nat.pow_pos s.den_pos⟩ := by
    rw [hatoms]
    have hsum :=
      listSum_scale_qpow_finWeighted_qprob cap
        (negativeBinomialWeight successes cap trueWeight falseWeight) s
    have hterm :
        natSum (cap + 1) (fun i =>
            finWeight (negativeBinomialWeight successes cap trueWeight
              falseWeight) i * s.num ^ i * s.den ^ (cap - i)) =
          trueWeight ^ successes *
            nbSumHomog successes (falseWeight * s.num) s.den cap := by
      have hcongr :
          natSum (cap + 1) (fun i =>
              finWeight (negativeBinomialWeight successes cap trueWeight
                falseWeight) i * s.num ^ i * s.den ^ (cap - i)) =
            natSum (cap + 1) (fun i =>
              trueWeight ^ successes *
                binom (i + successes - 1) i *
                  (falseWeight * s.num) ^ i * s.den ^ (cap - i)) := by
        apply natSum_congr
        intro i hi
        simp [finWeight, hi]
        exact negativeBinomialWeight_homogenize successes cap trueWeight
          falseWeight s.num s.den ⟨i, hi⟩
      rw [hcongr]
      have hfactor :
          natSum (cap + 1) (fun i =>
            trueWeight ^ successes * binom (i + successes - 1) i *
              (falseWeight * s.num) ^ i * s.den ^ (cap - i)) =
          natSum (cap + 1) (fun i =>
            trueWeight ^ successes *
              (binom (i + successes - 1) i *
                (falseWeight * s.num) ^ i * s.den ^ (cap - i))) := by
        apply natSum_congr
        intro i _
        simp [Nat.mul_assoc]
      rw [hfactor, natSum_mul_left]
      rfl
    refine QProb.equiv_trans hsum ?_
    simp [QProb.Equiv, hterm]
  have hden :
      QProb.Equiv
        (QProb.ofNat
          (negativeBinomialNatDistro successes cap trueWeight falseWeight
            hsuccesses htrue).distro.record.den)
        (QProb.ofNat
          (trueWeight ^ successes *
            nbSum successes falseWeight (cap + 1))) := by
    simp [QProb.Equiv, QProb.ofNat]
    exact negativeBinomial_den successes cap trueWeight falseWeight
      hsuccesses htrue
  have hdiv :=
    QProb.div_congr hnum hden
      (negativeBinomialNatDistro successes cap trueWeight falseWeight
        hsuccesses htrue).distro.record.den_pos
      (Nat.mul_pos (Nat.pow_pos htrue)
        (nbSum_pos successes falseWeight (cap + 1) hsuccesses
          (Nat.succ_pos cap)))
  simpa [pgf] using hdiv

/-- Negative-binomial tail after `cap` failures: sequences that record
`cap + 1` failures with fewer than `successes` successes, ending in a
failure.  For one success this is `falseWeight^{cap+1}`. -/
def negativeBinomialCensorTail
    (successes cap trueWeight falseWeight : Nat) : Nat :=
  falseWeight ^ (cap + 1) *
    natSum successes (fun s => binom (cap + s) s * trueWeight ^ s)

/-- Right-censored negative-binomial weights: ordinary occupancy on
`{0, …, cap - 1}`, and on the last cell the mass at `cap` together with
`negativeBinomialCensorTail`. -/
def negativeBinomialCensoredWeight
    (successes cap trueWeight falseWeight : Nat)
    (k : Fin (cap + 1)) : Nat :=
  if k.val < cap then
    negativeBinomialWeight successes cap trueWeight falseWeight k
  else
    negativeBinomialWeight successes cap trueWeight falseWeight k +
      negativeBinomialCensorTail successes cap trueWeight falseWeight

theorem negativeBinomialCensoredWeight_sum
    (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) :
    natSum (cap + 1)
        (finWeight (negativeBinomialCensoredWeight successes cap
          trueWeight falseWeight)) =
      trueWeight ^ successes *
          nbSum successes falseWeight (cap + 1) +
        negativeBinomialCensorTail successes cap trueWeight falseWeight := by
  have hcongr :
      natSum (cap + 1)
          (finWeight (negativeBinomialCensoredWeight successes cap
            trueWeight falseWeight)) =
        natSum (cap + 1)
            (finWeight (negativeBinomialWeight successes cap
              trueWeight falseWeight)) +
          negativeBinomialCensorTail successes cap trueWeight falseWeight := by
    rw [natSum_succ,
      natSum_succ (n := cap)
        (finWeight (negativeBinomialWeight successes cap
          trueWeight falseWeight))]
    have hprefix :
        natSum cap
            (finWeight (negativeBinomialCensoredWeight successes cap
              trueWeight falseWeight)) =
          natSum cap
            (finWeight (negativeBinomialWeight successes cap
              trueWeight falseWeight)) := by
      apply natSum_congr
      intro i hi
      have hfin : i < cap + 1 := Nat.lt_succ_of_lt hi
      simp [finWeight, negativeBinomialCensoredWeight, hfin, hi]
    have hlast :
        finWeight (negativeBinomialCensoredWeight successes cap
            trueWeight falseWeight) cap =
          finWeight (negativeBinomialWeight successes cap
              trueWeight falseWeight) cap +
            negativeBinomialCensorTail successes cap trueWeight
              falseWeight := by
      have hfin : cap < cap + 1 := Nat.lt_succ_self cap
      have hnlt : ¬ cap < cap := Nat.lt_irrefl cap
      simp [finWeight, negativeBinomialCensoredWeight, hfin, hnlt]
    rw [hprefix, hlast]
    ac_rfl
  rw [hcongr, negativeBinomialWeight_sum successes cap trueWeight
    falseWeight hsuccesses]

/-- Right-censored negative binomial on `{0, ..., cap}`. -/
def negativeBinomialCensoredDistro
    (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    Distro (Fin (cap + 1)) where
  record :=
    have hsum :=
      negativeBinomialCensoredWeight_sum successes cap trueWeight
        falseWeight hsuccesses
    have hpos : 0 < natSum (cap + 1)
        (finWeight (negativeBinomialCensoredWeight successes cap
          trueWeight falseWeight)) := by
      rw [hsum]
      exact Nat.lt_of_lt_of_le
        (Nat.mul_pos (Nat.pow_pos htrue)
          (nbSum_pos successes falseWeight (cap + 1) hsuccesses
            (Nat.succ_pos cap)))
        (Nat.le_add_right _ _)
    ofFinWeights (cap + 1)
      (negativeBinomialCensoredWeight successes cap trueWeight falseWeight)
      hpos

def negativeBinomialCensoredNatDistro
    (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    NatDistro (Fin (cap + 1)) :=
  ofFin cap
    (negativeBinomialCensoredDistro successes cap trueWeight falseWeight
      hsuccesses htrue).record

theorem negativeBinomialCensored_den
    (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    (negativeBinomialCensoredDistro successes cap trueWeight falseWeight
        hsuccesses htrue).record.den =
      trueWeight ^ successes *
          nbSum successes falseWeight (cap + 1) +
        negativeBinomialCensorTail successes cap trueWeight falseWeight := by
  simp [negativeBinomialCensoredDistro, ofFinWeights, totalMass_finWeighted]
  exact negativeBinomialCensoredWeight_sum successes cap trueWeight
    falseWeight hsuccesses

theorem negativeBinomialCensored_pmf
    (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight)
    (k : Fin (cap + 1)) :
    QProb.Equiv
      ((negativeBinomialCensoredDistro successes cap trueWeight falseWeight
        hsuccesses htrue).pmf k)
      ⟨negativeBinomialCensoredWeight successes cap trueWeight falseWeight k,
        (negativeBinomialCensoredDistro successes cap trueWeight falseWeight
          hsuccesses htrue).record.den,
        (negativeBinomialCensoredDistro successes cap trueWeight falseWeight
          hsuccesses htrue).record.den_pos⟩ := by
  simp [Distro.pmf, negativeBinomialCensoredDistro, ofFinWeights,
    FiniteProbRecord.probVal, QProb.Equiv, eventMass_finWeighted_singleton]

end Distros
end Probability
end Thesis
