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
  of two independent lattice Gaussians — the finite counterpart of χ² with
  two degrees of freedom.
* `betaBinomialDistro` is the Pólya / beta-binomial urn, the finite
  counterpart of a beta mixture of Bernoulli trials.
* `negativeBinomialDistro` is a truncated negative binomial, the finite
  counterpart of a gamma-Poisson mixture.  The `0 < successes` hypothesis
  is used as the `r - 1` shift in the Pascal-triangle term.  Its
  whole-number PGF is the ratio of `nbSum` generating sums after
  substituting `falseWeight * s`.
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

theorem two_natSqDiff_lt (radius : Nat)
    (x y : Fin (2 * radius + 1)) :
    natSqDiff x.val radius + natSqDiff y.val radius <
      2 * radius * radius + 1 := by
  have hx := natSqDiff_window radius x.val x.isLt
  have hy := natSqDiff_window radius y.val y.isLt
  have hsum := Nat.add_le_add hx hy
  have htwo : radius * radius + radius * radius = 2 * (radius * radius) :=
    (Nat.two_mul (radius * radius)).symm
  have hassoc : 2 * radius * radius = 2 * (radius * radius) :=
    Nat.mul_assoc 2 radius radius
  have hbound : radius * radius + radius * radius = 2 * radius * radius :=
    htwo.trans hassoc.symm
  exact Nat.lt_succ_of_le (Nat.le_trans hsum (Nat.le_of_eq hbound))

/-- Chi-squared counterpart: sum of squared centred coordinates of two
independent lattice Gaussians. -/
def chiSquaredDistro (radius base : Nat) :
    NatDistro (Fin (2 * radius * radius + 1)) where
  distro :=
    let gauss := (discreteGaussianDistro radius base).record
    ⟨(gauss.product gauss).map fun pair =>
      ⟨natSqDiff pair.1.val radius + natSqDiff pair.2.val radius,
        two_natSqDiff_lt radius pair.1 pair.2⟩⟩
  embed := Fin.val

theorem chiSquared_den (radius base : Nat) :
    (chiSquaredDistro radius base).distro.record.den =
      (discreteGaussianDistro radius base).record.den *
        (discreteGaussianDistro radius base).record.den := by
  simp [chiSquaredDistro, FiniteProbRecord.map, FiniteProbRecord.product]

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

end Distros
end Probability
end Thesis
