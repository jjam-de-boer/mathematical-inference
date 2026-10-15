import Thesis.Probability.Distros.Binomial

namespace Thesis
namespace Probability
namespace Distros

/-!
Finite counterparts of the classical limiting distros.

No constructor here is a real density.  Each named object is a finite urn,
presented as a `Distro` or `NatDistro`.

* `discreteGaussianDistro` is the lattice Gaussian on the centred window
  `Fin (2 * radius + 1)`, with rational kernel `q^((k - radius)²)`.  This is the
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
  weights pad each stopped path to `cap + successes` Bernoulli trials by
  `trueWeight + falseWeight`.  Its PGF is the ratio of `nbSumHomog`
  generating sums, with that Bernoulli total retained at general rational
  arguments.  The right-censored sibling also clears the denominator of
  every tail path before placing it on the last cell.  Both versions have
  whole-number PGFs as specializations of their general rational formulas.
-/

open Combinatorics

theorem radius_lt_window (radius : Nat) :
    radius < 2 * radius + 1 := by
  omega

/-- Clear the common denominator `q.den^(radius²)` from the rational
Gaussian kernel `q^((k - radius)²)`. -/
def discreteGaussianWeight (radius : Nat) (q : QProb)
    (k : Fin (2 * radius + 1)) : Nat :=
  q.num ^ natSqDiff k.val radius *
    q.den ^ (radius * radius - natSqDiff k.val radius)

theorem discreteGaussianWeight_center (radius : Nat) (q : QProb) :
    discreteGaussianWeight radius q ⟨radius, radius_lt_window radius⟩ =
      q.den ^ (radius * radius) := by
  simp [discreteGaussianWeight, natSqDiff]

theorem discreteGaussianWeight_sum_pos (radius : Nat) (q : QProb) :
    0 < natSum (2 * radius + 1)
        (finWeight (discreteGaussianWeight radius q)) := by
  have hterm :
      0 < finWeight (discreteGaussianWeight radius q) radius := by
    have hlt : radius < 2 * radius + 1 := radius_lt_window radius
    simp [finWeight, hlt, discreteGaussianWeight_center]
    exact Nat.pow_pos q.den_pos
  exact natSum_pos_of_term (radius_lt_window radius) hterm

/-- Exact finite rational Gaussian.  The bound on `q` enforces a kernel
that decreases away from the centre; zero and one retain their limiting
point-mass and uniform interpretations. -/
def discreteGaussianDistro (radius : Nat) (q : QProb)
    (_bounded : QProb.LE q QProb.one) :
    Distro (Fin (2 * radius + 1)) where
  record :=
    ofFinWeights (2 * radius + 1) (discreteGaussianWeight radius q)
      (discreteGaussianWeight_sum_pos radius q)

/-- Lattice Gaussian as a Nat-valued distro, embedding by the window index. -/
def discreteGaussianNatDistro (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    NatDistro (Fin (2 * radius + 1)) :=
  ofFin (2 * radius)
    (discreteGaussianDistro radius q bounded).record

theorem discreteGaussian_den (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    (discreteGaussianDistro radius q bounded).record.den =
      natSum (2 * radius + 1)
        (finWeight (discreteGaussianWeight radius q)) := by
  simp [discreteGaussianDistro, ofFinWeights, totalMass_finWeighted]

theorem discreteGaussian_pmf (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one)
    (k : Fin (2 * radius + 1)) :
    QProb.Equiv
      ((discreteGaussianDistro radius q bounded).pmf k)
      ⟨discreteGaussianWeight radius q k,
        (discreteGaussianDistro radius q bounded).record.den,
        (discreteGaussianDistro radius q bounded).record.den_pos⟩ := by
  simp [Distro.pmf, discreteGaussianDistro, ofFinWeights,
    FiniteProbRecord.probVal, QProb.Equiv, eventMass_finWeighted_singleton]

/-- The lattice Gaussian is symmetric about `radius`, so its Nat-shifted
mean is the window centre.  Variance of this embedding is the variance of
the signed lattice coordinate. -/
theorem discreteGaussian_mean (radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    QProb.Equiv
      (mean (discreteGaussianNatDistro radius q bounded))
      (QProb.ofNat radius) := by
  have hden := discreteGaussian_den radius q bounded
  have hsym :
      forall k, k ≤ 2 * radius →
        q.num ^ natSqDiff (2 * radius - k) radius *
            q.den ^ (radius * radius - natSqDiff (2 * radius - k) radius) =
          q.num ^ natSqDiff k radius *
            q.den ^ (radius * radius - natSqDiff k radius) := by
    intro k hk
    rw [natSqDiff_reflect radius k hk]
  have hcenter :=
    natSum_symm_center radius
      (fun k => q.num ^ natSqDiff k radius *
        q.den ^ (radius * radius - natSqDiff k radius)) hsym
  have hsum :
      weightedSum (natAtoms (discreteGaussianNatDistro radius q bounded)) =
        radius *
          natSum (2 * radius + 1)
            (finWeight (discreteGaussianWeight radius q)) := by
    simp [natAtoms, discreteGaussianNatDistro, ofFin, discreteGaussianDistro,
      ofFinWeights]
    have hfin :=
      weightedSum_finWeighted (2 * radius + 1)
        (discreteGaussianWeight radius q)
    rw [hfin]
    have hcongr :
        natSum (2 * radius + 1) (fun k =>
            k * finWeight (discreteGaussianWeight radius q) k) =
          natSum (2 * radius + 1) (fun k =>
            k * (q.num ^ natSqDiff k radius *
              q.den ^ (radius * radius - natSqDiff k radius))) := by
      apply natSum_congr
      intro k hk
      simp [finWeight, discreteGaussianWeight, hk]
    have htotal :
        natSum (2 * radius + 1)
            (finWeight (discreteGaussianWeight radius q)) =
          natSum (2 * radius + 1) (fun k =>
            q.num ^ natSqDiff k radius *
              q.den ^ (radius * radius - natSqDiff k radius)) := by
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
def chiSquaredRecord (df radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    FiniteProbRecord (Fin (df * radius * radius + 1)) :=
  match df with
  | 0 =>
      { atoms := [(⟨0, by simp⟩, 1)]
        den := 1
        den_pos := Nat.succ_pos 0
        total_mass := rfl }
  | df + 1 =>
      ((chiSquaredRecord df radius q bounded).product
          (discreteGaussianDistro radius q bounded).record).map
        fun pair =>
          ⟨pair.1.val + natSqDiff pair.2.val radius,
            natSqDiff_cons_lt df radius pair.1 pair.2⟩

/-- Chi-squared counterpart: sum of squared centred coordinates of `df`
independent lattice Gaussians. -/
def chiSquaredDistro (df radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    NatDistro (Fin (df * radius * radius + 1)) :=
  ofFin (df * radius * radius) (chiSquaredRecord df radius q bounded)

theorem chiSquaredRecord_den (df radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    (chiSquaredRecord df radius q bounded).den =
      (discreteGaussianDistro radius q bounded).record.den ^ df := by
  induction df with
  | zero =>
      simp [chiSquaredRecord, Nat.pow_zero]
  | succ df ih =>
      simp [chiSquaredRecord, FiniteProbRecord.map, FiniteProbRecord.product, ih]
      exact (Nat.pow_succ _ _).symm

theorem chiSquared_den (df radius : Nat) (q : QProb)
    (bounded : QProb.LE q QProb.one) :
    (chiSquaredDistro df radius q bounded).distro.record.den =
      (discreteGaussianDistro radius q bounded).record.den ^ df := by
  simpa [chiSquaredDistro, ofFin] using
    chiSquaredRecord_den df radius q bounded

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

/-- Failures before `successes` Bernoulli successes, cleared to the
common trial denominator `(trueWeight + falseWeight)^(cap + successes)`. -/
def negativeBinomialWeight (successes cap trueWeight falseWeight : Nat)
    (k : Fin (cap + 1)) : Nat :=
  binom (k.val + successes - 1) k.val *
    trueWeight ^ successes * falseWeight ^ k.val *
      (trueWeight + falseWeight) ^ (cap - k.val)

theorem negativeBinomialWeight_sum
    (successes cap trueWeight falseWeight : Nat) :
    natSum (cap + 1)
        (finWeight (negativeBinomialWeight successes cap trueWeight falseWeight)) =
      trueWeight ^ successes *
        nbSumHomog successes falseWeight (trueWeight + falseWeight) cap := by
  have hcongr :
      natSum (cap + 1)
          (finWeight (negativeBinomialWeight successes cap trueWeight falseWeight)) =
        natSum (cap + 1) (fun k =>
          trueWeight ^ successes *
            (binom (k + successes - 1) k * falseWeight ^ k *
              (trueWeight + falseWeight) ^ (cap - k))) := by
    apply natSum_congr
    intro k hk
    simp [finWeight, negativeBinomialWeight, hk]
    ac_rfl
  rw [hcongr, natSum_mul_left]
  rfl

/-- The waiting time conditioned on reaching the required successes before
the failure count exceeds the finite cap. -/
def negativeBinomialDistro (successes cap trueWeight falseWeight : Nat)
    (_hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    Distro (Fin (cap + 1)) where
  record :=
    have hpos : 0 < natSum (cap + 1)
        (finWeight (negativeBinomialWeight successes cap trueWeight falseWeight)) := by
      rw [negativeBinomialWeight_sum]
      exact Nat.mul_pos (Nat.pow_pos htrue)
        (nbSumHomog_pos _ _ _ _ (Nat.add_pos_left htrue _))
    ofFinWeights (cap + 1)
      (negativeBinomialWeight successes cap trueWeight falseWeight) hpos

def negativeBinomialNatDistro (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    NatDistro (Fin (cap + 1)) :=
  ofFin cap (negativeBinomialDistro successes cap trueWeight falseWeight hsuccesses htrue).record

theorem negativeBinomial_pmf (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) (k : Fin (cap + 1)) :
    QProb.Equiv
      ((negativeBinomialDistro successes cap trueWeight falseWeight hsuccesses htrue).pmf k)
      ⟨negativeBinomialWeight successes cap trueWeight falseWeight k,
        (negativeBinomialDistro successes cap trueWeight falseWeight hsuccesses htrue).record.den,
        (negativeBinomialDistro successes cap trueWeight falseWeight hsuccesses htrue).record.den_pos⟩ := by
  simp [Distro.pmf, negativeBinomialDistro, ofFinWeights,
    FiniteProbRecord.probVal, QProb.Equiv, eventMass_finWeighted_singleton]

theorem negativeBinomial_den (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    (negativeBinomialDistro successes cap trueWeight falseWeight hsuccesses htrue).record.den =
      trueWeight ^ successes *
        nbSumHomog successes falseWeight (trueWeight + falseWeight) cap := by
  simp [negativeBinomialDistro, ofFinWeights, totalMass_finWeighted, negativeBinomialWeight_sum]

theorem negativeBinomialWeight_scale_pow
    (successes cap trueWeight falseWeight s : Nat) (k : Fin (cap + 1)) :
    negativeBinomialWeight successes cap trueWeight falseWeight k * s ^ k.val =
      binom (k.val + successes - 1) k.val * trueWeight ^ successes *
        (falseWeight * s) ^ k.val *
          (trueWeight + falseWeight) ^ (cap - k.val) := by
  simp [negativeBinomialWeight, Nat.mul_pow]
  ac_rfl

theorem negativeBinomialWeight_homogenize
    (successes cap trueWeight falseWeight num den : Nat) (k : Fin (cap + 1)) :
    negativeBinomialWeight successes cap trueWeight falseWeight k *
        num ^ k.val * den ^ (cap - k.val) =
      trueWeight ^ successes * binom (k.val + successes - 1) k.val *
        (falseWeight * num) ^ k.val *
          ((trueWeight + falseWeight) * den) ^ (cap - k.val) := by
  simp [negativeBinomialWeight, Nat.mul_pow]
  ac_rfl

theorem negativeBinomialWeight_homog_sum
    (successes cap trueWeight falseWeight num den : Nat) :
    natSum (cap + 1) (fun k =>
        finWeight (negativeBinomialWeight successes cap trueWeight falseWeight) k *
          num ^ k * den ^ (cap - k)) =
      trueWeight ^ successes * nbSumHomog successes (falseWeight * num)
        ((trueWeight + falseWeight) * den) cap := by
  have hcongr :
      natSum (cap + 1) (fun k =>
          finWeight (negativeBinomialWeight successes cap trueWeight falseWeight) k *
            num ^ k * den ^ (cap - k)) =
        natSum (cap + 1) (fun k =>
          trueWeight ^ successes *
            (binom (k + successes - 1) k * (falseWeight * num) ^ k *
              ((trueWeight + falseWeight) * den) ^ (cap - k))) := by
    apply natSum_congr
    intro k hk
    simpa [finWeight, hk, Nat.mul_assoc] using
      negativeBinomialWeight_homogenize successes cap trueWeight falseWeight num den ⟨k, hk⟩
  rw [hcongr, natSum_mul_left]
  rfl

theorem negativeBinomial_pgf (successes cap trueWeight falseWeight : Nat) (s : QProb)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    QProb.Equiv
      (pgf (negativeBinomialNatDistro successes cap trueWeight falseWeight hsuccesses htrue) s)
      ⟨trueWeight ^ successes * nbSumHomog successes (falseWeight * s.num)
          ((trueWeight + falseWeight) * s.den) cap,
        s.den ^ cap *
          (trueWeight ^ successes * nbSumHomog successes falseWeight (trueWeight + falseWeight) cap),
        Nat.mul_pos (Nat.pow_pos s.den_pos) (Nat.mul_pos (Nat.pow_pos htrue)
          (nbSumHomog_pos _ _ _ _ (Nat.add_pos_left htrue _)))⟩ := by
  have hpos : 0 < natSum (cap + 1)
      (finWeight (negativeBinomialWeight successes cap trueWeight falseWeight)) := by
    rw [negativeBinomialWeight_sum]
    exact Nat.mul_pos (Nat.pow_pos htrue)
      (nbSumHomog_pos _ _ _ _ (Nat.add_pos_left htrue _))
  have h := ofFinWeights_pgf cap
    (negativeBinomialWeight successes cap trueWeight falseWeight) hpos s
  refine QProb.equiv_trans
    (by simpa [negativeBinomialNatDistro, negativeBinomialDistro] using h) ?_
  simp [QProb.Equiv, negativeBinomialWeight_homog_sum, negativeBinomialWeight_sum]

theorem negativeBinomial_pgf_ofNat (successes cap trueWeight falseWeight s : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    QProb.Equiv
      (pgf (negativeBinomialNatDistro successes cap trueWeight falseWeight hsuccesses htrue)
        (QProb.ofNat s))
      ⟨trueWeight ^ successes * nbSumHomog successes (falseWeight * s)
          (trueWeight + falseWeight) cap,
        trueWeight ^ successes * nbSumHomog successes falseWeight (trueWeight + falseWeight) cap,
        Nat.mul_pos (Nat.pow_pos htrue)
          (nbSumHomog_pos _ _ _ _ (Nat.add_pos_left htrue _))⟩ := by
  simpa [QProb.ofNat] using
    negativeBinomial_pgf successes cap trueWeight falseWeight (QProb.ofNat s) hsuccesses htrue

/-- Paths reaching `cap + 1` failures before the requested successes.
Each variable-length terminal path is padded to `cap + successes` trials
by the same Bernoulli total, so its mass shares the occupancy denominator. -/
def negativeBinomialCensorTail (successes cap trueWeight falseWeight : Nat) : Nat :=
  falseWeight ^ (cap + 1) *
    natSum successes (fun s =>
      binom (cap + s) s * trueWeight ^ s *
        (trueWeight + falseWeight) ^ (successes - 1 - s))

def negativeBinomialCensoredWeight (successes cap trueWeight falseWeight : Nat)
    (k : Fin (cap + 1)) : Nat :=
  if k.val < cap then
    negativeBinomialWeight successes cap trueWeight falseWeight k
  else
    negativeBinomialWeight successes cap trueWeight falseWeight k +
      negativeBinomialCensorTail successes cap trueWeight falseWeight

theorem negativeBinomialCensoredWeight_sum
    (successes cap trueWeight falseWeight : Nat) :
    natSum (cap + 1)
        (finWeight (negativeBinomialCensoredWeight successes cap trueWeight falseWeight)) =
      trueWeight ^ successes * nbSumHomog successes falseWeight (trueWeight + falseWeight) cap +
        negativeBinomialCensorTail successes cap trueWeight falseWeight := by
  have hcongr :
      natSum (cap + 1)
          (finWeight (negativeBinomialCensoredWeight successes cap trueWeight falseWeight)) =
        natSum (cap + 1)
          (finWeight (negativeBinomialWeight successes cap trueWeight falseWeight)) +
            negativeBinomialCensorTail successes cap trueWeight falseWeight := by
    rw [natSum_succ, natSum_succ (n := cap)
      (finWeight (negativeBinomialWeight successes cap trueWeight falseWeight))]
    have hp :
        natSum cap (finWeight (negativeBinomialCensoredWeight successes cap trueWeight falseWeight)) =
          natSum cap (finWeight (negativeBinomialWeight successes cap trueWeight falseWeight)) := by
      apply natSum_congr
      intro k hk
      simp [finWeight, negativeBinomialCensoredWeight, hk, Nat.lt_succ_of_lt hk]
    have hl :
        finWeight (negativeBinomialCensoredWeight successes cap trueWeight falseWeight) cap =
          finWeight (negativeBinomialWeight successes cap trueWeight falseWeight) cap +
            negativeBinomialCensorTail successes cap trueWeight falseWeight := by
      simp [finWeight, negativeBinomialCensoredWeight]
    rw [hp, hl]
    ac_rfl
  rw [hcongr, negativeBinomialWeight_sum]

def negativeBinomialCensoredDistro (successes cap trueWeight falseWeight : Nat)
    (_hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    Distro (Fin (cap + 1)) where
  record :=
    have hpos : 0 < natSum (cap + 1)
        (finWeight (negativeBinomialCensoredWeight successes cap trueWeight falseWeight)) := by
      rw [negativeBinomialCensoredWeight_sum]
      exact Nat.lt_of_lt_of_le
        (Nat.mul_pos (Nat.pow_pos htrue)
          (nbSumHomog_pos _ _ _ _ (Nat.add_pos_left htrue _)))
        (Nat.le_add_right _ _)
    ofFinWeights (cap + 1)
      (negativeBinomialCensoredWeight successes cap trueWeight falseWeight) hpos

def negativeBinomialCensoredNatDistro (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    NatDistro (Fin (cap + 1)) :=
  ofFin cap (negativeBinomialCensoredDistro successes cap trueWeight falseWeight hsuccesses htrue).record

theorem negativeBinomialCensored_den (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    (negativeBinomialCensoredDistro successes cap trueWeight falseWeight hsuccesses htrue).record.den =
      trueWeight ^ successes * nbSumHomog successes falseWeight (trueWeight + falseWeight) cap +
        negativeBinomialCensorTail successes cap trueWeight falseWeight := by
  simp [negativeBinomialCensoredDistro, ofFinWeights, totalMass_finWeighted,
    negativeBinomialCensoredWeight_sum]

theorem negativeBinomialCensored_pmf (successes cap trueWeight falseWeight : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) (k : Fin (cap + 1)) :
    QProb.Equiv
      ((negativeBinomialCensoredDistro successes cap trueWeight falseWeight hsuccesses htrue).pmf k)
      ⟨negativeBinomialCensoredWeight successes cap trueWeight falseWeight k,
        (negativeBinomialCensoredDistro successes cap trueWeight falseWeight hsuccesses htrue).record.den,
        (negativeBinomialCensoredDistro successes cap trueWeight falseWeight hsuccesses htrue).record.den_pos⟩ := by
  simp [Distro.pmf, negativeBinomialCensoredDistro, ofFinWeights,
    FiniteProbRecord.probVal, QProb.Equiv, eventMass_finWeighted_singleton]

theorem negativeBinomialCensoredWeight_homog_sum
    (successes cap trueWeight falseWeight num den : Nat) :
    natSum (cap + 1) (fun k =>
        finWeight (negativeBinomialCensoredWeight successes cap trueWeight falseWeight) k *
          num ^ k * den ^ (cap - k)) =
      trueWeight ^ successes * nbSumHomog successes (falseWeight * num)
          ((trueWeight + falseWeight) * den) cap +
        negativeBinomialCensorTail successes cap trueWeight falseWeight * num ^ cap := by
  have hp :
      natSum cap (fun k =>
          finWeight (negativeBinomialCensoredWeight successes cap trueWeight falseWeight) k *
            num ^ k * den ^ (cap - k)) =
        natSum cap (fun k =>
          finWeight (negativeBinomialWeight successes cap trueWeight falseWeight) k *
            num ^ k * den ^ (cap - k)) := by
    apply natSum_congr
    intro k hk
    simp [finWeight, negativeBinomialCensoredWeight, hk, Nat.lt_succ_of_lt hk]
  have hsum :
      natSum (cap + 1) (fun k =>
          finWeight (negativeBinomialCensoredWeight successes cap trueWeight falseWeight) k *
            num ^ k * den ^ (cap - k)) =
        natSum (cap + 1) (fun k =>
          finWeight (negativeBinomialWeight successes cap trueWeight falseWeight) k *
            num ^ k * den ^ (cap - k)) +
          negativeBinomialCensorTail successes cap trueWeight falseWeight * num ^ cap := by
    rw [natSum_succ, natSum_succ (n := cap)
      (fun k => finWeight (negativeBinomialWeight successes cap trueWeight falseWeight) k *
        num ^ k * den ^ (cap - k))]
    rw [hp]
    simp [finWeight, negativeBinomialCensoredWeight, Nat.add_mul, Nat.add_assoc]
  rw [hsum, negativeBinomialWeight_homog_sum]

theorem negativeBinomialCensored_pgf
    (successes cap trueWeight falseWeight : Nat) (s : QProb)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    QProb.Equiv
      (pgf (negativeBinomialCensoredNatDistro successes cap trueWeight falseWeight hsuccesses htrue) s)
      ⟨trueWeight ^ successes * nbSumHomog successes (falseWeight * s.num)
          ((trueWeight + falseWeight) * s.den) cap +
          negativeBinomialCensorTail successes cap trueWeight falseWeight * s.num ^ cap,
        s.den ^ cap *
          (trueWeight ^ successes * nbSumHomog successes falseWeight (trueWeight + falseWeight) cap +
            negativeBinomialCensorTail successes cap trueWeight falseWeight),
        Nat.mul_pos (Nat.pow_pos s.den_pos)
          (Nat.lt_of_lt_of_le
            (Nat.mul_pos (Nat.pow_pos htrue) (nbSumHomog_pos _ _ _ _ (Nat.add_pos_left htrue _)))
            (Nat.le_add_right _ _))⟩ := by
  have hpos : 0 < natSum (cap + 1)
      (finWeight (negativeBinomialCensoredWeight successes cap trueWeight falseWeight)) := by
    rw [negativeBinomialCensoredWeight_sum]
    exact Nat.lt_of_lt_of_le
      (Nat.mul_pos (Nat.pow_pos htrue) (nbSumHomog_pos _ _ _ _ (Nat.add_pos_left htrue _)))
      (Nat.le_add_right _ _)
  have h := ofFinWeights_pgf cap
    (negativeBinomialCensoredWeight successes cap trueWeight falseWeight) hpos s
  refine QProb.equiv_trans
    (by simpa [negativeBinomialCensoredNatDistro, negativeBinomialCensoredDistro] using h) ?_
  simp [QProb.Equiv, negativeBinomialCensoredWeight_homog_sum,
    negativeBinomialCensoredWeight_sum]

theorem negativeBinomialCensored_pgf_ofNat
    (successes cap trueWeight falseWeight s : Nat)
    (hsuccesses : 0 < successes) (htrue : 0 < trueWeight) :
    QProb.Equiv
      (pgf (negativeBinomialCensoredNatDistro successes cap trueWeight falseWeight hsuccesses htrue)
        (QProb.ofNat s))
      ⟨trueWeight ^ successes * nbSumHomog successes (falseWeight * s)
          (trueWeight + falseWeight) cap +
          negativeBinomialCensorTail successes cap trueWeight falseWeight * s ^ cap,
        trueWeight ^ successes * nbSumHomog successes falseWeight (trueWeight + falseWeight) cap +
          negativeBinomialCensorTail successes cap trueWeight falseWeight,
        Nat.lt_of_lt_of_le
          (Nat.mul_pos (Nat.pow_pos htrue) (nbSumHomog_pos _ _ _ _ (Nat.add_pos_left htrue _)))
          (Nat.le_add_right _ _)⟩ := by
  simpa [QProb.ofNat] using
    negativeBinomialCensored_pgf successes cap trueWeight falseWeight (QProb.ofNat s) hsuccesses htrue

end Distros
end Probability
end Thesis
