import Thesis.Probability.Distros.Basic

namespace Thesis
namespace Probability
namespace Distros

/-!
Sampling distros derived from finite urns.

Hypergeometric probability is the occupancy of one colour after drawing
without replacement from a two-colour urn; its normaliser is Vandermonde
convolution of binomial coefficients.  Event probabilities, not merely
singleton PMFs, are the selected-weight sums against that Vandermonde
total.  The univariate PGF of the marked count is the homogenised
Vandermonde generating polynomial.  The truncated geometric distro is the
waiting time for a Bernoulli true outcome, conditioned on success in a
finite window.  Every terminal path is padded to the same horizon by the
Bernoulli total `trueWeight + falseWeight`.  Its generating sums therefore
retain that total when substituting the PGF argument.  Both the truncated
and right-censored laws have PGFs at general nonnegative rational arguments.
The censored sibling puts the all-failure path on the last cell and has
denominator `(trueWeight + falseWeight)^(cap + 1)`.
-/

open Combinatorics

/-- Hypergeometric weights: `K` marked cells in an `N`-cell urn, `n` draws. -/
def hypergeometricWeight (marked total draws : Nat)
    (k : Fin (draws + 1)) : Nat :=
  binom marked k.val * binom (total - marked) (draws - k.val)

/-- Hypergeometric distro, requiring a well-formed two-colour urn. -/
def hypergeometricDistro (marked total draws : Nat)
    (hmarked : marked ≤ total)
    (positive : 0 < binom total draws) :
    Distro (Fin (draws + 1)) where
  record :=
    have hsum :
        natSum (draws + 1)
            (finWeight (hypergeometricWeight marked total draws)) =
          binom total draws := by
      have hcongr :
          natSum (draws + 1)
              (finWeight (hypergeometricWeight marked total draws)) =
            natSum (draws + 1) (fun k =>
              binom marked k * binom (total - marked) (draws - k)) := by
        apply natSum_congr
        intro k hk
        simp [finWeight, hypergeometricWeight, hk]
      have hv := vandermonde marked (total - marked) draws
      have htotal : marked + (total - marked) = total :=
        Nat.add_sub_of_le hmarked
      rw [hcongr, hv, htotal]
    ofFinWeights (draws + 1) (hypergeometricWeight marked total draws) (by
      simpa [hsum] using positive)

theorem hypergeometric_den (marked total draws : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws) :
    (hypergeometricDistro marked total draws hmarked positive).record.den =
      binom total draws := by
  have hcongr :
      natSum (draws + 1)
          (finWeight (hypergeometricWeight marked total draws)) =
        natSum (draws + 1) (fun k =>
          binom marked k * binom (total - marked) (draws - k)) := by
    apply natSum_congr
    intro k hk
    simp [finWeight, hypergeometricWeight, hk]
  have hv := vandermonde marked (total - marked) draws
  have htotal : marked + (total - marked) = total :=
    Nat.add_sub_of_le hmarked
  simp [hypergeometricDistro, ofFinWeights, totalMass_finWeighted,
    hcongr, hv, htotal]

theorem hypergeometric_pmf (marked total draws : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws)
    (k : Fin (draws + 1)) :
    QProb.Equiv
      ((hypergeometricDistro marked total draws hmarked positive).pmf k)
      ⟨hypergeometricWeight marked total draws k,
        (hypergeometricDistro marked total draws hmarked positive).record.den,
        (hypergeometricDistro marked total draws hmarked
          positive).record.den_pos⟩ := by
  simp [Distro.pmf, hypergeometricDistro, ofFinWeights, FiniteProbRecord.probVal,
    QProb.Equiv, eventMass_finWeighted_singleton]

/-- Hypergeometric event probability is the selected-weight sum over the
Vandermonde total `C(total, draws)`. -/
theorem hypergeometric_probVal (marked total draws : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws)
    (event : Event (Fin (draws + 1))) :
    QProb.Equiv
      ((hypergeometricDistro marked total draws hmarked
          positive).record.probVal event)
      ⟨natSum (draws + 1) (fun k =>
          if h : k < draws + 1 then
            if event ⟨k, h⟩ then
              hypergeometricWeight marked total draws ⟨k, h⟩
            else 0
          else 0),
        binom total draws,
        positive⟩ := by
  have hsum :
      natSum (draws + 1)
          (finWeight (hypergeometricWeight marked total draws)) =
        binom total draws := by
    have hcongr :
        natSum (draws + 1)
            (finWeight (hypergeometricWeight marked total draws)) =
          natSum (draws + 1) (fun k =>
            binom marked k * binom (total - marked) (draws - k)) := by
      apply natSum_congr
      intro k hk
      simp [finWeight, hypergeometricWeight, hk]
    have hv := vandermonde marked (total - marked) draws
    have htotal : marked + (total - marked) = total :=
      Nat.add_sub_of_le hmarked
    rw [hcongr, hv, htotal]
  have hpos : 0 < natSum (draws + 1)
      (finWeight (hypergeometricWeight marked total draws)) := by
    simpa [hsum] using positive
  have hfin :=
    ofFinWeights_probVal (draws + 1)
      (hypergeometricWeight marked total draws) hpos event
  refine QProb.equiv_trans (by simpa [hypergeometricDistro] using hfin) ?_
  simp [QProb.Equiv, hsum]

def hypergeometricNatDistro (marked total draws : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws) :
    NatDistro (Fin (draws + 1)) :=
  ofFin draws
    (hypergeometricDistro marked total draws hmarked positive).record

/-- Homogenised hypergeometric generating sum
`∑_k C(marked, k) C(total - marked, draws - k) num^k den^{draws - k}`.
The Vandermonde identity is the `num = den = 1` case. -/
def hypergeometricSumHomog (marked total draws num den : Nat) : Nat :=
  natSum (draws + 1) (fun k =>
    binom marked k * binom (total - marked) (draws - k) *
      num ^ k * den ^ (draws - k))

/-- Homogenising a hypergeometric weight against a common denominator
power is the corresponding Vandermonde generating term. -/
theorem hypergeometricWeight_homogenize
    (marked total draws num den : Nat) (k : Fin (draws + 1)) :
    hypergeometricWeight marked total draws k * num ^ k.val *
        den ^ (draws - k.val) =
      binom marked k.val * binom (total - marked) (draws - k.val) *
        num ^ k.val * den ^ (draws - k.val) := by
  simp [hypergeometricWeight]

/-- The hypergeometric PGF at a nonnegative rational `s` is the ratio of
the homogenised Vandermonde generating sum to `C(total, draws)`. -/
theorem hypergeometric_pgf (marked total draws : Nat)
    (hmarked : marked ≤ total) (positive : 0 < binom total draws)
    (s : QProb) :
    QProb.Equiv
      (pgf (hypergeometricNatDistro marked total draws hmarked positive) s)
      (QProb.div
        ⟨hypergeometricSumHomog marked total draws s.num s.den,
          s.den ^ draws,
          Nat.pow_pos s.den_pos⟩
        (QProb.ofNat (binom total draws))
        positive) := by
  have hatoms :
      (hypergeometricNatDistro marked total draws hmarked
          positive).distro.record.atoms =
        finWeighted (draws + 1)
          (hypergeometricWeight marked total draws) := by
    simp [hypergeometricNatDistro, ofFin, hypergeometricDistro, ofFinWeights]
  have hnum :
      QProb.Equiv
        (QProb.listSum
          ((hypergeometricNatDistro marked total draws hmarked
              positive).distro.record.atoms.map fun atom =>
            QProb.scale atom.2
              (qpow s
                ((hypergeometricNatDistro marked total draws hmarked
                    positive).embed atom.1))))
        ⟨hypergeometricSumHomog marked total draws s.num s.den,
          s.den ^ draws,
          Nat.pow_pos s.den_pos⟩ := by
    rw [hatoms]
    have hsum :=
      listSum_scale_qpow_finWeighted_qprob draws
        (hypergeometricWeight marked total draws) s
    have hterm :
        natSum (draws + 1) (fun i =>
            finWeight (hypergeometricWeight marked total draws) i *
              s.num ^ i * s.den ^ (draws - i)) =
          hypergeometricSumHomog marked total draws s.num s.den := by
      apply natSum_congr
      intro i hi
      simp [finWeight, hi]
      exact hypergeometricWeight_homogenize marked total draws
        s.num s.den ⟨i, hi⟩
    refine QProb.equiv_trans hsum ?_
    simp [QProb.Equiv, hterm]
  have hden :
      QProb.Equiv
        (QProb.ofNat
          (hypergeometricNatDistro marked total draws hmarked
            positive).distro.record.den)
        (QProb.ofNat (binom total draws)) := by
    simp [QProb.Equiv, QProb.ofNat]
    exact hypergeometric_den marked total draws hmarked positive
  have hdiv :=
    QProb.div_congr hnum hden
      (hypergeometricNatDistro marked total draws hmarked
        positive).distro.record.den_pos
      positive
  simpa [pgf] using hdiv

/-- Bernoulli waiting-time weights on `{0, ..., cap}`, cleared to
the common trial denominator `(trueWeight + falseWeight)^(cap + 1)`. -/
def geometricWeight (cap trueWeight falseWeight : Nat)
    (k : Fin (cap + 1)) : Nat :=
  trueWeight * falseWeight ^ k.val *
    (trueWeight + falseWeight) ^ (cap - k.val)

theorem geometricWeight_sum (cap trueWeight falseWeight : Nat) :
    natSum (cap + 1) (finWeight (geometricWeight cap trueWeight falseWeight)) =
      trueWeight * geomSumHomog falseWeight (trueWeight + falseWeight) cap := by
  have hcongr :
      natSum (cap + 1)
          (finWeight (geometricWeight cap trueWeight falseWeight)) =
        natSum (cap + 1) (fun k =>
          trueWeight * (falseWeight ^ k *
            (trueWeight + falseWeight) ^ (cap - k))) := by
    apply natSum_congr
    intro k hk
    simp [finWeight, geometricWeight, hk, Nat.mul_assoc]
  rw [hcongr, natSum_mul_left]
  rfl

/-- The waiting time conditioned on success within the finite window. -/
def geometricDistro (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) : Distro (Fin (cap + 1)) where
  record :=
    have hpos : 0 < natSum (cap + 1)
        (finWeight (geometricWeight cap trueWeight falseWeight)) := by
      rw [geometricWeight_sum]
      exact Nat.mul_pos positive
        (geomSumHomog_pos _ _ _ (Nat.add_pos_left positive _))
    ofFinWeights (cap + 1) (geometricWeight cap trueWeight falseWeight) hpos

def geometricNatDistro (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) : NatDistro (Fin (cap + 1)) :=
  ofFin cap (geometricDistro cap trueWeight falseWeight positive).record

theorem geometric_den (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) :
    (geometricDistro cap trueWeight falseWeight positive).record.den =
      trueWeight * geomSumHomog falseWeight (trueWeight + falseWeight) cap := by
  simp [geometricDistro, ofFinWeights, totalMass_finWeighted, geometricWeight_sum]

theorem geometric_pmf (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) (k : Fin (cap + 1)) :
    QProb.Equiv
      ((geometricDistro cap trueWeight falseWeight positive).pmf k)
      ⟨geometricWeight cap trueWeight falseWeight k,
        (geometricDistro cap trueWeight falseWeight positive).record.den,
        (geometricDistro cap trueWeight falseWeight positive).record.den_pos⟩ := by
  simp [Distro.pmf, geometricDistro, ofFinWeights,
    FiniteProbRecord.probVal, QProb.Equiv, eventMass_finWeighted_singleton]

/-- Generating substitution keeps the original Bernoulli total fixed. -/
theorem geometricWeight_scale_pow (cap trueWeight falseWeight s : Nat)
    (k : Fin (cap + 1)) :
    geometricWeight cap trueWeight falseWeight k * s ^ k.val =
      trueWeight * (falseWeight * s) ^ k.val *
        (trueWeight + falseWeight) ^ (cap - k.val) := by
  simp [geometricWeight, Nat.mul_pow]
  ac_rfl

theorem geometricWeight_homogenize
    (cap trueWeight falseWeight num den : Nat) (k : Fin (cap + 1)) :
    geometricWeight cap trueWeight falseWeight k * num ^ k.val *
        den ^ (cap - k.val) =
      trueWeight * (falseWeight * num) ^ k.val *
        ((trueWeight + falseWeight) * den) ^ (cap - k.val) := by
  simp [geometricWeight, Nat.mul_pow]
  ac_rfl

theorem geometricWeight_homog_sum
    (cap trueWeight falseWeight num den : Nat) :
    natSum (cap + 1) (fun k =>
        finWeight (geometricWeight cap trueWeight falseWeight) k *
          num ^ k * den ^ (cap - k)) =
      trueWeight * geomSumHomog (falseWeight * num)
        ((trueWeight + falseWeight) * den) cap := by
  have hcongr :
      natSum (cap + 1) (fun k =>
          finWeight (geometricWeight cap trueWeight falseWeight) k *
            num ^ k * den ^ (cap - k)) =
        natSum (cap + 1) (fun k =>
          trueWeight * ((falseWeight * num) ^ k *
            ((trueWeight + falseWeight) * den) ^ (cap - k))) := by
    apply natSum_congr
    intro k hk
    simpa [finWeight, hk, Nat.mul_assoc] using
      geometricWeight_homogenize cap trueWeight falseWeight num den ⟨k, hk⟩
  rw [hcongr, natSum_mul_left]
  rfl

/-- The finite conditional PGF retains the Bernoulli trial denominator. -/
theorem geometric_pgf (cap trueWeight falseWeight : Nat) (s : QProb)
    (positive : 0 < trueWeight) :
    QProb.Equiv
      (pgf (geometricNatDistro cap trueWeight falseWeight positive) s)
      ⟨trueWeight * geomSumHomog (falseWeight * s.num)
          ((trueWeight + falseWeight) * s.den) cap,
        s.den ^ cap *
          (trueWeight * geomSumHomog falseWeight (trueWeight + falseWeight) cap),
        Nat.mul_pos (Nat.pow_pos s.den_pos)
          (Nat.mul_pos positive
            (geomSumHomog_pos _ _ _ (Nat.add_pos_left positive _)))⟩ := by
  have hpos : 0 < natSum (cap + 1)
      (finWeight (geometricWeight cap trueWeight falseWeight)) := by
    rw [geometricWeight_sum]
    exact Nat.mul_pos positive
      (geomSumHomog_pos _ _ _ (Nat.add_pos_left positive _))
  have h := ofFinWeights_pgf cap (geometricWeight cap trueWeight falseWeight) hpos s
  refine QProb.equiv_trans (by simpa [geometricNatDistro, geometricDistro] using h) ?_
  simp [QProb.Equiv, geometricWeight_homog_sum, geometricWeight_sum]

theorem geometric_pgf_ofNat (cap trueWeight falseWeight s : Nat)
    (positive : 0 < trueWeight) :
    QProb.Equiv
      (pgf (geometricNatDistro cap trueWeight falseWeight positive) (QProb.ofNat s))
      ⟨trueWeight * geomSumHomog (falseWeight * s) (trueWeight + falseWeight) cap,
        trueWeight * geomSumHomog falseWeight (trueWeight + falseWeight) cap,
        Nat.mul_pos positive
          (geomSumHomog_pos _ _ _ (Nat.add_pos_left positive _))⟩ := by
  simpa [QProb.ofNat] using geometric_pgf cap trueWeight falseWeight (QProb.ofNat s) positive

/-- Censor the failure count at `cap`.  The last cell includes success
at `cap` failures and the all-failure path in `cap + 1` trials. -/
def geometricCensoredWeight (cap trueWeight falseWeight : Nat)
    (k : Fin (cap + 1)) : Nat :=
  if k.val < cap then
    geometricWeight cap trueWeight falseWeight k
  else
    geometricWeight cap trueWeight falseWeight k + falseWeight ^ (cap + 1)

theorem geometricCensoredWeight_sum (cap trueWeight falseWeight : Nat) :
    natSum (cap + 1)
        (finWeight (geometricCensoredWeight cap trueWeight falseWeight)) =
      (trueWeight + falseWeight) ^ (cap + 1) := by
  have hcongr :
      natSum (cap + 1)
          (finWeight (geometricCensoredWeight cap trueWeight falseWeight)) =
        natSum (cap + 1)
          (finWeight (geometricWeight cap trueWeight falseWeight)) +
            falseWeight ^ (cap + 1) := by
    rw [natSum_succ, natSum_succ (n := cap)
      (finWeight (geometricWeight cap trueWeight falseWeight))]
    have hp :
        natSum cap (finWeight (geometricCensoredWeight cap trueWeight falseWeight)) =
          natSum cap (finWeight (geometricWeight cap trueWeight falseWeight)) := by
      apply natSum_congr
      intro k hk
      simp [finWeight, geometricCensoredWeight, hk, Nat.lt_succ_of_lt hk]
    have hl :
        finWeight (geometricCensoredWeight cap trueWeight falseWeight) cap =
          finWeight (geometricWeight cap trueWeight falseWeight) cap +
            falseWeight ^ (cap + 1) := by
      simp [finWeight, geometricCensoredWeight]
    rw [hp, hl]
    ac_rfl
  rw [hcongr, geometricWeight_sum, geomSumHomog_bernoulli]

def geometricCensoredDistro (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) : Distro (Fin (cap + 1)) where
  record :=
    have hpos : 0 < natSum (cap + 1)
        (finWeight (geometricCensoredWeight cap trueWeight falseWeight)) := by
      rw [geometricCensoredWeight_sum]
      exact Nat.pow_pos (Nat.add_pos_left positive _)
    ofFinWeights (cap + 1) (geometricCensoredWeight cap trueWeight falseWeight) hpos

def geometricCensoredNatDistro (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) : NatDistro (Fin (cap + 1)) :=
  ofFin cap (geometricCensoredDistro cap trueWeight falseWeight positive).record

theorem geometricCensored_den (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) :
    (geometricCensoredDistro cap trueWeight falseWeight positive).record.den =
      (trueWeight + falseWeight) ^ (cap + 1) := by
  simp [geometricCensoredDistro, ofFinWeights, totalMass_finWeighted,
    geometricCensoredWeight_sum]

theorem geometricCensored_pmf (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) (k : Fin (cap + 1)) :
    QProb.Equiv
      ((geometricCensoredDistro cap trueWeight falseWeight positive).pmf k)
      ⟨geometricCensoredWeight cap trueWeight falseWeight k,
        (geometricCensoredDistro cap trueWeight falseWeight positive).record.den,
        (geometricCensoredDistro cap trueWeight falseWeight positive).record.den_pos⟩ := by
  simp [Distro.pmf, geometricCensoredDistro, ofFinWeights,
    FiniteProbRecord.probVal, QProb.Equiv, eventMass_finWeighted_singleton]

theorem geometricCensoredWeight_homog_sum
    (cap trueWeight falseWeight num den : Nat) :
    natSum (cap + 1) (fun k =>
        finWeight (geometricCensoredWeight cap trueWeight falseWeight) k *
          num ^ k * den ^ (cap - k)) =
      trueWeight * geomSumHomog (falseWeight * num)
          ((trueWeight + falseWeight) * den) cap +
        falseWeight ^ (cap + 1) * num ^ cap := by
  have hp :
      natSum cap (fun k =>
          finWeight (geometricCensoredWeight cap trueWeight falseWeight) k *
            num ^ k * den ^ (cap - k)) =
        natSum cap (fun k =>
          finWeight (geometricWeight cap trueWeight falseWeight) k *
            num ^ k * den ^ (cap - k)) := by
    apply natSum_congr
    intro k hk
    simp [finWeight, geometricCensoredWeight, hk, Nat.lt_succ_of_lt hk]
  have hsum :
      natSum (cap + 1) (fun k =>
          finWeight (geometricCensoredWeight cap trueWeight falseWeight) k *
            num ^ k * den ^ (cap - k)) =
        natSum (cap + 1) (fun k =>
          finWeight (geometricWeight cap trueWeight falseWeight) k *
            num ^ k * den ^ (cap - k)) +
          falseWeight ^ (cap + 1) * num ^ cap := by
    rw [natSum_succ, natSum_succ (n := cap)
      (fun k => finWeight (geometricWeight cap trueWeight falseWeight) k *
        num ^ k * den ^ (cap - k))]
    rw [hp]
    simp [finWeight, geometricCensoredWeight, Nat.add_mul, Nat.add_assoc]
  rw [hsum, geometricWeight_homog_sum]

theorem geometricCensored_pgf (cap trueWeight falseWeight : Nat) (s : QProb)
    (positive : 0 < trueWeight) :
    QProb.Equiv
      (pgf (geometricCensoredNatDistro cap trueWeight falseWeight positive) s)
      ⟨trueWeight * geomSumHomog (falseWeight * s.num)
          ((trueWeight + falseWeight) * s.den) cap +
          falseWeight ^ (cap + 1) * s.num ^ cap,
        s.den ^ cap * (trueWeight + falseWeight) ^ (cap + 1),
        Nat.mul_pos (Nat.pow_pos s.den_pos)
          (Nat.pow_pos (Nat.add_pos_left positive _))⟩ := by
  have hpos : 0 < natSum (cap + 1)
      (finWeight (geometricCensoredWeight cap trueWeight falseWeight)) := by
    rw [geometricCensoredWeight_sum]
    exact Nat.pow_pos (Nat.add_pos_left positive _)
  have h := ofFinWeights_pgf cap
    (geometricCensoredWeight cap trueWeight falseWeight) hpos s
  refine QProb.equiv_trans
    (by simpa [geometricCensoredNatDistro, geometricCensoredDistro] using h) ?_
  simp [QProb.Equiv, geometricCensoredWeight_homog_sum, geometricCensoredWeight_sum]

theorem geometricCensored_pgf_ofNat (cap trueWeight falseWeight s : Nat)
    (positive : 0 < trueWeight) :
    QProb.Equiv
      (pgf (geometricCensoredNatDistro cap trueWeight falseWeight positive) (QProb.ofNat s))
      ⟨trueWeight * geomSumHomog (falseWeight * s) (trueWeight + falseWeight) cap +
          falseWeight ^ (cap + 1) * s ^ cap,
        (trueWeight + falseWeight) ^ (cap + 1),
        Nat.pow_pos (Nat.add_pos_left positive _)⟩ := by
  simpa [QProb.ofNat] using
    geometricCensored_pgf cap trueWeight falseWeight (QProb.ofNat s) positive

end Distros
end Probability
end Thesis
