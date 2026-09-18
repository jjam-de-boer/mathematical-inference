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
waiting time for a Bernoulli true outcome, restricted to a finite window so
the record remains a finite urn.  Its whole-number PGF is the ratio of
geometric sums after substituting `falseWeight * s`.  The same closed form
holds at a general nonnegative rational after homogenising the generating
sum against `s.den`.  The right-censored sibling keeps the ordinary
waiting-time weights on `{0, …, cap - 1}` and places the leftover
`falseWeight^{cap+1}` (together with the mass at `cap`) on the last cell.
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

/-- Truncated geometric weights: `k` false outcomes then a true outcome,
for `k ≤ cap`. -/
def geometricWeight (cap trueWeight falseWeight : Nat)
    (k : Fin (cap + 1)) : Nat :=
  trueWeight * falseWeight ^ k.val

theorem geometricWeight_sum (cap trueWeight falseWeight : Nat) :
    natSum (cap + 1) (finWeight (geometricWeight cap trueWeight falseWeight)) =
      trueWeight * geomSum falseWeight (cap + 1) := by
  have hcongr :
      natSum (cap + 1)
          (finWeight (geometricWeight cap trueWeight falseWeight)) =
        natSum (cap + 1) (fun k => trueWeight * falseWeight ^ k) := by
    apply natSum_congr
    intro k hk
    simp [finWeight, geometricWeight, hk]
  rw [hcongr]
  simp [geomSum, natSum_mul_left]

/-- Truncated geometric distro on `{0, ..., cap}`. -/
def geometricDistro (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) : Distro (Fin (cap + 1)) where
  record :=
    have hsum := geometricWeight_sum cap trueWeight falseWeight
    have hpos : 0 < natSum (cap + 1)
        (finWeight (geometricWeight cap trueWeight falseWeight)) := by
      have hgeom : 0 < geomSum falseWeight (cap + 1) := by
        unfold geomSum
        rw [natSum_head]
        simp [Nat.pow_zero]
        exact Nat.add_pos_left (Nat.succ_pos 0) _
      have : 0 < trueWeight * geomSum falseWeight (cap + 1) :=
        Nat.mul_pos positive hgeom
      simpa [hsum] using this
    ofFinWeights (cap + 1) (geometricWeight cap trueWeight falseWeight) hpos

def geometricNatDistro (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) : NatDistro (Fin (cap + 1)) :=
  ofFin cap (geometricDistro cap trueWeight falseWeight positive).record

theorem geometric_den (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) :
    (geometricDistro cap trueWeight falseWeight positive).record.den =
      trueWeight * geomSum falseWeight (cap + 1) := by
  simp [geometricDistro, ofFinWeights, totalMass_finWeighted,
    geometricWeight_sum]

theorem geometric_pmf (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) (k : Fin (cap + 1)) :
    QProb.Equiv
      ((geometricDistro cap trueWeight falseWeight positive).pmf k)
      ⟨geometricWeight cap trueWeight falseWeight k,
        (geometricDistro cap trueWeight falseWeight positive).record.den,
        (geometricDistro cap trueWeight falseWeight positive).record.den_pos⟩ :=
  by
  simp [Distro.pmf, geometricDistro, ofFinWeights, FiniteProbRecord.probVal,
    QProb.Equiv, eventMass_finWeighted_singleton]

/-- Scaling the waiting-time weight by `s^k` substitutes `falseWeight * s`
for the failure weight. -/
theorem geometricWeight_scale_pow (cap trueWeight falseWeight s : Nat)
    (k : Fin (cap + 1)) :
    geometricWeight cap trueWeight falseWeight k * s ^ k.val =
      geometricWeight cap trueWeight (falseWeight * s) k := by
  simp [geometricWeight, Nat.mul_pow]
  ac_rfl

/-- The truncated geometric PGF, evaluated at a whole number `s`, is the
ratio of geometric sums after substituting `falseWeight * s`. -/
theorem geometric_pgf_ofNat (cap trueWeight falseWeight s : Nat)
    (positive : 0 < trueWeight) :
    QProb.Equiv
      (pgf (geometricNatDistro cap trueWeight falseWeight positive)
        (QProb.ofNat s))
      ⟨trueWeight * geomSum (falseWeight * s) (cap + 1),
        trueWeight * geomSum falseWeight (cap + 1),
        Nat.mul_pos positive (geomSum_pos falseWeight (cap + 1) (Nat.succ_pos cap))⟩ := by
  have hatoms :
      (geometricNatDistro cap trueWeight falseWeight positive).distro.record.atoms =
        finWeighted (cap + 1)
          (geometricWeight cap trueWeight falseWeight) := by
    simp [geometricNatDistro, ofFin, geometricDistro, ofFinWeights]
  have hnum :
      QProb.Equiv
        (QProb.listSum
          ((geometricNatDistro cap trueWeight falseWeight
              positive).distro.record.atoms.map fun atom =>
            QProb.scale atom.2
              (qpow (QProb.ofNat s)
                ((geometricNatDistro cap trueWeight falseWeight
                    positive).embed atom.1))))
        (QProb.ofNat (trueWeight * geomSum (falseWeight * s) (cap + 1))) := by
    rw [hatoms]
    have hsum :=
      listSum_scale_qpow_finWeighted (cap + 1)
        (geometricWeight cap trueWeight falseWeight) s
    have hterm :
        natSum (cap + 1) (fun i =>
            finWeight (geometricWeight cap trueWeight falseWeight) i * s ^ i) =
          trueWeight * geomSum (falseWeight * s) (cap + 1) := by
      have hcongr :
          natSum (cap + 1) (fun i =>
              finWeight (geometricWeight cap trueWeight falseWeight) i * s ^ i) =
            natSum (cap + 1) (fun i =>
              finWeight (geometricWeight cap trueWeight (falseWeight * s)) i) := by
        apply natSum_congr
        intro i hi
        simp only [finWeight, hi]
        exact geometricWeight_scale_pow cap trueWeight falseWeight s ⟨i, hi⟩
      rw [hcongr, geometricWeight_sum]
    exact QProb.equiv_trans hsum (by
      simp [QProb.Equiv, QProb.ofNat]
      exact hterm)
  have hden :
      QProb.Equiv
        (QProb.ofNat
          (geometricNatDistro cap trueWeight falseWeight
            positive).distro.record.den)
        (QProb.ofNat (trueWeight * geomSum falseWeight (cap + 1))) := by
    simp [QProb.Equiv, QProb.ofNat]
    exact geometric_den cap trueWeight falseWeight positive
  have hdiv :=
    QProb.div_congr hnum hden
      (geometricNatDistro cap trueWeight falseWeight positive).distro.record.den_pos
      (Nat.mul_pos positive (geomSum_pos falseWeight (cap + 1) (Nat.succ_pos cap)))
  refine QProb.equiv_trans (by simpa [pgf] using hdiv) ?_
  simp [QProb.div, QProb.ofNat, QProb.Equiv]

/-- Homogenising a truncated geometric weight against a common denominator
power substitutes `falseWeight * num` in the generating base. -/
theorem geometricWeight_homogenize
    (cap trueWeight falseWeight num den : Nat)
    (k : Fin (cap + 1)) :
    geometricWeight cap trueWeight falseWeight k * num ^ k.val *
        den ^ (cap - k.val) =
      trueWeight * (falseWeight * num) ^ k.val * den ^ (cap - k.val) := by
  simp [geometricWeight, Nat.mul_pow]
  ac_rfl

/-- The truncated geometric PGF at a nonnegative rational `s` is the ratio
of a homogenised geometric sum to the ordinary geometric normaliser. -/
theorem geometric_pgf (cap trueWeight falseWeight : Nat) (s : QProb)
    (positive : 0 < trueWeight) :
    QProb.Equiv
      (pgf (geometricNatDistro cap trueWeight falseWeight positive) s)
      (QProb.div
        ⟨trueWeight *
            geomSumHomog (falseWeight * s.num) s.den cap,
          s.den ^ cap,
          Nat.pow_pos s.den_pos⟩
        (QProb.ofNat (trueWeight * geomSum falseWeight (cap + 1)))
        (Nat.mul_pos positive
          (geomSum_pos falseWeight (cap + 1) (Nat.succ_pos cap)))) := by
  have hatoms :
      (geometricNatDistro cap trueWeight falseWeight positive).distro.record.atoms =
        finWeighted (cap + 1)
          (geometricWeight cap trueWeight falseWeight) := by
    simp [geometricNatDistro, ofFin, geometricDistro, ofFinWeights]
  have hnum :
      QProb.Equiv
        (QProb.listSum
          ((geometricNatDistro cap trueWeight falseWeight
              positive).distro.record.atoms.map fun atom =>
            QProb.scale atom.2
              (qpow s
                ((geometricNatDistro cap trueWeight falseWeight
                    positive).embed atom.1))))
        ⟨trueWeight *
            geomSumHomog (falseWeight * s.num) s.den cap,
          s.den ^ cap,
          Nat.pow_pos s.den_pos⟩ := by
    rw [hatoms]
    have hsum :=
      listSum_scale_qpow_finWeighted_qprob cap
        (geometricWeight cap trueWeight falseWeight) s
    have hterm :
        natSum (cap + 1) (fun i =>
            finWeight (geometricWeight cap trueWeight falseWeight) i *
              s.num ^ i * s.den ^ (cap - i)) =
          trueWeight *
            geomSumHomog (falseWeight * s.num) s.den cap := by
      have hcongr :
          natSum (cap + 1) (fun i =>
              finWeight (geometricWeight cap trueWeight falseWeight) i *
                s.num ^ i * s.den ^ (cap - i)) =
            natSum (cap + 1) (fun i =>
              trueWeight * (falseWeight * s.num) ^ i *
                s.den ^ (cap - i)) := by
        apply natSum_congr
        intro i hi
        simp only [finWeight, hi]
        exact geometricWeight_homogenize cap trueWeight falseWeight
          s.num s.den ⟨i, hi⟩
      rw [hcongr]
      have hfactor :
          natSum (cap + 1) (fun i =>
            trueWeight * (falseWeight * s.num) ^ i * s.den ^ (cap - i)) =
          natSum (cap + 1) (fun i =>
            trueWeight *
              ((falseWeight * s.num) ^ i * s.den ^ (cap - i))) := by
        apply natSum_congr
        intro i _
        exact Nat.mul_assoc _ _ _
      rw [hfactor, natSum_mul_left]
      rfl
    refine QProb.equiv_trans hsum ?_
    simp [QProb.Equiv, hterm]
  have hden :
      QProb.Equiv
        (QProb.ofNat
          (geometricNatDistro cap trueWeight falseWeight
            positive).distro.record.den)
        (QProb.ofNat (trueWeight * geomSum falseWeight (cap + 1))) := by
    simp [QProb.Equiv, QProb.ofNat]
    exact geometric_den cap trueWeight falseWeight positive
  have hdiv :=
    QProb.div_congr hnum hden
      (geometricNatDistro cap trueWeight falseWeight positive).distro.record.den_pos
      (Nat.mul_pos positive
        (geomSum_pos falseWeight (cap + 1) (Nat.succ_pos cap)))
  simpa [pgf] using hdiv

/-- Right-censored geometric weights: ordinary waiting-time mass on
`{0, …, cap - 1}`, and on the last cell the mass at `cap` together with
the leftover `falseWeight^{cap+1}` of paths that never succeed in the
window. -/
def geometricCensoredWeight (cap trueWeight falseWeight : Nat)
    (k : Fin (cap + 1)) : Nat :=
  if k.val < cap then
    trueWeight * falseWeight ^ k.val
  else
    trueWeight * falseWeight ^ cap + falseWeight ^ (cap + 1)

theorem geometricCensoredWeight_sum (cap trueWeight falseWeight : Nat) :
    natSum (cap + 1)
        (finWeight (geometricCensoredWeight cap trueWeight falseWeight)) =
      trueWeight * geomSum falseWeight (cap + 1) +
        falseWeight ^ (cap + 1) := by
  have hprefix :
      natSum cap
          (finWeight (geometricCensoredWeight cap trueWeight falseWeight)) =
        trueWeight * geomSum falseWeight cap := by
    have hcongr :
        natSum cap
            (finWeight (geometricCensoredWeight cap trueWeight falseWeight)) =
          natSum cap (fun i => trueWeight * falseWeight ^ i) := by
      apply natSum_congr
      intro i hi
      have hfin : i < cap + 1 := Nat.lt_succ_of_lt hi
      simp [finWeight, geometricCensoredWeight, hfin, hi]
    rw [hcongr]
    simp [geomSum, natSum_mul_left]
  have hlast :
      finWeight (geometricCensoredWeight cap trueWeight falseWeight) cap =
        trueWeight * falseWeight ^ cap + falseWeight ^ (cap + 1) := by
    have hfin : cap < cap + 1 := Nat.lt_succ_self cap
    have hnlt : ¬ cap < cap := Nat.lt_irrefl cap
    simp [finWeight, geometricCensoredWeight, hfin, hnlt]
  rw [natSum_succ, hprefix, hlast, geomSum_succ, Nat.mul_add]
  ac_rfl

/-- Right-censored geometric distro on `{0, ..., cap}`. -/
def geometricCensoredDistro (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) : Distro (Fin (cap + 1)) where
  record :=
    have hsum := geometricCensoredWeight_sum cap trueWeight falseWeight
    have hpos : 0 < natSum (cap + 1)
        (finWeight (geometricCensoredWeight cap trueWeight falseWeight)) := by
      have hgeom : 0 < geomSum falseWeight (cap + 1) :=
        geomSum_pos falseWeight (cap + 1) (Nat.succ_pos cap)
      rw [hsum]
      exact Nat.lt_of_lt_of_le (Nat.mul_pos positive hgeom)
        (Nat.le_add_right _ _)
    ofFinWeights (cap + 1)
      (geometricCensoredWeight cap trueWeight falseWeight) hpos

def geometricCensoredNatDistro (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) : NatDistro (Fin (cap + 1)) :=
  ofFin cap (geometricCensoredDistro cap trueWeight falseWeight positive).record

theorem geometricCensored_den (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) :
    (geometricCensoredDistro cap trueWeight falseWeight positive).record.den =
      trueWeight * geomSum falseWeight (cap + 1) +
        falseWeight ^ (cap + 1) := by
  simp [geometricCensoredDistro, ofFinWeights, totalMass_finWeighted,
    geometricCensoredWeight_sum]

theorem geometricCensored_pmf (cap trueWeight falseWeight : Nat)
    (positive : 0 < trueWeight) (k : Fin (cap + 1)) :
    QProb.Equiv
      ((geometricCensoredDistro cap trueWeight falseWeight positive).pmf k)
      ⟨geometricCensoredWeight cap trueWeight falseWeight k,
        (geometricCensoredDistro cap trueWeight falseWeight
          positive).record.den,
        (geometricCensoredDistro cap trueWeight falseWeight
          positive).record.den_pos⟩ := by
  simp [Distro.pmf, geometricCensoredDistro, ofFinWeights,
    FiniteProbRecord.probVal, QProb.Equiv, eventMass_finWeighted_singleton]

end Distros
end Probability
end Thesis
