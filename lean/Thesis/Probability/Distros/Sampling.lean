import Thesis.Probability.Distros.Basic

namespace Thesis
namespace Probability
namespace Distros

/-!
Sampling distros derived from finite urns.

Hypergeometric probability is the occupancy of one colour after drawing
without replacement from a two-colour urn; its normaliser is Vandermonde
convolution of binomial coefficients.  The truncated geometric distro is the
waiting time for a Bernoulli true outcome, restricted to a finite window so
the record remains a finite urn.  Its whole-number PGF is the ratio of
geometric sums after substituting `falseWeight * s`.
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

end Distros
end Probability
end Thesis
