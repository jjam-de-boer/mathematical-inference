import Thesis.Probability.Distros.Basic

namespace Thesis
namespace Probability
namespace Distros

/-!
Bernoulli distro: a two-cell labelled urn.

`bernoulliDistro trueWeight falseWeight` places mass `trueWeight` on `true`
and `falseWeight` on `false`.  It is the generating atom of the binomial
family: an `n`-fold independent product, pushed forward along the success
count, is the binomial distro of `n` trials.  Its whole-number PGF is
`(falseWeight + trueWeight * s) / (falseWeight + trueWeight)`.  The
success-count embedding `bernoulliBit` identifies it with the one-trial
binomial, and `bernoulliOfBit` is the inverse transport.
-/

/-- Two-outcome distro with the given positive total weight. -/
def bernoulliDistro (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) : Distro Bool where
  record := {
    atoms := [(false, falseWeight), (true, trueWeight)]
    den := falseWeight + trueWeight
    den_pos := positive
    total_mass := by
      simp [FiniteProbRecord.totalMass, Nat.add_comm]
  }

/-- Bernoulli as a Nat-valued distro, with `false ↦ 0` and `true ↦ 1`. -/
def bernoulliNatDistro (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) : NatDistro Bool where
  distro := bernoulliDistro trueWeight falseWeight positive
  embed := fun value => if value then 1 else 0

/-- The success-count embedding of a Bernoulli outcome into `Fin 2`. -/
def bernoulliBit : Bool → Fin 2
  | false => ⟨0, Nat.succ_pos 1⟩
  | true => ⟨1, Nat.lt_succ_self 1⟩

/-- Inverse of `bernoulliBit` on `Fin 2`. -/
def bernoulliOfBit : Fin 2 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨n + 2, h⟩ => False.elim (Nat.not_lt.mpr (Nat.le_add_left 2 n) h)

theorem bernoulliBit_ofBit (k : Fin 2) :
    bernoulliBit (bernoulliOfBit k) = k := by
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨n + 2, h⟩ =>
      exact False.elim (Nat.not_lt.mpr (Nat.le_add_left 2 n) h)

theorem bernoulliOfBit_bit (value : Bool) :
    bernoulliOfBit (bernoulliBit value) = value := by
  cases value with
  | false => rfl
  | true => rfl

/-- Pulling a `Fin 2` singleton back along `bernoulliBit` is the Boolean
singleton of the inverse bit. -/
theorem singleton_comp_bernoulliBit (k : Fin 2) (value : Bool) :
    FiniteProbRecord.singletonEvent k (bernoulliBit value) =
      FiniteProbRecord.singletonEvent (bernoulliOfBit k) value := by
  cases value with
  | false =>
      match k with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨n + 2, h⟩ =>
          exact False.elim (Nat.not_lt.mpr (Nat.le_add_left 2 n) h)
  | true =>
      match k with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨n + 2, h⟩ =>
          exact False.elim (Nat.not_lt.mpr (Nat.le_add_left 2 n) h)

/-- `bernoulliBit` is the `Fin 2` packaging of the Nat embedding
`false ↦ 0`, `true ↦ 1`. -/
theorem bernoulliBit_val (value : Bool) :
    (bernoulliBit value).val = if value then 1 else 0 := by
  cases value with
  | false => rfl
  | true => rfl

theorem bernoulliBit_embed (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (value : Bool) :
    (bernoulliBit value).val =
      (bernoulliNatDistro trueWeight falseWeight positive).embed value := by
  simp [bernoulliNatDistro, bernoulliBit_val]

theorem bernoulli_pmf_true (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    QProb.Equiv
      ((bernoulliDistro trueWeight falseWeight positive).pmf true)
      ⟨trueWeight, falseWeight + trueWeight, positive⟩ := by
  simp [Distro.pmf, FiniteProbRecord.probVal, FiniteProbRecord.singletonEvent,
    FiniteProbRecord.eventMass, bernoulliDistro, QProb.Equiv]

theorem bernoulli_pmf_false (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    QProb.Equiv
      ((bernoulliDistro trueWeight falseWeight positive).pmf false)
      ⟨falseWeight, falseWeight + trueWeight, positive⟩ := by
  simp [Distro.pmf, FiniteProbRecord.probVal, FiniteProbRecord.singletonEvent,
    FiniteProbRecord.eventMass, bernoulliDistro, QProb.Equiv]

/-- The Bernoulli mean is the success probability `trueWeight / (falseWeight + trueWeight)`. -/
theorem bernoulli_mean (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    QProb.Equiv
      (mean (bernoulliNatDistro trueWeight falseWeight positive))
      ⟨trueWeight, falseWeight + trueWeight, positive⟩ := by
  simp [mean, rawMoment, natAtoms, bernoulliNatDistro, bernoulliDistro,
    Combinatorics.weightedPowSum, QProb.Equiv]

/-- The two-cell urn of a Bernoulli distro has one cell per weight unit. -/
theorem bernoulli_toUrn_n (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    (bernoulliDistro trueWeight falseWeight positive).toUrn.n =
      falseWeight + trueWeight := by
  simp [Distro.toUrn, FiniteProbRecord.toUrn, bernoulliDistro, UrnProb.ofList]
  rw [FiniteProbRecord.length_expand]
  simp [FiniteProbRecord.totalMass, Nat.add_comm]

/-- The Bernoulli PGF, evaluated at a whole number `s`, is
`(falseWeight + trueWeight * s) / (falseWeight + trueWeight)`. -/
theorem bernoulli_pgf_ofNat (trueWeight falseWeight s : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    QProb.Equiv
      (pgf (bernoulliNatDistro trueWeight falseWeight positive)
        (QProb.ofNat s))
      ⟨falseWeight + trueWeight * s,
        falseWeight + trueWeight,
        positive⟩ := by
  have hf := scale_qpow_ofNat falseWeight s 0
  have ht := scale_qpow_ofNat trueWeight s 1
  have hnum :
      QProb.Equiv
        (QProb.listSum
          ((bernoulliNatDistro trueWeight falseWeight
              positive).distro.record.atoms.map fun atom =>
            QProb.scale atom.2
              (qpow (QProb.ofNat s)
                ((bernoulliNatDistro trueWeight falseWeight
                    positive).embed atom.1))))
        (QProb.ofNat (falseWeight + trueWeight * s)) := by
    simp [bernoulliNatDistro, bernoulliDistro, QProb.listSum]
    have hz : s ^ 0 = 1 := Nat.pow_zero s
    have hone : s ^ 1 = s := Nat.pow_one s
    have hf' : QProb.Equiv
        (QProb.scale falseWeight (qpow (QProb.ofNat s) 0))
        (QProb.ofNat falseWeight) := by
      simpa [hz, Nat.mul_one] using hf
    have ht' : QProb.Equiv
        (QProb.scale trueWeight (qpow (QProb.ofNat s) 1))
        (QProb.ofNat (trueWeight * s)) := by
      simpa [hone] using ht
    have htail :
        QProb.Equiv
          (QProb.add
            (QProb.scale trueWeight (qpow (QProb.ofNat s) 1))
            QProb.zero)
          (QProb.scale trueWeight (qpow (QProb.ofNat s) 1)) := by
      simp [QProb.add, QProb.zero, QProb.Equiv, QProb.scale]
    have hsum :=
      QProb.add_congr hf' (QProb.equiv_trans htail ht')
    exact QProb.equiv_trans hsum (QProb.ofNat_add falseWeight (trueWeight * s))
  have hden :
      QProb.Equiv
        (QProb.ofNat
          (bernoulliNatDistro trueWeight falseWeight positive).distro.record.den)
        (QProb.ofNat (falseWeight + trueWeight)) := by
    simp [bernoulliNatDistro, bernoulliDistro, QProb.Equiv, QProb.ofNat]
  have hdiv :=
    QProb.div_congr hnum hden
      (bernoulliNatDistro trueWeight falseWeight positive).distro.record.den_pos
      positive
  refine QProb.equiv_trans (by simpa [pgf] using hdiv) ?_
  simp [QProb.div, QProb.ofNat, QProb.Equiv]

end Distros
end Probability
end Thesis
