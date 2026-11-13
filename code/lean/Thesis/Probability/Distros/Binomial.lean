import Thesis.Probability.Construction
import Thesis.Probability.Distros.Bernoulli

namespace Thesis
namespace Probability
namespace Distros

/-!
Binomial distro: the success count of independent Bernoulli trials.

Two presentations are recorded, and they agree as events, not merely as
normalisers.  The closed form places weight
`C(n, k) trueWeight^k falseWeight^{n-k}` on `k : Fin (n + 1)`, with
normaliser `(trueWeight + falseWeight)^n` by the binomial theorem.  The
derived form is the pushforward of the `n`-fold independent Bernoulli
product along the count of `true` coordinates.  The event mass of
`trueCount = k` on that product is the closed binomial term, so the two
PMFs are `QProb.Equiv`.  The mean and the whole-number PGF are the
corresponding generating-function evaluations of those closed terms.
The PGF is recorded both at whole-number arguments and at a general
nonnegative rational.  Independent binomials with the same weights convolve
to the binomial of the summed trial count.  A single Bernoulli trial is the
one-trial binomial, transported along `false ↦ 0` and `true ↦ 1` and back
along `bernoulliOfBit`, as events, as PMFs, and as round-trip sections.
-/

open Combinatorics
open FiniteProduct

/-- Count the `true` coordinates of a finite Boolean assignment. -/
def trueCount : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, assignment =>
      trueCount n (fun i => assignment i.castSucc) +
        if assignment (Fin.last n) then 1 else 0

theorem trueCount_le (n : Nat) (assignment : Fin n → Bool) :
    trueCount n assignment ≤ n := by
  induction n with
  | zero => simp [trueCount]
  | succ n ih =>
      simp only [trueCount]
      have hprefix : trueCount n (fun i => assignment i.castSucc) ≤ n :=
        ih (fun i => assignment i.castSucc)
      cases assignment (Fin.last n) with
      | false => exact Nat.le_succ_of_le hprefix
      | true => exact Nat.succ_le_succ hprefix

theorem trueCount_extend (n : Nat) (last : Bool)
    (front : Fin n → Bool) :
    trueCount (n + 1) (extend last front) =
      trueCount n front + if last then 1 else 0 := by
  simp [trueCount, extend_last, extend_castSucc]

/-- Closed-form binomial weights on `Fin (trials + 1)`. -/
def binomialWeight (trials trueWeight falseWeight : Nat)
    (k : Fin (trials + 1)) : Nat :=
  binomTerm trials trueWeight falseWeight k.val

theorem binomialWeight_sum (trials trueWeight falseWeight : Nat) :
    natSum (trials + 1)
        (finWeight (binomialWeight trials trueWeight falseWeight)) =
      (trueWeight + falseWeight) ^ trials := by
  have hcongr :
      natSum (trials + 1)
          (finWeight (binomialWeight trials trueWeight falseWeight)) =
        natSum (trials + 1)
          (fun k => binomTerm trials trueWeight falseWeight k) := by
    apply natSum_congr
    intro k hk
    simp [finWeight, binomialWeight, hk]
  rw [hcongr, binomial_theorem]

/-- Closed-form binomial distro. -/
def binomialDistro (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) : Distro (Fin (trials + 1)) where
  record :=
    have hpos : 0 < natSum (trials + 1)
        (finWeight (binomialWeight trials trueWeight falseWeight)) := by
      have hsum := binomialWeight_sum trials trueWeight falseWeight
      have hbase : 0 < trueWeight + falseWeight := by
        simpa [Nat.add_comm falseWeight trueWeight] using positive
      have hpow : 0 < (trueWeight + falseWeight) ^ trials := Nat.pow_pos hbase
      simpa [hsum] using hpow
    ofFinWeights (trials + 1)
      (binomialWeight trials trueWeight falseWeight) hpos

/-- Binomial as a Nat-valued distro, embedding by the success count. -/
def binomialNatDistro (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) : NatDistro (Fin (trials + 1)) :=
  ofFin trials (binomialDistro trials trueWeight falseWeight positive).record

/-- Pushforward of `n` independent Bernoulli factors along the success count. -/
def binomialFromBernoulli (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) : Distro (Fin (trials + 1)) where
  record :=
    (record trials (fun _ => Bool)
      (fun _ => (bernoulliDistro trueWeight falseWeight positive).record)).map
      (fun assignment =>
        ⟨trueCount trials assignment,
          Nat.lt_succ_of_le (trueCount_le trials assignment)⟩)

theorem binomialDistro_den (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    (binomialDistro trials trueWeight falseWeight positive).record.den =
      (falseWeight + trueWeight) ^ trials := by
  simp [binomialDistro, ofFinWeights, totalMass_finWeighted,
    binomialWeight_sum, Nat.add_comm trueWeight falseWeight]

theorem bernoulli_record_den (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    (bernoulliDistro trueWeight falseWeight positive).record.den =
      falseWeight + trueWeight :=
  rfl

theorem bernoulliProduct_den (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    FiniteProduct.denominator trials (fun _ => Bool)
        (fun _ => (bernoulliDistro trueWeight falseWeight positive).record) =
      (falseWeight + trueWeight) ^ trials := by
  induction trials with
  | zero => simp [FiniteProduct.denominator]
  | succ n ih =>
      simp only [FiniteProduct.denominator]
      rw [bernoulli_record_den, ih, Nat.pow_succ, Nat.mul_comm]

theorem binomialFromBernoulli_den (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    (binomialFromBernoulli trials trueWeight falseWeight positive).record.den =
      (falseWeight + trueWeight) ^ trials := by
  simp [binomialFromBernoulli, FiniteProbRecord.map, FiniteProduct.record,
    bernoulliProduct_den]

/-- The closed-form binomial distro and the Bernoulli-product derivation
share a denominator, hence the same normaliser
`(trueWeight + falseWeight)^n`. -/
theorem binomial_eq_fromBernoulli_den (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    (binomialDistro trials trueWeight falseWeight positive).record.den =
      (binomialFromBernoulli trials trueWeight falseWeight positive).record.den :=
  by
  rw [binomialDistro_den, binomialFromBernoulli_den]

/-- The unit-cell urn of the closed binomial distro has one cell per
normaliser unit `(falseWeight + trueWeight)^n`. -/
theorem binomial_toUrn_n (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    (binomialDistro trials trueWeight falseWeight positive).toUrn.n =
      (falseWeight + trueWeight) ^ trials := by
  simp [Distro.toUrn, FiniteProbRecord.toUrn, binomialDistro, ofFinWeights,
    UrnProb.ofList]
  rw [FiniteProbRecord.length_expand]
  simp [totalMass_finWeighted, binomialWeight_sum,
    Nat.add_comm trueWeight falseWeight]

/-- Independent Bernoulli atoms used by the product presentation. -/
def bernoulliProductAtoms (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    List ((Fin trials → Bool) × Nat) :=
  FiniteProduct.atoms trials (fun _ => Bool)
    (fun _ => (bernoulliDistro trueWeight falseWeight positive).record)

theorem bernoulli_atoms (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    (bernoulliDistro trueWeight falseWeight positive).record.atoms =
      [(false, falseWeight), (true, trueWeight)] :=
  rfl

/-- Cartesian event mass against a two-cell Bernoulli factor. -/
theorem eventMass_bernoulli_cartesian (trueWeight falseWeight : Nat)
    (front : List (X × Nat)) (event : Event (Bool × X)) :
    FiniteProbRecord.eventMass
        (FiniteProbRecord.weightedCartesian
          [(false, falseWeight), (true, trueWeight)] front)
        event =
      falseWeight * FiniteProbRecord.eventMass front
          (fun x => event (false, x)) +
        trueWeight * FiniteProbRecord.eventMass front
          (fun x => event (true, x)) := by
  rw [FiniteProbRecord.eventMass_weightedCartesian_bind]
  simp [List.map, List.sum]

/-- Relabel a cartesian list along `extend` without going through the
generic `map_labels` unifier. -/
theorem eventMass_map_extend {n : Nat}
    (atoms : List ((Bool × (Fin n → Bool)) × Nat))
    (event : Event (Fin (n + 1) → Bool)) :
    FiniteProbRecord.eventMass
        (atoms.map fun atom => (extend atom.1.1 atom.1.2, atom.2)) event =
      FiniteProbRecord.eventMass atoms
        (fun pair => event (extend pair.1 pair.2)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      rcases atom with ⟨pair, weight⟩
      rcases pair with ⟨last, front⟩
      cases h : event (extend last front) <;>
        simp [FiniteProbRecord.eventMass, h, ih]

/-- Relabel Bernoulli-product atoms by their success count. -/
theorem eventMass_map_trueCount (trials : Nat)
    (atoms : List ((Fin trials → Bool) × Nat)) (k : Fin (trials + 1)) :
    FiniteProbRecord.eventMass
        (atoms.map fun atom =>
          (⟨trueCount trials atom.1,
              Nat.lt_succ_of_le (trueCount_le trials atom.1)⟩,
            atom.2))
        (FiniteProbRecord.singletonEvent k) =
      FiniteProbRecord.eventMass atoms
        (fun assignment => decide (trueCount trials assignment = k.val)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      rcases atom with ⟨assignment, weight⟩
      simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
        Fin.ext_iff, ih]

/-- Push the successor true-count identity through `decide`. -/
theorem trueCount_decide_extend (n k : Nat) (last : Bool)
    (front : Fin n → Bool) :
    decide (trueCount (n + 1) (extend last front) = k) =
      decide (trueCount n front + (if last then 1 else 0) = k) :=
  congrArg (fun t => decide (t = k)) (trueCount_extend n last front)

/-- A trailing `false` bit does not change the success count. -/
theorem trueCount_decide_false_bit (n k : Nat) (front : Fin n → Bool) :
    decide (trueCount n front + (if false then 1 else 0) = k) =
      decide (trueCount n front = k) := by
  have hcond : (if false then 1 else 0) = 0 := rfl
  rw [hcond, Nat.add_zero]

/-- A trailing `true` bit increments the success count. -/
theorem trueCount_decide_true_bit (n k : Nat) (front : Fin n → Bool) :
    decide (trueCount n front + (if true then 1 else 0) = k) =
      decide (trueCount n front + 1 = k) :=
  rfl

/-- The successor count is never zero, so the `k = 0` true-slice is empty. -/
theorem trueCount_succ_eq_zero_false (n : Nat) (front : Fin n → Bool) :
    decide (trueCount n front + 1 = 0) = false :=
  decide_eq_false (Nat.succ_ne_zero (trueCount n front))

/-- `decide` respects successor cancellation, using `Nat.decEq` rather than
classical case-splitting. -/
theorem trueCount_succ_inj_decide (n k : Nat) (front : Fin n → Bool) :
    decide (trueCount n front + 1 = k + 1) =
      decide (trueCount n front = k) := by
  cases Nat.decEq (trueCount n front) k with
  | isTrue hct =>
      rw [hct, decide_eq_true (Eq.refl (k + 1)), decide_eq_true (Eq.refl k)]
  | isFalse hct =>
      have hneq : trueCount n front + 1 ≠ k + 1 :=
        fun heq => hct (Nat.succ_inj.mp heq)
      rw [decide_eq_false hneq, decide_eq_false hct]

/-- Empty-product base of the count-mass identity: one dummy assignment of
weight one, whose true-count is zero. -/
theorem trueCount_mass_nil (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (k : Nat) :
    FiniteProbRecord.eventMass
        (bernoulliProductAtoms 0 trueWeight falseWeight positive)
        (fun assignment => decide (trueCount 0 assignment = k)) =
      binomTerm 0 trueWeight falseWeight k := by
  have hatoms :
      bernoulliProductAtoms 0 trueWeight falseWeight positive =
        [(fun i => Fin.elim0 i, 1)] :=
    rfl
  rw [hatoms]
  cases k with
  | zero =>
      rfl
  | succ k =>
      have hmass :
          FiniteProbRecord.eventMass
              ([(fun i => Fin.elim0 i, 1)] : List ((Fin 0 → Bool) × Nat))
              (fun assignment =>
                decide (trueCount 0 assignment = k + 1)) =
            FiniteProbRecord.eventMass
              ([(fun i => Fin.elim0 i, 1)] : List ((Fin 0 → Bool) × Nat))
              (fun _ => false) := by
        apply FiniteProbRecord.eventMass_congr
        intro assignment
        have htc : trueCount 0 assignment = 0 := rfl
        rw [htc]
        exact decide_eq_false (fun h => Nat.succ_ne_zero k h.symm)
      rw [hmass, FiniteProbRecord.eventMass_false, binomTerm, binom_zero_succ,
        Nat.zero_mul, Nat.zero_mul]

/-- The event `trueCount = k` on the Bernoulli product has mass equal to
the closed binomial term.  This is the event-level agreement of the two
binomial presentations; the `k = 0` / `k + 1` split avoids subtracting
from zero on `Nat`. -/
theorem trueCount_mass (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (k : Nat) :
    FiniteProbRecord.eventMass
        (bernoulliProductAtoms trials trueWeight falseWeight positive)
        (fun assignment => decide (trueCount trials assignment = k)) =
      binomTerm trials trueWeight falseWeight k := by
  induction trials generalizing k with
  | zero =>
      exact trueCount_mass_nil trueWeight falseWeight positive k
  | succ n ih =>
      have hatoms :
          bernoulliProductAtoms (n + 1) trueWeight falseWeight positive =
            (FiniteProbRecord.weightedCartesian
              (bernoulliDistro trueWeight falseWeight positive).record.atoms
              (bernoulliProductAtoms n trueWeight falseWeight
                positive)).map
              (fun atom => (extend atom.1.1 atom.1.2, atom.2)) :=
        rfl
      rw [hatoms, eventMass_map_extend]
      have hcount :
          FiniteProbRecord.eventMass
              (FiniteProbRecord.weightedCartesian
                (bernoulliDistro trueWeight falseWeight positive).record.atoms
                (bernoulliProductAtoms n trueWeight falseWeight positive))
              (fun pair =>
                decide (trueCount (n + 1) (extend pair.1 pair.2) = k)) =
            FiniteProbRecord.eventMass
              (FiniteProbRecord.weightedCartesian
                (bernoulliDistro trueWeight falseWeight positive).record.atoms
                (bernoulliProductAtoms n trueWeight falseWeight positive))
              (fun pair =>
                decide
                  (trueCount n pair.2 + (if pair.1 then 1 else 0) = k)) := by
        apply FiniteProbRecord.eventMass_congr
        intro pair
        exact trueCount_decide_extend n k pair.1 pair.2
      rw [hcount, bernoulli_atoms, eventMass_bernoulli_cartesian]
      have hfalse_slice :
          FiniteProbRecord.eventMass
              (bernoulliProductAtoms n trueWeight falseWeight positive)
              (fun front =>
                decide
                  (trueCount n (false, front).2 +
                    (if (false, front).1 then 1 else 0) = k)) =
            FiniteProbRecord.eventMass
              (bernoulliProductAtoms n trueWeight falseWeight positive)
              (fun front => decide (trueCount n front = k)) := by
        apply FiniteProbRecord.eventMass_congr
        intro front
        exact trueCount_decide_false_bit n k front
      have htrue_slice :
          FiniteProbRecord.eventMass
              (bernoulliProductAtoms n trueWeight falseWeight positive)
              (fun front =>
                decide
                  (trueCount n (true, front).2 +
                    (if (true, front).1 then 1 else 0) = k)) =
            FiniteProbRecord.eventMass
              (bernoulliProductAtoms n trueWeight falseWeight positive)
              (fun front => decide (trueCount n front + 1 = k)) := by
        apply FiniteProbRecord.eventMass_congr
        intro front
        exact trueCount_decide_true_bit n k front
      rw [hfalse_slice, htrue_slice]
      cases k with
      | zero =>
          have htrue0 :
              FiniteProbRecord.eventMass
                  (bernoulliProductAtoms n trueWeight falseWeight positive)
                  (fun front => decide (trueCount n front + 1 = 0)) =
                FiniteProbRecord.eventMass
                  (bernoulliProductAtoms n trueWeight falseWeight positive)
                  (fun _ => false) := by
            apply FiniteProbRecord.eventMass_congr
            intro front
            exact trueCount_succ_eq_zero_false n front
          rw [htrue0, FiniteProbRecord.eventMass_false, ih 0,
            Nat.mul_zero, Nat.add_zero]
          exact Eq.symm (binomTerm_succ_zero n trueWeight falseWeight)
      | succ k =>
          have htrue_succ :
              FiniteProbRecord.eventMass
                  (bernoulliProductAtoms n trueWeight falseWeight positive)
                  (fun front => decide (trueCount n front + 1 = k + 1)) =
                FiniteProbRecord.eventMass
                  (bernoulliProductAtoms n trueWeight falseWeight positive)
                  (fun front => decide (trueCount n front = k)) := by
            apply FiniteProbRecord.eventMass_congr
            intro front
            exact trueCount_succ_inj_decide n k front
          rw [htrue_succ, ih (k + 1), ih k]
          have hterm := binomTerm_succ_succ n trueWeight falseWeight k
          rw [hterm]
          ac_rfl

theorem binomial_pmf (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (k : Fin (trials + 1)) :
    QProb.Equiv
      ((binomialDistro trials trueWeight falseWeight positive).pmf k)
      ⟨binomialWeight trials trueWeight falseWeight k,
        (binomialDistro trials trueWeight falseWeight positive).record.den,
        (binomialDistro trials trueWeight falseWeight positive).record.den_pos⟩ :=
  by
  simp [Distro.pmf, binomialDistro, ofFinWeights, FiniteProbRecord.probVal,
    QProb.Equiv, eventMass_finWeighted_singleton]

theorem binomialFromBernoulli_count_mass
    (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (k : Fin (trials + 1)) :
    FiniteProbRecord.eventMass
        (binomialFromBernoulli trials trueWeight falseWeight positive).record.atoms
        (FiniteProbRecord.singletonEvent k) =
      binomTerm trials trueWeight falseWeight k.val := by
  have hmap :
      FiniteProbRecord.eventMass
          (binomialFromBernoulli trials trueWeight falseWeight
            positive).record.atoms
          (FiniteProbRecord.singletonEvent k) =
        FiniteProbRecord.eventMass
          (bernoulliProductAtoms trials trueWeight falseWeight positive)
          (fun assignment => decide (trueCount trials assignment = k.val)) := by
    simp [binomialFromBernoulli, FiniteProbRecord.map, FiniteProduct.record,
      bernoulliProductAtoms]
    exact eventMass_map_trueCount trials _ k
  rw [hmap, trueCount_mass]

theorem binomialFromBernoulli_pmf (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (k : Fin (trials + 1)) :
    QProb.Equiv
      ((binomialFromBernoulli trials trueWeight falseWeight positive).pmf k)
      ⟨binomTerm trials trueWeight falseWeight k.val,
        (binomialFromBernoulli trials trueWeight falseWeight positive).record.den,
        (binomialFromBernoulli trials trueWeight falseWeight
          positive).record.den_pos⟩ := by
  simp [Distro.pmf, FiniteProbRecord.probVal, QProb.Equiv,
    binomialFromBernoulli_count_mass]

/-- Closed binomial weights and the Bernoulli-product count law agree as
PMFs: same numerator `C(n,k) trueWeight^k falseWeight^{n-k}` and same
denominator `(falseWeight + trueWeight)^n`. -/
theorem binomial_eq_fromBernoulli_pmf (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (k : Fin (trials + 1)) :
    QProb.Equiv
      ((binomialDistro trials trueWeight falseWeight positive).pmf k)
      ((binomialFromBernoulli trials trueWeight falseWeight positive).pmf k) := by
  refine QProb.equiv_trans (binomial_pmf trials trueWeight falseWeight
      positive k) ?_
  have hden := binomial_eq_fromBernoulli_den trials trueWeight falseWeight
    positive
  have hfrom := binomialFromBernoulli_pmf trials trueWeight falseWeight
    positive k
  refine QProb.equiv_trans ?_ (QProb.equiv_symm hfrom)
  simp [QProb.Equiv, binomialWeight, hden]

/-- The two presentations agree on the event `{trueCount = k}`, packaged
as a `QProb` rather than a raw Nat mass. -/
theorem binomial_eq_fromBernoulli_event (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (k : Fin (trials + 1)) :
    QProb.Equiv
      ((binomialDistro trials trueWeight falseWeight positive).record.probVal
        (FiniteProbRecord.singletonEvent k))
      ((binomialFromBernoulli trials trueWeight falseWeight
        positive).record.probVal
        (FiniteProbRecord.singletonEvent k)) :=
  binomial_eq_fromBernoulli_pmf trials trueWeight falseWeight positive k

/-- The binomial mean is `n * trueWeight / (falseWeight + trueWeight)`.  On
`Nat`, the `n = 0` case is zero because the exponent `n - 1` underflows and
the front factor `n` vanishes. -/
theorem binomial_mean (trials trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    QProb.Equiv
      (mean (binomialNatDistro trials trueWeight falseWeight positive))
      ⟨trials * trueWeight *
          (falseWeight + trueWeight) ^ (trials - 1),
        (falseWeight + trueWeight) ^ trials,
        Nat.pow_pos positive⟩ := by
  have hden := binomialDistro_den trials trueWeight falseWeight positive
  have hsum :
      weightedSum
          (natAtoms (binomialNatDistro trials trueWeight falseWeight
            positive)) =
        trials * trueWeight *
          (trueWeight + falseWeight) ^ (trials - 1) := by
    simp [natAtoms, binomialNatDistro, ofFin, binomialDistro, ofFinWeights]
    have hfin :=
      weightedSum_finWeighted (trials + 1)
        (binomialWeight trials trueWeight falseWeight)
    rw [hfin]
    have hcongr :
        natSum (trials + 1) (fun k =>
            k * finWeight
              (binomialWeight trials trueWeight falseWeight) k) =
          natSum (trials + 1) (fun k =>
            k * binomTerm trials trueWeight falseWeight k) := by
      apply natSum_congr
      intro k hk
      simp [finWeight, binomialWeight, hk]
    rw [hcongr, binomTerm_weighted_sum]
  simp [mean, rawMoment, QProb.Equiv, weightedPowSum_one]
  rw [hsum]
  have hden' :
      (binomialNatDistro trials trueWeight falseWeight positive).distro.record.den =
        (falseWeight + trueWeight) ^ trials :=
    hden
  rw [hden']
  simp [Nat.add_comm trueWeight falseWeight]

/-- The binomial PGF, evaluated at a whole number `s`, is
`(trueWeight * s + falseWeight)^n / (falseWeight + trueWeight)^n`. -/
theorem binomial_pgf_ofNat (trials trueWeight falseWeight s : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    QProb.Equiv
      (pgf (binomialNatDistro trials trueWeight falseWeight positive)
        (QProb.ofNat s))
      ⟨(trueWeight * s + falseWeight) ^ trials,
        (falseWeight + trueWeight) ^ trials,
        Nat.pow_pos positive⟩ := by
  have hatoms :
      (binomialNatDistro trials trueWeight falseWeight positive).distro.record.atoms =
        finWeighted (trials + 1)
          (binomialWeight trials trueWeight falseWeight) := by
    simp [binomialNatDistro, ofFin, binomialDistro, ofFinWeights]
  have hnum :
      QProb.Equiv
        (QProb.listSum
          ((binomialNatDistro trials trueWeight falseWeight
              positive).distro.record.atoms.map fun atom =>
            QProb.scale atom.2
              (qpow (QProb.ofNat s)
                ((binomialNatDistro trials trueWeight falseWeight
                    positive).embed atom.1))))
        (QProb.ofNat ((trueWeight * s + falseWeight) ^ trials)) := by
    rw [hatoms]
    have hsum :=
      listSum_scale_qpow_finWeighted (trials + 1)
        (binomialWeight trials trueWeight falseWeight) s
    have hterm :
        natSum (trials + 1) (fun i =>
            finWeight (binomialWeight trials trueWeight falseWeight) i *
              s ^ i) =
          (trueWeight * s + falseWeight) ^ trials := by
      have hcongr :
          natSum (trials + 1) (fun i =>
              finWeight (binomialWeight trials trueWeight falseWeight) i *
                s ^ i) =
            natSum (trials + 1) (fun i =>
              binomTerm trials trueWeight falseWeight i * s ^ i) := by
        apply natSum_congr
        intro i hi
        simp [finWeight, binomialWeight, hi]
      rw [hcongr, binomTerm_generating]
    exact QProb.equiv_trans hsum (by
      simp [QProb.Equiv, QProb.ofNat]
      exact hterm)
  have hden :
      QProb.Equiv
        (QProb.ofNat
          (binomialNatDistro trials trueWeight falseWeight
            positive).distro.record.den)
        (QProb.ofNat ((falseWeight + trueWeight) ^ trials)) := by
    simp [QProb.Equiv, QProb.ofNat]
    exact binomialDistro_den trials trueWeight falseWeight positive
  have hdiv :=
    QProb.div_congr hnum hden
      (binomialNatDistro trials trueWeight falseWeight
        positive).distro.record.den_pos
      (Nat.pow_pos positive)
  refine QProb.equiv_trans (by simpa [pgf] using hdiv) ?_
  simp [QProb.div, QProb.ofNat, QProb.Equiv]

/-- The binomial PGF at a nonnegative rational `s` is
`(trueWeight * s + falseWeight)^n / (falseWeight + trueWeight)^n`. -/
theorem binomial_pgf (trials trueWeight falseWeight : Nat) (s : QProb)
    (positive : 0 < falseWeight + trueWeight) :
    QProb.Equiv
      (pgf (binomialNatDistro trials trueWeight falseWeight positive) s)
      (QProb.div
        (qpow
          (QProb.add (QProb.mul (QProb.ofNat trueWeight) s)
            (QProb.ofNat falseWeight))
          trials)
        (QProb.ofNat ((falseWeight + trueWeight) ^ trials))
        (Nat.pow_pos positive)) := by
  have hatoms :
      (binomialNatDistro trials trueWeight falseWeight positive).distro.record.atoms =
        finWeighted (trials + 1)
          (binomialWeight trials trueWeight falseWeight) := by
    simp [binomialNatDistro, ofFin, binomialDistro, ofFinWeights]
  have hnum :
      QProb.Equiv
        (QProb.listSum
          ((binomialNatDistro trials trueWeight falseWeight
              positive).distro.record.atoms.map fun atom =>
            QProb.scale atom.2
              (qpow s
                ((binomialNatDistro trials trueWeight falseWeight
                    positive).embed atom.1))))
        (qpow
          (QProb.add (QProb.mul (QProb.ofNat trueWeight) s)
            (QProb.ofNat falseWeight))
          trials) := by
    rw [hatoms]
    have hsum :=
      listSum_scale_qpow_finWeighted_qprob trials
        (binomialWeight trials trueWeight falseWeight) s
    have hterm :
        natSum (trials + 1) (fun i =>
            finWeight (binomialWeight trials trueWeight falseWeight) i *
              s.num ^ i * s.den ^ (trials - i)) =
          (trueWeight * s.num + falseWeight * s.den) ^ trials := by
      have hcongr :
          natSum (trials + 1) (fun i =>
              finWeight (binomialWeight trials trueWeight falseWeight) i *
                s.num ^ i * s.den ^ (trials - i)) =
            natSum (trials + 1) (fun i =>
              binomTerm trials (trueWeight * s.num)
                (falseWeight * s.den) i) := by
        apply natSum_congr
        intro i hi
        simp [finWeight, binomialWeight, hi]
        exact binomTerm_homogenize trials trueWeight falseWeight
          s.num s.den i
      rw [hcongr, binomial_theorem]
    refine QProb.equiv_trans hsum ?_
    refine QProb.equiv_trans ?_ (QProb.equiv_symm
      (qpow_add_scaled trueWeight s falseWeight trials))
    simp [QProb.Equiv, hterm]
  have hden :
      QProb.Equiv
        (QProb.ofNat
          (binomialNatDistro trials trueWeight falseWeight
            positive).distro.record.den)
        (QProb.ofNat ((falseWeight + trueWeight) ^ trials)) := by
    simp [QProb.Equiv, QProb.ofNat]
    exact binomialDistro_den trials trueWeight falseWeight positive
  have hdiv :=
    QProb.div_congr hnum hden
      (binomialNatDistro trials trueWeight falseWeight
        positive).distro.record.den_pos
      (Nat.pow_pos positive)
  simpa [pgf] using hdiv

/-- Independent binomials with a common success/failure weight convolve
to the binomial of the summed trial count. -/
theorem binomialWeight_convolution (n m trueWeight falseWeight : Nat)
    (k : Fin (n + m + 1)) :
    convolutionWeight n m
        (binomialWeight n trueWeight falseWeight)
        (binomialWeight m trueWeight falseWeight) k =
      binomialWeight (n + m) trueWeight falseWeight k := by
  unfold convolutionWeight
  have hcongr :
      natSum (k.val + 1) (fun i =>
          finWeight (binomialWeight n trueWeight falseWeight) i *
            finWeight (binomialWeight m trueWeight falseWeight) (k.val - i)) =
        natSum (k.val + 1) (fun i =>
          (if i < n + 1 then binomTerm n trueWeight falseWeight i else 0) *
            (if k.val - i < m + 1 then
              binomTerm m trueWeight falseWeight (k.val - i) else 0)) := by
    apply natSum_congr
    intro i _
    simp [finWeight, binomialWeight]
  rw [hcongr, binomTerm_convolution n m trueWeight falseWeight k.val]
  simp [binomialWeight]

/-- The independent sum of two binomial distros with the same weights is
the binomial distro of the summed trial count. -/
theorem binomial_addFin_pmf (n m trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight)
    (k : Fin (n + m + 1)) :
    QProb.Equiv
      ((⟨addFin n m
          (binomialDistro n trueWeight falseWeight positive).record
          (binomialDistro m trueWeight falseWeight positive).record⟩
        : Distro (Fin (n + m + 1))).pmf k)
      ((binomialDistro (n + m) trueWeight falseWeight positive).pmf k) := by
  have hpmf_add :=
    addFin_pmf n m
      (binomialDistro n trueWeight falseWeight positive).record
      (binomialDistro m trueWeight falseWeight positive).record k
  have hatoms_n :
      (binomialDistro n trueWeight falseWeight positive).record.atoms =
        finWeighted (n + 1)
          (binomialWeight n trueWeight falseWeight) := by
    simp [binomialDistro, ofFinWeights]
  have hatoms_m :
      (binomialDistro m trueWeight falseWeight positive).record.atoms =
        finWeighted (m + 1)
          (binomialWeight m trueWeight falseWeight) := by
    simp [binomialDistro, ofFinWeights]
  have hslots :
      natSum (k.val + 1) (fun i =>
          finSlotMass (n + 1)
              (binomialDistro n trueWeight falseWeight positive).record.atoms i *
            finSlotMass (m + 1)
              (binomialDistro m trueWeight falseWeight positive).record.atoms
              (k.val - i)) =
        convolutionWeight n m
          (binomialWeight n trueWeight falseWeight)
          (binomialWeight m trueWeight falseWeight) k := by
    unfold convolutionWeight
    apply natSum_congr
    intro i _
    simp [hatoms_n, hatoms_m, finSlotMass_finWeighted]
  have hden :
      (binomialDistro n trueWeight falseWeight positive).record.den *
          (binomialDistro m trueWeight falseWeight positive).record.den =
        (binomialDistro (n + m) trueWeight falseWeight positive).record.den := by
    rw [binomialDistro_den, binomialDistro_den, binomialDistro_den,
      ← Nat.pow_add]
  have hclosed :=
    binomial_pmf (n + m) trueWeight falseWeight positive k
  refine QProb.equiv_trans hpmf_add ?_
  refine QProb.equiv_trans ?_ (QProb.equiv_symm hclosed)
  simp [QProb.Equiv, hslots, binomialWeight_convolution, hden, binomialWeight]

/-- A Bernoulli outcome is the one-trial binomial success count. -/
theorem bernoulliBit_pmf (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (value : Bool) :
    QProb.Equiv
      ((bernoulliDistro trueWeight falseWeight positive).pmf value)
      ((binomialDistro 1 trueWeight falseWeight positive).pmf
        (bernoulliBit value)) := by
  cases value with
  | false =>
      refine QProb.equiv_trans
        (bernoulli_pmf_false trueWeight falseWeight positive) ?_
      refine QProb.equiv_trans ?_
        (QProb.equiv_symm
          (binomial_pmf 1 trueWeight falseWeight positive
            (bernoulliBit false)))
      simp [bernoulliBit, binomialWeight, binomTerm, binomialDistro_den,
        QProb.Equiv, binom_zero_right, Nat.pow_zero, Nat.pow_one]
  | true =>
      refine QProb.equiv_trans
        (bernoulli_pmf_true trueWeight falseWeight positive) ?_
      refine QProb.equiv_trans ?_
        (QProb.equiv_symm
          (binomial_pmf 1 trueWeight falseWeight positive
            (bernoulliBit true)))
      simp [bernoulliBit, binomialWeight, binomTerm, binomialDistro_den,
        QProb.Equiv, binom_self, Nat.pow_one, Nat.pow_zero]

/-- The Bernoulli whole-number PGF is the one-trial binomial PGF. -/
theorem bernoulli_pgf_eq_binomial_one (trueWeight falseWeight s : Nat)
    (positive : 0 < falseWeight + trueWeight) :
    QProb.Equiv
      (pgf (bernoulliNatDistro trueWeight falseWeight positive)
        (QProb.ofNat s))
      (pgf (binomialNatDistro 1 trueWeight falseWeight positive)
        (QProb.ofNat s)) := by
  refine QProb.equiv_trans
    (bernoulli_pgf_ofNat trueWeight falseWeight s positive) ?_
  refine QProb.equiv_trans ?_
    (QProb.equiv_symm
      (binomial_pgf_ofNat 1 trueWeight falseWeight s positive))
  simp [QProb.Equiv, Nat.pow_one]
  ac_rfl

/-- Mapping the Bernoulli distro along `bernoulliBit` recovers the
one-trial binomial on every `Fin 2` event. -/
theorem bernoulli_map_binomial_one_event (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight)
    (event : Event (Fin 2)) :
    QProb.Equiv
      (((bernoulliDistro trueWeight falseWeight positive).map
        bernoulliBit).record.probVal event)
      ((binomialDistro 1 trueWeight falseWeight positive).record.probVal
        event) := by
  have hmap :=
    Distro.map_probVal
      (bernoulliDistro trueWeight falseWeight positive) bernoulliBit event
  have hfalse : bernoulliBit false = ⟨0, Nat.succ_pos 1⟩ := rfl
  have htrue : bernoulliBit true = ⟨1, Nat.lt_succ_self 1⟩ := rfl
  have hbernoulli :
      FiniteProbRecord.eventMass
          (bernoulliDistro trueWeight falseWeight positive).record.atoms
          (fun value => event (bernoulliBit value)) =
        (if event (bernoulliBit false) then falseWeight else 0) +
          (if event (bernoulliBit true) then trueWeight else 0) := by
    simp [bernoulliDistro]
    simpa using
      FiniteProbRecord.eventMass_pair false true falseWeight trueWeight
        (fun value => event (bernoulliBit value))
  have hatoms :
      (binomialDistro 1 trueWeight falseWeight positive).record.atoms =
        [(⟨0, Nat.succ_pos 1⟩, falseWeight),
          (⟨1, Nat.lt_succ_self 1⟩, trueWeight)] := by
    simp [binomialDistro, ofFinWeights, finWeighted, binomialWeight, binomTerm,
      binom_zero_right, binom_self, Nat.pow_zero, Nat.pow_one]
  have hbinomial :
      FiniteProbRecord.eventMass
          (binomialDistro 1 trueWeight falseWeight positive).record.atoms
          event =
        (if event (bernoulliBit false) then falseWeight else 0) +
          (if event (bernoulliBit true) then trueWeight else 0) := by
    rw [hatoms, FiniteProbRecord.eventMass_pair, hfalse, htrue]
  refine QProb.equiv_trans hmap ?_
  simp [FiniteProbRecord.probVal, QProb.Equiv, bernoulli_record_den,
    binomialDistro_den, Nat.pow_one]
  rw [hbernoulli, hbinomial]

/-- Mapping the Bernoulli distro along `bernoulliBit` recovers the
one-trial binomial on every `Fin 2` singleton. -/
theorem bernoulli_map_binomial_one_pmf (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (k : Fin 2) :
    QProb.Equiv
      (((bernoulliDistro trueWeight falseWeight positive).map
        bernoulliBit).pmf k)
      ((binomialDistro 1 trueWeight falseWeight positive).pmf k) := by
  simpa [Distro.pmf] using
    bernoulli_map_binomial_one_event trueWeight falseWeight positive
      (FiniteProbRecord.singletonEvent k)

/-- Mapping the one-trial binomial along `bernoulliOfBit` recovers the
Bernoulli distro on every Boolean event. -/
theorem binomial_one_map_bernoulli_event (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight)
    (event : Event Bool) :
    QProb.Equiv
      (((binomialDistro 1 trueWeight falseWeight positive).map
        bernoulliOfBit).record.probVal event)
      ((bernoulliDistro trueWeight falseWeight positive).record.probVal
        event) := by
  have hmap :=
    Distro.map_probVal
      (binomialDistro 1 trueWeight falseWeight positive) bernoulliOfBit event
  have hfwd :=
    bernoulli_map_binomial_one_event trueWeight falseWeight positive
      (fun k => event (bernoulliOfBit k))
  have hbit :=
    Distro.map_probVal
      (bernoulliDistro trueWeight falseWeight positive) bernoulliBit
      (fun k => event (bernoulliOfBit k))
  have hpreimage :
      (bernoulliDistro trueWeight falseWeight positive).record.probVal
          (fun value => event (bernoulliOfBit (bernoulliBit value))) =
        (bernoulliDistro trueWeight falseWeight positive).record.probVal
          event := by
    simp [FiniteProbRecord.probVal]
    apply FiniteProbRecord.eventMass_congr
    intro value
    simp [bernoulliOfBit_bit]
  refine QProb.equiv_trans hmap ?_
  refine QProb.equiv_trans (QProb.equiv_symm hfwd) ?_
  refine QProb.equiv_trans hbit ?_
  rw [hpreimage]
  exact QProb.equiv_refl _

/-- Mapping the one-trial binomial along `bernoulliOfBit` recovers the
Bernoulli distro on every Boolean singleton. -/
theorem binomial_one_map_bernoulli_pmf (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (value : Bool) :
    QProb.Equiv
      (((binomialDistro 1 trueWeight falseWeight positive).map
        bernoulliOfBit).pmf value)
      ((bernoulliDistro trueWeight falseWeight positive).pmf value) := by
  simpa [Distro.pmf] using
    binomial_one_map_bernoulli_event trueWeight falseWeight positive
      (FiniteProbRecord.singletonEvent value)

/-- Mapping Bernoulli to `Fin 2` and back along the bit section recovers
every Boolean event. -/
theorem bernoulli_map_bit_ofBit_event (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight)
    (event : Event Bool) :
    QProb.Equiv
      ((((bernoulliDistro trueWeight falseWeight positive).map
          bernoulliBit).map bernoulliOfBit).record.probVal event)
      ((bernoulliDistro trueWeight falseWeight positive).record.probVal
        event) :=
  Distro.map_section_probVal
    (bernoulliDistro trueWeight falseWeight positive)
    bernoulliBit bernoulliOfBit bernoulliOfBit_bit event

/-- Mapping Bernoulli to `Fin 2` and back along the bit section recovers
every Boolean singleton. -/
theorem bernoulli_map_bit_ofBit_pmf (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (value : Bool) :
    QProb.Equiv
      ((((bernoulliDistro trueWeight falseWeight positive).map
          bernoulliBit).map bernoulliOfBit).pmf value)
      ((bernoulliDistro trueWeight falseWeight positive).pmf value) :=
  Distro.map_section_pmf
    (bernoulliDistro trueWeight falseWeight positive)
    bernoulliBit bernoulliOfBit bernoulliOfBit_bit value

/-- Mapping the one-trial binomial to `Bool` and back along the bit
section recovers every `Fin 2` event. -/
theorem binomial_one_map_ofBit_bit_event (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight)
    (event : Event (Fin 2)) :
    QProb.Equiv
      ((((binomialDistro 1 trueWeight falseWeight positive).map
          bernoulliOfBit).map bernoulliBit).record.probVal event)
      ((binomialDistro 1 trueWeight falseWeight positive).record.probVal
        event) :=
  Distro.map_section_probVal
    (binomialDistro 1 trueWeight falseWeight positive)
    bernoulliOfBit bernoulliBit bernoulliBit_ofBit event

/-- Mapping the one-trial binomial to `Bool` and back along the bit
section recovers every `Fin 2` singleton. -/
theorem binomial_one_map_ofBit_bit_pmf (trueWeight falseWeight : Nat)
    (positive : 0 < falseWeight + trueWeight) (k : Fin 2) :
    QProb.Equiv
      ((((binomialDistro 1 trueWeight falseWeight positive).map
          bernoulliOfBit).map bernoulliBit).pmf k)
      ((binomialDistro 1 trueWeight falseWeight positive).pmf k) :=
  Distro.map_section_pmf
    (binomialDistro 1 trueWeight falseWeight positive)
    bernoulliOfBit bernoulliBit bernoulliBit_ofBit k

end Distros
end Probability
end Thesis
