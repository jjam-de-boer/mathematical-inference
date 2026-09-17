import Thesis.Probability.Combinatorics
import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability
namespace Distros

/-!
Named finite distros, presented as probability records.

A `Distro` is a finite common-denominator record together with the usual
event-probability interface and outcome relabelling.  A `NatDistro`
additionally embeds outcomes in `Nat`, which is the setting in which raw
moments, probability generating functions, Markov's inequality, and
witnessed variance live.

No constructor in this hierarchy introduces a continuous density.  Continuous
names such as Gaussian, beta, gamma, or chi-squared appear later only as
finite urn counterparts or as `n`-indexed families.
-/

open Combinatorics

/-- A finite probability distro on an arbitrary outcome type. -/
structure Distro (Ω : Type u) where
  record : FiniteProbRecord Ω

namespace Distro

/-- The probability mass of a singleton outcome. -/
def pmf [DecidableEq Ω] (μ : Distro Ω) (value : Ω) : QProb :=
  μ.record.probVal (FiniteProbRecord.singletonEvent value)

/-- The unit-cell urn presentation of a distro. -/
def toUrn (μ : Distro Ω) : UrnProb Ω :=
  μ.record.toUrn

/-- Record and urn presentations agree on every Boolean event. -/
theorem toUrn_agrees (μ : Distro Ω) :
    FiniteProbRecord.AgreesWith μ.record μ.toUrn :=
  μ.record.toUrn_agrees

/-- Every event probability of a distro is a probability in `[0, 1]`. -/
theorem probVal_bounds (μ : Distro Ω) (event : Event Ω) :
    QProb.LE QProb.zero (μ.record.probVal event) ∧
      QProb.LE (μ.record.probVal event) QProb.one :=
  μ.record.probVal_bounds event

/-- The whole space has probability one. -/
theorem normalization (μ : Distro Ω) :
    QProb.Equiv (μ.record.probVal topEvent) QProb.one :=
  μ.record.normalization

/-- Relabel outcomes, keeping the atom weights and the common denominator. -/
def map (μ : Distro Ω) (f : Ω → X) : Distro X where
  record := μ.record.map f

/-- Event probabilities are preserved under relabelling, evaluated on the
preimage. -/
theorem map_probVal (μ : Distro Ω) (f : Ω → X) (event : Event X) :
    QProb.Equiv ((μ.map f).record.probVal event)
      (μ.record.probVal (fun omega => event (f omega))) :=
  FiniteProbRecord.map_probVal μ.record f event

/-- Singleton masses after relabelling are the source masses of the
preimage. -/
theorem map_pmf [DecidableEq X] (μ : Distro Ω) (f : Ω → X) (value : X) :
    QProb.Equiv
      ((μ.map f).pmf value)
      (μ.record.probVal (fun omega =>
        FiniteProbRecord.singletonEvent value (f omega))) := by
  simpa [Distro.pmf] using
    map_probVal μ f (FiniteProbRecord.singletonEvent value)

end Distro

/-- A distro whose outcomes carry a natural-number embedding. -/
structure NatDistro (Ω : Type u) where
  distro : Distro Ω
  embed : Ω → Nat

/-- Canonical `Fin (n + 1)`-supported Nat-valued distro, embedding by `Fin.val`. -/
def ofFin (n : Nat) (record : FiniteProbRecord (Fin (n + 1))) :
    NatDistro (Fin (n + 1)) where
  distro := ⟨record⟩
  embed := Fin.val

/-- Relabel atoms by their numeric embedding. -/
def natAtoms (μ : NatDistro Ω) : List (Nat × Nat) :=
  μ.distro.record.atoms.map fun atom => (μ.embed atom.1, atom.2)

theorem weightTotal_natAtoms (μ : NatDistro Ω) :
    weightTotal (natAtoms μ) = FiniteProbRecord.totalMass μ.distro.record.atoms := by
  unfold natAtoms
  induction μ.distro.record.atoms with
  | nil => simp [weightTotal, FiniteProbRecord.totalMass]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      simp [weightTotal, FiniteProbRecord.totalMass, ih]

theorem weightTotal_natAtoms_den (μ : NatDistro Ω) :
    weightTotal (natAtoms μ) = μ.distro.record.den := by
  rw [weightTotal_natAtoms, μ.distro.record.total_mass]

theorem eventMass_embed (atoms : List (Ω × Nat)) (embed : Ω → Nat)
    (p : Nat → Bool) :
    FiniteProbRecord.eventMass atoms (fun value => p (embed value)) =
      weightTotal
        ((atoms.map fun atom => (embed atom.1, atom.2)).filter
          (fun pair => p pair.1)) := by
  induction atoms with
  | nil => simp [FiniteProbRecord.eventMass, weightTotal]
  | cons atom atoms ih =>
      rcases atom with ⟨value, weight⟩
      cases hp : p (embed value) with
      | false =>
          simp [FiniteProbRecord.eventMass, List.map, hp, ih]
      | true =>
          simp [FiniteProbRecord.eventMass, List.map, hp, ih, weightTotal]

/-- Raw moment `E[X^power]` of a Nat-valued distro. -/
def rawMoment (μ : NatDistro Ω) (power : Nat) : QProb where
  num := weightedPowSum power (natAtoms μ)
  den := μ.distro.record.den
  den_pos := μ.distro.record.den_pos

/-- The mean `E[X]`. -/
def mean (μ : NatDistro Ω) : QProb :=
  rawMoment μ 1

/-- The second moment `E[X²]`. -/
def secondMoment (μ : NatDistro Ω) : QProb :=
  rawMoment μ 2

theorem mean_num (μ : NatDistro Ω) :
    (mean μ).num = weightedSum (natAtoms μ) := by
  simp [mean, rawMoment, weightedPowSum_one]

/-- Square of the mean, placed on the common denominator `den²`. -/
def meanSq (μ : NatDistro Ω) : QProb where
  num := (mean μ).num * (mean μ).num
  den := μ.distro.record.den * μ.distro.record.den
  den_pos := Nat.mul_pos μ.distro.record.den_pos μ.distro.record.den_pos

/-- Second moment on the same `den²` presentation as `meanSq`. -/
def secondMomentScaled (μ : NatDistro Ω) : QProb where
  num := (secondMoment μ).num * μ.distro.record.den
  den := μ.distro.record.den * μ.distro.record.den
  den_pos := Nat.mul_pos μ.distro.record.den_pos μ.distro.record.den_pos

theorem secondMomentScaled_equiv (μ : NatDistro Ω) :
    QProb.Equiv (secondMomentScaled μ) (secondMoment μ) := by
  simp [QProb.Equiv, secondMomentScaled, secondMoment, rawMoment]
  ac_rfl

/-- Cauchy--Schwarz supplies the inequality `meanSq ≤ secondMomentScaled`. -/
theorem meanSq_le_secondMoment (μ : NatDistro Ω) :
    QProb.LE (meanSq μ) (secondMomentScaled μ) := by
  apply QProb.le_of_same_den
  · rfl
  · have h := cauchy_schwarz_weights (natAtoms μ)
    have hden : weightTotal (natAtoms μ) = μ.distro.record.den :=
      weightTotal_natAtoms_den μ
    rw [hden] at h
    simp [meanSq, secondMomentScaled, secondMoment, rawMoment, mean,
      weightedPowSum_one, weightedPowSum_two]
    exact Nat.le_trans h (Nat.le_of_eq (Nat.mul_comm _ _))

/--
Variance `E[X²] - (E[X])²`, as a witnessed `QProb` subtraction.  The
inequality witness is the weighted Cauchy--Schwarz identity, so the
numerator is a natural number without introducing signed rationals.
-/
def variance (μ : NatDistro Ω) : QProb :=
  QProb.sub (secondMomentScaled μ) (meanSq μ) (meanSq_le_secondMoment μ)

/-- Iterate multiplication to form a nonnegative rational power. -/
def qpow (p : QProb) : Nat → QProb
  | 0 => QProb.one
  | n + 1 => QProb.mul p (qpow p n)

/-- Probability generating function `G(s) = E[s^X]`.  The argument `s` is a
nonnegative rational, so the value stays inside `QProb`. -/
def pgf (μ : NatDistro Ω) (s : QProb) : QProb :=
  QProb.div
    (QProb.listSum
      (μ.distro.record.atoms.map fun atom =>
        QProb.scale atom.2 (qpow s (μ.embed atom.1))))
    (QProb.ofNat μ.distro.record.den) μ.distro.record.den_pos

/-- Markov's inequality: `t P(X ≥ t) ≤ E[X]` for a positive threshold. -/
theorem markov (μ : NatDistro Ω) (t : Nat) (_ht : 0 < t) :
    QProb.LE
      (QProb.scale t
        (μ.distro.record.probVal (fun value => decide (t ≤ μ.embed value))))
      (mean μ) := by
  have hmass :
      FiniteProbRecord.eventMass μ.distro.record.atoms
          (fun value => decide (t ≤ μ.embed value)) =
        weightTotal
          ((natAtoms μ).filter (fun pair => decide (t ≤ pair.1))) := by
    simpa [natAtoms] using
      eventMass_embed μ.distro.record.atoms μ.embed (fun n => decide (t ≤ n))
  have hmarkov := markov_weights (natAtoms μ) t
  simp only [QProb.LE, QProb.scale, mean, rawMoment, FiniteProbRecord.probVal,
    weightedPowSum_one, hmass]
  exact Nat.mul_le_mul_right μ.distro.record.den hmarkov

/-- Markov in ratio form: `P(X ≥ t) ≤ E[X] / t`. -/
theorem markov_div (μ : NatDistro Ω) (t : Nat) (ht : 0 < t) :
    QProb.LE
      (μ.distro.record.probVal (fun value => decide (t ≤ μ.embed value)))
      (QProb.div (mean μ) (QProb.ofNat t) ht) := by
  have hscaled := markov μ t ht
  simp only [QProb.LE, QProb.div, QProb.ofNat, FiniteProbRecord.probVal,
    mean, rawMoment, QProb.scale] at hscaled ⊢
  have h := hscaled
  simpa [Nat.mul_comm t, Nat.mul_assoc] using h

/-- Squared deviation of an embedded outcome from a rational mean `num/den`. -/
def sqDev (embed : Ω → Nat) (meanNum meanDen : Nat) (value : Ω) : Nat :=
  let left := embed value * meanDen
  let right := meanNum
  let delta := if right ≤ left then left - right else right - left
  delta * delta

/-- Chebyshev as Markov on the Nat-valued squared deviation from the mean. -/
def deviationDistro (μ : NatDistro Ω) : NatDistro Ω where
  distro := μ.distro
  embed := sqDev μ.embed (mean μ).num μ.distro.record.den

/-- Chebyshev's inequality: a large squared deviation is Markov-controlled by
the mean squared deviation.  This is the finite constructive stand-in for a
CLT tail bound. -/
theorem chebyshev (μ : NatDistro Ω) (t : Nat) (ht : 0 < t) :
    QProb.LE
      (QProb.scale t
        (μ.distro.record.probVal (fun value =>
          decide (t ≤ sqDev μ.embed (mean μ).num μ.distro.record.den value))))
      (mean (deviationDistro μ)) :=
  markov (deviationDistro μ) t ht

/-- Independent sum of two Fin-supported Nat distros, by pushforward of the
product record along addition of values.  Convolution of the two PMFs is
the resulting PMF. -/
def addFin (n m : Nat)
    (μ : FiniteProbRecord (Fin (n + 1)))
    (ν : FiniteProbRecord (Fin (m + 1))) :
    FiniteProbRecord (Fin (n + m + 1)) :=
  (μ.product ν).map fun pair =>
    ⟨pair.1.val + pair.2.val, by
      have hμ : pair.1.val ≤ n := Nat.le_of_lt_succ pair.1.isLt
      have hν : pair.2.val ≤ m := Nat.le_of_lt_succ pair.2.isLt
      have : pair.1.val + pair.2.val ≤ n + m := Nat.add_le_add hμ hν
      exact Nat.lt_succ_of_le this⟩

/-- The independent-sum record keeps the product of the two denominators. -/
theorem addFin_den (n m : Nat)
    (μ : FiniteProbRecord (Fin (n + 1)))
    (ν : FiniteProbRecord (Fin (m + 1))) :
    (addFin n m μ ν).den = μ.den * ν.den := by
  simp [addFin, FiniteProbRecord.map, FiniteProbRecord.product]

/-- Enumerate `Fin n` with an explicit weight at each index. -/
def finWeighted : (n : Nat) → (Fin n → Nat) → List (Fin n × Nat)
  | 0, _ => []
  | n + 1, w =>
      (finWeighted n (fun i => w i.castSucc)).map (fun atom =>
        (atom.1.castSucc, atom.2)) ++
        [(Fin.last n, w (Fin.last n))]

def finWeight (w : Fin n → Nat) (i : Nat) : Nat :=
  if h : i < n then w ⟨i, h⟩ else 0

/-- Cauchy product of two Fin-supported weight functions, evaluated at
slot `k`.  This is the Nat-level convolution whose pushforward is `addFin`. -/
def convolutionWeight (n m : Nat)
    (μ : Fin (n + 1) → Nat) (ν : Fin (m + 1) → Nat)
    (k : Fin (n + m + 1)) : Nat :=
  natSum (k.val + 1) fun i =>
    finWeight μ i * finWeight ν (k.val - i)

theorem totalMass_finWeighted (n : Nat) (w : Fin n → Nat) :
    FiniteProbRecord.totalMass (finWeighted n w) =
      natSum n (finWeight w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [finWeighted, FiniteProbRecord.totalMass_append,
        FiniteProbRecord.totalMass_map_labels, FiniteProbRecord.totalMass,
        natSum_succ]
      have hprefix :
          FiniteProbRecord.totalMass
              (finWeighted n (fun i => w i.castSucc)) =
            natSum n (finWeight (fun i => w i.castSucc)) :=
        ih (fun i => w i.castSucc)
      have hfun :
          natSum n (finWeight (fun i => w i.castSucc)) =
            natSum n (finWeight w) := by
        apply natSum_congr
        intro i hi
        simp [finWeight, hi, Nat.lt_succ_of_lt hi]
      have hlast : finWeight w n = w (Fin.last n) := by
        simp [finWeight]
        exact congrArg w (Fin.ext rfl)
      rw [hprefix, hfun, hlast]
      ac_rfl

/-- Relabel `finWeighted` atoms by their `Fin.val` without changing weights. -/
theorem map_val_castSucc (n : Nat) (atoms : List (Fin n × Nat)) :
    atoms.map (fun atom => (atom.1.castSucc.val, atom.2)) =
      atoms.map (fun atom => (atom.1.val, atom.2)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      rcases atom with ⟨index, weight⟩
      simp

/-- First-moment evaluation of a Fin-supported weight function. -/
theorem weightedSum_finWeighted (n : Nat) (w : Fin n → Nat) :
    weightedSum
        ((finWeighted n w).map fun atom => (atom.1.val, atom.2)) =
      natSum n (fun i => i * finWeight w i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [finWeighted, List.map_append, List.map_cons, List.map_nil,
        weightedSum_append, weightedSum, Nat.add_zero]
      have hprefix := ih (fun i => w i.castSucc)
      have hcast := map_val_castSucc n (finWeighted n (fun i => w i.castSucc))
      have hfun :
          natSum n (fun i => i * finWeight (fun j => w j.castSucc) i) =
            natSum n (fun i => i * finWeight w i) := by
        apply natSum_congr
        intro i hi
        simp [finWeight, hi, Nat.lt_succ_of_lt hi]
      have hlast : finWeight w n = w (Fin.last n) := by
        simp [finWeight]
        exact congrArg w (Fin.ext rfl)
      have hmap :
          ((finWeighted n (fun i => w i.castSucc)).map
              (fun atom => (atom.1.castSucc, atom.2))).map
            (fun atom => (atom.1.val, atom.2)) =
          (finWeighted n (fun i => w i.castSucc)).map
            (fun atom => (atom.1.castSucc.val, atom.2)) := by
        simp [List.map_map]
      rw [hmap, hcast, hprefix, hfun]
      have hterm :
          w (Fin.last n) * (Fin.last n).val = n * finWeight w n := by
        rw [hlast, Fin.val_last]
        exact Nat.mul_comm _ _
      rw [natSum_succ, hterm]

theorem finWeighted_den_pos {n : Nat} (w : Fin n → Nat)
    (positive : 0 < natSum n (finWeight w)) :
    0 < FiniteProbRecord.totalMass (finWeighted n w) := by
  simpa [totalMass_finWeighted] using positive

/-- Package a finitely supported weight function on `Fin n` as a distro. -/
def ofFinWeights (n : Nat) (w : Fin n → Nat)
    (positive : 0 < natSum n (finWeight w)) :
    FiniteProbRecord (Fin n) where
  atoms := finWeighted n w
  den := FiniteProbRecord.totalMass (finWeighted n w)
  den_pos := finWeighted_den_pos w positive
  total_mass := rfl

/-- The independent sum of two Fin-weighted records has normaliser equal
to the product of the two weight totals, the Cauchy-product evaluation of
the convolution at the generating-function level `s = 1`. -/
theorem addFin_ofFinWeights_den (n m : Nat)
    (μ : Fin (n + 1) → Nat) (ν : Fin (m + 1) → Nat)
    (hμ : 0 < natSum (n + 1) (finWeight μ))
    (hν : 0 < natSum (m + 1) (finWeight ν)) :
    (addFin n m (ofFinWeights (n + 1) μ hμ)
        (ofFinWeights (m + 1) ν hν)).den =
      natSum (n + 1) (finWeight μ) * natSum (m + 1) (finWeight ν) := by
  simp [addFin_den, ofFinWeights, totalMass_finWeighted]

theorem eventMass_finWeighted_singleton (n : Nat) (w : Fin n → Nat)
    (k : Fin n) :
    FiniteProbRecord.eventMass (finWeighted n w)
      (FiniteProbRecord.singletonEvent k) = w k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      rw [finWeighted, FiniteProbRecord.eventMass_append,
        FiniteProbRecord.eventMass_map_labels]
      refine Fin.lastCases ?_ (fun earlier => ?_) k
      · have hprefix :
            FiniteProbRecord.eventMass
                (finWeighted n (fun i => w i.castSucc))
                (fun index =>
                  FiniteProbRecord.singletonEvent (Fin.last n) index.castSucc) =
              0 := by
          have hfalse :
              (fun index : Fin n =>
                FiniteProbRecord.singletonEvent (Fin.last n) index.castSucc) =
                fun _ => false := by
            funext index
            simp [FiniteProbRecord.singletonEvent,
              Fin.ne_of_lt index.castSucc_lt_last]
          rw [hfalse, FiniteProbRecord.eventMass_false]
        have hlast :
            FiniteProbRecord.eventMass [(Fin.last n, w (Fin.last n))]
                (FiniteProbRecord.singletonEvent (Fin.last n)) =
              w (Fin.last n) := by
          simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
        simp [hprefix, hlast]
      · have hlast :
            FiniteProbRecord.eventMass [(Fin.last n, w (Fin.last n))]
                (FiniteProbRecord.singletonEvent earlier.castSucc) = 0 := by
          have hne : Fin.last n ≠ earlier.castSucc :=
            (Fin.ne_of_lt earlier.castSucc_lt_last).symm
          simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
            decide_eq_false hne]
        have hprefix := ih (fun i => w i.castSucc) earlier
        have hcast :
            FiniteProbRecord.eventMass
                (finWeighted n (fun i => w i.castSucc))
                (fun index =>
                  FiniteProbRecord.singletonEvent earlier.castSucc
                    index.castSucc) =
              FiniteProbRecord.eventMass
                (finWeighted n (fun i => w i.castSucc))
                (FiniteProbRecord.singletonEvent earlier) := by
          apply FiniteProbRecord.eventMass_congr
          intro index
          simp [FiniteProbRecord.singletonEvent, Fin.castSucc_inj]
        simp [hlast, hcast, hprefix]

/-- Slot mass of a Fin-supported atom list: the event mass of `{i}`, or
zero when `i` lies outside the carrier.  Duplicate labels are summed, so
this is the Cauchy factor of an arbitrary finite record, not merely of a
`finWeighted` presentation. -/
def finSlotMass (n : Nat) (atoms : List (Fin n × Nat)) (i : Nat) : Nat :=
  if h : i < n then
    FiniteProbRecord.eventMass atoms (FiniteProbRecord.singletonEvent ⟨i, h⟩)
  else 0

theorem finSlotMass_nil (n i : Nat) :
    finSlotMass n [] i = 0 := by
  unfold finSlotMass
  split <;> simp [FiniteProbRecord.eventMass]

theorem finSlotMass_cons (n : Nat) (a : Fin n) (w : Nat)
    (rest : List (Fin n × Nat)) (i : Nat) :
    finSlotMass n ((a, w) :: rest) i =
      (if i = a.val then w else 0) + finSlotMass n rest i := by
  by_cases hlt : i < n
  · simp [finSlotMass, hlt, FiniteProbRecord.eventMass,
      FiniteProbRecord.singletonEvent, Fin.ext_iff]
    by_cases heq : i = a.val
    · simp [heq]
    · have hne' : a.val ≠ i := fun h => heq h.symm
      simp [heq, hne']
  · have hne : i ≠ a.val := fun heq => hlt (heq ▸ a.isLt)
    simp [finSlotMass, hlt, hne]

/-- The event `a + X = k` on a Fin-supported list is the slot `{k - a}`
when `a ≤ k`, and is empty otherwise. -/
theorem eventMass_add_eq_slot (m : Nat)
    (atoms : List (Fin (m + 1) × Nat)) (a k : Nat) :
    FiniteProbRecord.eventMass atoms
        (fun x => decide (a + x.val = k)) =
      if a ≤ k then finSlotMass (m + 1) atoms (k - a) else 0 := by
  by_cases hle : a ≤ k
  · by_cases htarget : k - a < m + 1
    · have hmass :
          FiniteProbRecord.eventMass atoms
              (fun x => decide (a + x.val = k)) =
            FiniteProbRecord.eventMass atoms
              (FiniteProbRecord.singletonEvent ⟨k - a, htarget⟩) := by
        apply FiniteProbRecord.eventMass_congr
        intro x
        simp [FiniteProbRecord.singletonEvent, Fin.ext_iff]
        cases Nat.decEq (a + x.val) k with
        | isTrue heq =>
            have hval : x.val = k - a := by
              have := congrArg (fun t => t - a) heq
              simpa [Nat.add_comm a, Nat.add_sub_cancel] using this
            have hadd : a + (k - a) = k := Nat.add_sub_of_le hle
            simp [hval, hadd]
        | isFalse hne =>
            have hval : x.val ≠ k - a := fun h =>
              hne (by rw [h, Nat.add_sub_of_le hle])
            simp [hne, hval]
      rw [hmass]
      simp [finSlotMass, hle, htarget]
    · have hfalse :
          FiniteProbRecord.eventMass atoms
              (fun x => decide (a + x.val = k)) =
            FiniteProbRecord.eventMass atoms (fun _ => false) := by
        apply FiniteProbRecord.eventMass_congr
        intro x
        have hne : a + x.val ≠ k := fun heq =>
          htarget (by
            have hval : x.val = k - a := by
              have := congrArg (fun t => t - a) heq
              simpa [Nat.add_comm a, Nat.add_sub_cancel] using this
            exact hval ▸ x.isLt)
        exact decide_eq_false hne
      rw [hfalse, FiniteProbRecord.eventMass_false]
      simp [finSlotMass, hle, htarget]
  · have hfalse :
        FiniteProbRecord.eventMass atoms
            (fun x => decide (a + x.val = k)) =
          FiniteProbRecord.eventMass atoms (fun _ => false) := by
      apply FiniteProbRecord.eventMass_congr
      intro x
      have hne : a + x.val ≠ k := fun heq =>
        hle (Nat.le_trans (Nat.le_add_right a x.val) (Nat.le_of_eq heq))
      exact decide_eq_false hne
    rw [hfalse, FiniteProbRecord.eventMass_false]
    simp [hle]

theorem natSum_zero_mul (n : Nat) (g : Nat → Nat) :
    natSum n (fun i => 0 * g i) = 0 := by
  have hcongr :
      natSum n (fun i => 0 * g i) = natSum n (fun _ => 0) := by
    apply natSum_congr
    intro i _
    simp
  rw [hcongr, natSum_zero_fun]

/-- Cauchy product of two Fin-supported records, as an event mass on the
sum of labels.  This is the slotwise convolution identity for `addFin`. -/
theorem eventMass_cartesian_add (n m : Nat)
    (left : List (Fin (n + 1) × Nat))
    (right : List (Fin (m + 1) × Nat)) (k : Nat) :
    FiniteProbRecord.eventMass
        (FiniteProbRecord.weightedCartesian left right)
        (fun pair => decide (pair.1.val + pair.2.val = k)) =
      natSum (k + 1) (fun i =>
        finSlotMass (n + 1) left i *
          finSlotMass (m + 1) right (k - i)) := by
  induction left with
  | nil =>
      simp [FiniteProbRecord.weightedCartesian, FiniteProbRecord.eventMass]
      have h0 :
          natSum (k + 1) (fun i =>
              finSlotMass (n + 1) [] i *
                finSlotMass (m + 1) right (k - i)) =
            natSum (k + 1) (fun _ => 0) := by
        apply natSum_congr
        intro i _
        rw [finSlotMass_nil]
        simp
      rw [h0, natSum_zero_fun]
  | cons atom rest ih =>
      rcases atom with ⟨a, w⟩
      have hdef :
          FiniteProbRecord.weightedCartesian ((a, w) :: rest) right =
            right.map (fun rightAtom =>
              ((a, rightAtom.1), w * rightAtom.2)) ++
              FiniteProbRecord.weightedCartesian rest right :=
        rfl
      rw [hdef, FiniteProbRecord.eventMass_append,
        FiniteProbRecord.eventMass_map_weight, ih]
      have hslice := eventMass_add_eq_slot m right a.val k
      rw [hslice]
      have hslots :
          natSum (k + 1) (fun i =>
              finSlotMass (n + 1) ((a, w) :: rest) i *
                finSlotMass (m + 1) right (k - i)) =
            natSum (k + 1) (fun i =>
              ((if i = a.val then w else 0) +
                  finSlotMass (n + 1) rest i) *
                finSlotMass (m + 1) right (k - i)) := by
        apply natSum_congr
        intro i _
        rw [finSlotMass_cons]
      have hspike :
          natSum (k + 1) (fun i =>
              (if i = a.val then w else 0) *
                finSlotMass (m + 1) right (k - i)) =
            if a.val ≤ k then
              w * finSlotMass (m + 1) right (k - a.val)
            else 0 := by
        have hsp :=
          natSum_spike (k + 1) a.val w
            (fun i => finSlotMass (m + 1) right (k - i))
        by_cases hle : a.val ≤ k
        · have hlt : a.val < k + 1 := Nat.lt_succ_of_le hle
          simpa [hle, hlt] using hsp
        · have hlt : ¬ a.val < k + 1 := fun h => hle (Nat.le_of_lt_succ h)
          simpa [hle, hlt] using hsp
      have hdistrib :
          natSum (k + 1) (fun i =>
              ((if i = a.val then w else 0) +
                  finSlotMass (n + 1) rest i) *
                finSlotMass (m + 1) right (k - i)) =
            natSum (k + 1) (fun i =>
                (if i = a.val then w else 0) *
                  finSlotMass (m + 1) right (k - i)) +
              natSum (k + 1) (fun i =>
                finSlotMass (n + 1) rest i *
                  finSlotMass (m + 1) right (k - i)) := by
        rw [← natSum_add]
        apply natSum_congr
        intro i _
        simp [Nat.add_mul]
      apply Eq.symm
      rw [hslots, hdistrib, hspike]
      by_cases hle : a.val ≤ k
      · simp [hle, Nat.mul_comm w]
      · simp [hle]

/-- Independent-sum singleton mass is the Cauchy product of the two slot
masses. -/
theorem addFin_singleton_mass (n m : Nat)
    (μ : FiniteProbRecord (Fin (n + 1)))
    (ν : FiniteProbRecord (Fin (m + 1)))
    (k : Fin (n + m + 1)) :
    FiniteProbRecord.eventMass (addFin n m μ ν).atoms
        (FiniteProbRecord.singletonEvent k) =
      natSum (k.val + 1) (fun i =>
        finSlotMass (n + 1) μ.atoms i *
          finSlotMass (m + 1) ν.atoms (k.val - i)) := by
  have hmap :
      FiniteProbRecord.eventMass (addFin n m μ ν).atoms
          (FiniteProbRecord.singletonEvent k) =
        FiniteProbRecord.eventMass
          (FiniteProbRecord.weightedCartesian μ.atoms ν.atoms)
          (fun pair => decide (pair.1.val + pair.2.val = k.val)) := by
    simp [addFin, FiniteProbRecord.map, FiniteProbRecord.product]
    induction FiniteProbRecord.weightedCartesian μ.atoms ν.atoms with
    | nil => rfl
    | cons atom atoms ih =>
        rcases atom with ⟨pair, weight⟩
        simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
          Fin.ext_iff, ih]
  rw [hmap, eventMass_cartesian_add]

theorem finSlotMass_finWeighted (n : Nat) (w : Fin n → Nat) (i : Nat) :
    finSlotMass n (finWeighted n w) i = finWeight w i := by
  by_cases hlt : i < n
  · simp [finSlotMass, finWeight, hlt, eventMass_finWeighted_singleton]
  · simp [finSlotMass, finWeight, hlt]

/-- On `ofFinWeights` presentations, slotwise convolution specialises to the
pointwise Cauchy product `convolutionWeight`. -/
theorem addFin_ofFinWeights_convolution (n m : Nat)
    (μ : Fin (n + 1) → Nat) (ν : Fin (m + 1) → Nat)
    (hμ : 0 < natSum (n + 1) (finWeight μ))
    (hν : 0 < natSum (m + 1) (finWeight ν))
    (k : Fin (n + m + 1)) :
    FiniteProbRecord.eventMass
        (addFin n m (ofFinWeights (n + 1) μ hμ)
          (ofFinWeights (m + 1) ν hν)).atoms
        (FiniteProbRecord.singletonEvent k) =
      convolutionWeight n m μ ν k := by
  rw [addFin_singleton_mass]
  unfold convolutionWeight
  apply natSum_congr
  intro i _
  simp [ofFinWeights, finSlotMass_finWeighted]

/-- Independent-sum singleton probabilities, as a `QProb` PMF.  The numerator
is the Cauchy product of slot masses and the denominator is the product of
the two record normalisers. -/
theorem addFin_pmf (n m : Nat)
    (μ : FiniteProbRecord (Fin (n + 1)))
    (ν : FiniteProbRecord (Fin (m + 1)))
    (k : Fin (n + m + 1)) :
    QProb.Equiv
      ((⟨addFin n m μ ν⟩ : Distro (Fin (n + m + 1))).pmf k)
      ⟨natSum (k.val + 1) (fun i =>
          finSlotMass (n + 1) μ.atoms i *
            finSlotMass (m + 1) ν.atoms (k.val - i)),
        μ.den * ν.den,
        Nat.mul_pos μ.den_pos ν.den_pos⟩ := by
  simp [Distro.pmf, FiniteProbRecord.probVal, QProb.Equiv]
  rw [addFin_singleton_mass, addFin_den]

/-- On `ofFinWeights` presentations, the independent-sum PMF is the Cauchy
product `convolutionWeight` over the product of the two weight totals. -/
theorem addFin_ofFinWeights_pmf (n m : Nat)
    (μ : Fin (n + 1) → Nat) (ν : Fin (m + 1) → Nat)
    (hμ : 0 < natSum (n + 1) (finWeight μ))
    (hν : 0 < natSum (m + 1) (finWeight ν))
    (k : Fin (n + m + 1)) :
    QProb.Equiv
      ((⟨addFin n m (ofFinWeights (n + 1) μ hμ)
          (ofFinWeights (m + 1) ν hν)⟩ : Distro (Fin (n + m + 1))).pmf k)
      ⟨convolutionWeight n m μ ν k,
        natSum (n + 1) (finWeight μ) * natSum (m + 1) (finWeight ν),
        Nat.mul_pos hμ hν⟩ := by
  have hmass :=
    addFin_ofFinWeights_convolution n m μ ν hμ hν k
  have hden := addFin_ofFinWeights_den n m μ ν hμ hν
  simp [Distro.pmf, FiniteProbRecord.probVal, QProb.Equiv, hmass, hden]

/-- Natural powers of a whole-number argument stay whole numbers. -/
theorem qpow_ofNat (s : Nat) :
    forall k : Nat, QProb.Equiv (qpow (QProb.ofNat s) k) (QProb.ofNat (s ^ k))
  | 0 => by
      simp [qpow, QProb.ofNat, QProb.one, QProb.Equiv]
  | k + 1 => by
      have ih := qpow_ofNat s k
      have hmul := QProb.mul_congr (QProb.equiv_refl (QProb.ofNat s)) ih
      simp only [qpow]
      refine QProb.equiv_trans hmul ?_
      simp [QProb.mul, QProb.ofNat, QProb.Equiv, Nat.pow_succ]
      ac_rfl

/-- Scaling a whole-number power recovers the monomial `w s^k`. -/
theorem scale_qpow_ofNat (w s k : Nat) :
    QProb.Equiv
      (QProb.scale w (qpow (QProb.ofNat s) k))
      (QProb.ofNat (w * s ^ k)) := by
  refine QProb.equiv_trans (QProb.scale_congr w (qpow_ofNat s k)) ?_
  simp [QProb.scale, QProb.ofNat, QProb.Equiv]

/-- Relabel `castSucc` atoms without changing the generating-function terms. -/
theorem map_scale_qpow_castSucc (n : Nat) (s : Nat)
    (atoms : List (Fin n × Nat)) :
    (atoms.map (fun atom => (atom.1.castSucc, atom.2))).map
        (fun atom =>
          QProb.scale atom.2 (qpow (QProb.ofNat s) atom.1.val)) =
      atoms.map (fun atom =>
        QProb.scale atom.2 (qpow (QProb.ofNat s) atom.1.val)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      rcases atom with ⟨index, weight⟩
      simp [ih]

/-- The PGF of a Fin-supported weight function, evaluated at a whole number
`s`, is the ordinary generating function `∑ w(i) s^i`. -/
theorem listSum_scale_qpow_finWeighted (n : Nat) (w : Fin n → Nat) (s : Nat) :
    QProb.Equiv
      (QProb.listSum
        ((finWeighted n w).map fun atom =>
          QProb.scale atom.2 (qpow (QProb.ofNat s) atom.1.val)))
      (QProb.ofNat (natSum n (fun i => finWeight w i * s ^ i))) := by
  induction n with
  | zero =>
      simp [finWeighted, QProb.listSum, QProb.ofNat, QProb.zero, QProb.Equiv,
        natSum]
  | succ n ih =>
      simp only [finWeighted, List.map_append, List.map_cons, List.map_nil]
      refine QProb.equiv_trans (QProb.listSum_append _ _) ?_
      have hmap :=
        map_scale_qpow_castSucc n s (finWeighted n (fun i => w i.castSucc))
      have hprefix :
          QProb.Equiv
            (QProb.listSum
              (((finWeighted n (fun i => w i.castSucc)).map
                  (fun atom => (atom.1.castSucc, atom.2))).map
                (fun atom =>
                  QProb.scale atom.2
                    (qpow (QProb.ofNat s) atom.1.val))))
            (QProb.ofNat
              (natSum n (fun i =>
                finWeight (fun j => w j.castSucc) i * s ^ i))) := by
        rw [hmap]
        exact ih (fun i => w i.castSucc)
      have hfun :
          natSum n (fun i =>
              finWeight (fun j => w j.castSucc) i * s ^ i) =
            natSum n (fun i => finWeight w i * s ^ i) := by
        apply natSum_congr
        intro i hi
        simp [finWeight, hi, Nat.lt_succ_of_lt hi]
      have hlastW : finWeight w n = w (Fin.last n) := by
        simp [finWeight]
        exact congrArg w (Fin.ext rfl)
      have hprefix' :
          QProb.Equiv
            (QProb.listSum
              (((finWeighted n (fun i => w i.castSucc)).map
                  (fun atom => (atom.1.castSucc, atom.2))).map
                (fun atom =>
                  QProb.scale atom.2
                    (qpow (QProb.ofNat s) atom.1.val))))
            (QProb.ofNat
              (natSum n (fun i => finWeight w i * s ^ i))) :=
        QProb.equiv_trans hprefix (by
          simp [QProb.Equiv, QProb.ofNat]
          exact hfun)
      have hlast :
          QProb.Equiv
            (QProb.listSum
              [QProb.scale (w (Fin.last n))
                (qpow (QProb.ofNat s) (Fin.last n).val)])
            (QProb.ofNat (w (Fin.last n) * s ^ n)) := by
        have hsing :
            QProb.Equiv
              (QProb.listSum
                [QProb.scale (w (Fin.last n))
                  (qpow (QProb.ofNat s) (Fin.last n).val)])
              (QProb.scale (w (Fin.last n))
                (qpow (QProb.ofNat s) n)) := by
          simp [QProb.listSum, QProb.add, QProb.zero, QProb.Equiv,
            QProb.scale, Fin.val_last]
        exact QProb.equiv_trans hsing (scale_qpow_ofNat (w (Fin.last n)) s n)
      have hadd := QProb.add_congr hprefix' hlast
      refine QProb.equiv_trans hadd ?_
      refine QProb.equiv_trans (QProb.ofNat_add _ _) ?_
      simp [QProb.Equiv, QProb.ofNat, natSum_succ, hlastW]

end Distros
end Probability
end Thesis
