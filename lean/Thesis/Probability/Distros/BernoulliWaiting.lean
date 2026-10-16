import Thesis.Probability.Distros.WaitingTime

namespace Thesis
namespace Probability
namespace Distros

/-!
Actual finite Bernoulli product windows for waiting-time distributions.
Trials are read in the last-coordinate-first order used by the recursive
product atom constructor.  A window with no success returns its length.
-/

open Combinatorics FiniteProduct

def waitingFailures : (trials : Nat) → (Fin trials → Bool) → Nat
  | 0, _ => 0
  | n + 1, assignment =>
      if assignment (Fin.last n) then 0
      else waitingFailures n (fun i => assignment i.castSucc) + 1

theorem waitingFailures_le (n : Nat) (assignment : Fin n → Bool) :
    waitingFailures n assignment ≤ n := by
  induction n with
  | zero => simp [waitingFailures]
  | succ n ih =>
      cases h : assignment (Fin.last n) with
      | false =>
          simp only [waitingFailures, h, Bool.false_eq_true, if_false]
          exact Nat.succ_le_succ (ih _)
      | true => simp [waitingFailures, h]

theorem waitingFailures_extend (n : Nat) (last : Bool) (front : Fin n → Bool) :
    waitingFailures (n + 1) (extend last front) =
      if last then 0 else waitingFailures n front + 1 := by
  simp [waitingFailures, extend_last, extend_castSucc]

theorem bernoulliProduct_totalMass (n a b : Nat) (positive : 0 < b + a) :
    FiniteProbRecord.totalMass (bernoulliProductAtoms n a b positive) = (b + a) ^ n := by
  have h := totalMass_atoms n (fun _ => Bool)
    (fun _ => (bernoulliDistro a b positive).record)
  simpa [bernoulliProductAtoms, bernoulliProduct_den] using h

/-- First-success occupancy on the actual independent product atoms.
The final slot is exactly the no-success event, not a normalized sum of
unscaled paths of differing lengths. -/
theorem waitingFailures_mass (n a b : Nat) (positive : 0 < b + a) (k : Nat) :
    FiniteProbRecord.eventMass (bernoulliProductAtoms n a b positive)
        (fun assignment => decide (waitingFailures n assignment = k)) =
      if k < n then a * b ^ k * (b + a) ^ (n - 1 - k)
      else if k = n then b ^ n else 0 := by
  induction n generalizing k with
  | zero =>
      simp [bernoulliProductAtoms, atoms, waitingFailures,
        FiniteProbRecord.eventMass, eq_comm]
  | succ n ih =>
      have hatoms : bernoulliProductAtoms (n + 1) a b positive =
          (FiniteProbRecord.weightedCartesian
            (bernoulliDistro a b positive).record.atoms
            (bernoulliProductAtoms n a b positive)).map
              (fun atom => (extend atom.1.1 atom.1.2, atom.2)) := rfl
      rw [hatoms, eventMass_map_extend]
      have hevent :
          FiniteProbRecord.eventMass
              (FiniteProbRecord.weightedCartesian
                (bernoulliDistro a b positive).record.atoms
                (bernoulliProductAtoms n a b positive))
              (fun pair => decide (waitingFailures (n + 1) (extend pair.1 pair.2) = k)) =
            FiniteProbRecord.eventMass
              (FiniteProbRecord.weightedCartesian
                (bernoulliDistro a b positive).record.atoms
                (bernoulliProductAtoms n a b positive))
              (fun pair => decide ((if pair.1 then 0 else waitingFailures n pair.2 + 1) = k)) := by
        apply FiniteProbRecord.eventMass_congr
        intro pair
        rw [waitingFailures_extend]
      rw [hevent, bernoulli_atoms, eventMass_bernoulli_cartesian]
      cases k with
      | zero =>
          simp
          rw [← show topEvent = (fun _ : Fin n → Bool => true) from rfl,
            FiniteProbRecord.eventMass_top, bernoulliProduct_totalMass]
          simp [FiniteProbRecord.eventMass_false]
      | succ k =>
          have hslice :
              FiniteProbRecord.eventMass (bernoulliProductAtoms n a b positive)
                  (fun front => decide (waitingFailures n front + 1 = k + 1)) =
                FiniteProbRecord.eventMass (bernoulliProductAtoms n a b positive)
                  (fun front => decide (waitingFailures n front = k)) := by
            apply FiniteProbRecord.eventMass_congr
            intro front
            simp
          simp only [Bool.false_eq_true, if_false, if_true]
          rw [hslice]
          simp only [Nat.zero_ne_add_one k, decide_false]
          rw [FiniteProbRecord.eventMass_false, Nat.mul_zero, Nat.add_zero, ih]
          by_cases hlt : k < n
          · have hexp : n - (k + 1) = n - 1 - k := by
              rw [Nat.sub_sub, Nat.add_comm k 1]
            simp [hlt, hexp, Nat.pow_succ]
            ac_rfl
          · by_cases heq : k = n
            · simp [heq, Nat.pow_succ, Nat.mul_comm]
            · simp [hlt, heq]

/-- Keep the no-success outcome distinct from a censored last cell. -/
def bernoulliWaitingRecord (n a b : Nat) (positive : 0 < b + a) :
    FiniteProbRecord (Fin (n + 1)) :=
  (record n (fun _ => Bool)
    (fun _ => (bernoulliDistro a b positive).record)).map
      (fun assignment =>
        ⟨waitingFailures n assignment, Nat.lt_succ_of_le (waitingFailures_le n assignment)⟩)

theorem bernoulliWaitingRecord_den (n a b : Nat) (positive : 0 < b + a) :
    (bernoulliWaitingRecord n a b positive).den = (b + a) ^ n := by
  simp [bernoulliWaitingRecord, FiniteProbRecord.map, record, bernoulliProduct_den]

theorem eventMass_map_waitingFailures (n : Nat)
    (source : List ((Fin n → Bool) × Nat)) (k : Fin (n + 1)) :
    FiniteProbRecord.eventMass
        (source.map fun atom =>
          (⟨waitingFailures n atom.1,
            Nat.lt_succ_of_le (waitingFailures_le n atom.1)⟩, atom.2))
        (FiniteProbRecord.singletonEvent k) =
      FiniteProbRecord.eventMass source
        (fun assignment => decide (waitingFailures n assignment = k.val)) := by
  induction source with
  | nil => rfl
  | cons atom rest ih =>
      rcases atom with ⟨assignment, weight⟩
      simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent, Fin.ext_iff, ih]

theorem bernoulliWaitingRecord_mass (n a b : Nat) (positive : 0 < b + a)
    (k : Fin (n + 1)) :
    FiniteProbRecord.eventMass (bernoulliWaitingRecord n a b positive).atoms
        (FiniteProbRecord.singletonEvent k) =
      if k.val < n then a * b ^ k.val * (b + a) ^ (n - 1 - k.val)
      else b ^ n := by
  change FiniteProbRecord.eventMass
    ((bernoulliProductAtoms n a b positive).map fun atom =>
      ((⟨waitingFailures n atom.1,
        Nat.lt_succ_of_le (waitingFailures_le n atom.1)⟩ : Fin (n + 1)), atom.2))
    (FiniteProbRecord.singletonEvent k) = _
  rw [eventMass_map_waitingFailures, waitingFailures_mass]
  by_cases hk : k.val < n
  · simp [hk]
  · have heq : k.val = n := by have := k.isLt; omega
    simp [heq]

theorem bernoulliWaitingRecord_pmf (n a b : Nat) (positive : 0 < b + a)
    (k : Fin (n + 1)) :
    QProb.Equiv
      ((bernoulliWaitingRecord n a b positive).probVal (FiniteProbRecord.singletonEvent k))
      ⟨if k.val < n then a * b ^ k.val * (b + a) ^ (n - 1 - k.val) else b ^ n,
        (b + a) ^ n, Nat.pow_pos positive⟩ := by
  simp [FiniteProbRecord.probVal, QProb.Equiv, bernoulliWaitingRecord_mass,
    bernoulliWaitingRecord_den]

/-- Censor the actual product-window outcome at the displayed failure cap. -/
def censorWaitingValue (cap : Nat) (k : Fin (cap + 2)) : Fin (cap + 1) :=
  ⟨min k.val cap, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def geometricCensoredFromBernoulli (cap a b : Nat) (ha : 0 < a) :
    Distro (Fin (cap + 1)) where
  record := (bernoulliWaitingRecord (cap + 1) a b (Nat.add_pos_right b ha)).map
    (censorWaitingValue cap)

theorem geometricCensoredFromBernoulli_pmf (cap a b : Nat) (ha : 0 < a)
    (k : Fin (cap + 1)) :
    QProb.Equiv ((geometricCensoredFromBernoulli cap a b ha).pmf k)
      ((geometricCensoredDistro cap a b ha).pmf k) := by
  let R := bernoulliWaitingRecord (cap + 1) a b (Nat.add_pos_right b ha)
  let event : Event (Fin (cap + 2)) :=
    fun x => FiniteProbRecord.singletonEvent k (censorWaitingValue cap x)
  have hmap : QProb.Equiv ((geometricCensoredFromBernoulli cap a b ha).pmf k)
      (R.probVal event) := by
    exact FiniteProbRecord.map_probVal R (censorWaitingValue cap)
      (FiniteProbRecord.singletonEvent k)
  refine QProb.equiv_trans hmap
    (QProb.equiv_trans ?_ (QProb.equiv_symm (geometricCensored_pmf cap a b ha k)))
  by_cases hk : k.val < cap
  · let j : Fin (cap + 2) := ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
    have hevent : event = FiniteProbRecord.singletonEvent j := by
      funext x
      simp only [event, FiniteProbRecord.singletonEvent, censorWaitingValue, Fin.ext_iff]
      by_cases hx : x.val ≤ cap
      · simp [Nat.min_eq_left hx, j]
      · have hge : cap ≤ x.val := Nat.le_of_not_le hx
        have hne : x.val ≠ k.val := by omega
        simp [Nat.min_eq_right hge, j, hne, Nat.ne_of_gt hk]
    rw [hevent]
    refine QProb.equiv_trans (bernoulliWaitingRecord_pmf (cap + 1) a b _ j) ?_
    simp [j, QProb.Equiv, geometricCensored_den, geometricCensoredWeight,
      geometricWeight, hk, Nat.lt_succ_of_lt hk, Nat.add_comm]
  · have hlast : k.val = cap := by have := k.isLt; omega
    let j : Fin (cap + 2) := ⟨cap, by omega⟩
    let last : Fin (cap + 2) := ⟨cap + 1, Nat.lt_succ_self _⟩
    have hevent : event = union (FiniteProbRecord.singletonEvent j)
        (FiniteProbRecord.singletonEvent last) := by
      funext x
      simp only [event, FiniteProbRecord.singletonEvent, censorWaitingValue,
        Fin.ext_iff, union, hlast]
      by_cases hx : x.val ≤ cap
      · by_cases heq : x.val = cap
        · rw [heq]
          simp only [j, last, Nat.min_self, eq_self,
            Nat.ne_of_lt (Nat.lt_succ_self cap), decide_true, decide_false, Bool.or_false]
        · have hne : x.val ≠ cap + 1 := by omega
          simp [Nat.min_eq_left hx, j, last, heq, hne]
      · have heq : x.val = cap + 1 := by have := x.isLt; omega
        rw [heq]
        simp only [j, last, Nat.min_eq_right (Nat.le_succ _), eq_self,
          Nat.succ_ne_self cap, decide_true, decide_false, Bool.or_true]
    have hdisjoint : disjoint (FiniteProbRecord.singletonEvent j)
        (FiniteProbRecord.singletonEvent last) := by
      intro x hx hy
      have hx' : x.val = cap := by
        simpa [FiniteProbRecord.singletonEvent, Fin.ext_iff, j] using hx
      have hy' : x.val = cap + 1 := by
        simpa [FiniteProbRecord.singletonEvent, Fin.ext_iff, last] using hy
      omega
    have hj : QProb.Equiv (R.probVal (FiniteProbRecord.singletonEvent j))
        ⟨a * b ^ cap, (a + b) ^ (cap + 1), Nat.pow_pos (Nat.add_pos_left ha _)⟩ := by
      refine QProb.equiv_trans (bernoulliWaitingRecord_pmf (cap + 1) a b _ j) ?_
      simp [QProb.Equiv, j, Nat.add_comm]
    have hl : QProb.Equiv (R.probVal (FiniteProbRecord.singletonEvent last))
        ⟨b ^ (cap + 1), (a + b) ^ (cap + 1), Nat.pow_pos (Nat.add_pos_left ha _)⟩ := by
      refine QProb.equiv_trans (bernoulliWaitingRecord_pmf (cap + 1) a b _ last) ?_
      simp [QProb.Equiv, last, Nat.add_comm]
    rw [hevent]
    refine QProb.equiv_trans (R.probVal_union_disjoint _ _ hdisjoint)
      (QProb.equiv_trans (QProb.add_congr hj hl)
        (QProb.equiv_trans (QProb.add_mk_same_den _ _ _ _) ?_))
    simp [QProb.Equiv, geometricCensored_den, geometricCensoredWeight,
      geometricWeight, hlast]

/-- Every Boolean event agrees with the actual censored Bernoulli product,
not only the singleton occupancy formulas. -/
theorem geometricCensoredFromBernoulli_event (cap a b : Nat) (ha : 0 < a)
    (event : Event (Fin (cap + 1))) :
    QProb.Equiv ((geometricCensoredFromBernoulli cap a b ha).record.probVal event)
      ((geometricCensoredDistro cap a b ha).record.probVal event) := by
  exact FiniteProbRecord.probVal_extensional_of_singletons _ _ (List.finRange (cap + 1))
    (finRange_nodup _) (fun value => List.mem_finRange value)
    (geometricCensoredFromBernoulli_pmf cap a b ha) event

def waitingSucceeded (cap : Nat) : Event (Fin (cap + 2)) :=
  fun k => decide (k.val ≤ cap)

/-- Success within the actual window has exactly the truncated
normalizer, before the common trial denominator is divided out. -/
theorem waitingSucceeded_mass (cap a b : Nat) (positive : 0 < b + a) :
    FiniteProbRecord.eventMass (bernoulliWaitingRecord (cap + 1) a b positive).atoms
        (waitingSucceeded cap) =
      a * geomSumHomog b (a + b) cap := by
  let last : Fin (cap + 2) := ⟨cap + 1, Nat.lt_succ_self _⟩
  have hcomp : (fun k => !(waitingSucceeded cap k)) =
      FiniteProbRecord.singletonEvent last := by
    funext k
    by_cases hk : k.val ≤ cap
    · have hne : k.val ≠ cap + 1 := by omega
      simp [waitingSucceeded, hk, FiniteProbRecord.singletonEvent, Fin.ext_iff, last, hne]
    · have heq : k.val = cap + 1 := by have := k.isLt; omega
      simp [waitingSucceeded, FiniteProbRecord.singletonEvent, Fin.ext_iff, last, heq]
  have hp := FiniteProbRecord.eventMass_add_complement
    (bernoulliWaitingRecord (cap + 1) a b positive).atoms (waitingSucceeded cap)
  rw [hcomp, bernoulliWaitingRecord_mass] at hp
  simp only [last, Nat.lt_irrefl, if_false] at hp
  rw [(bernoulliWaitingRecord (cap + 1) a b positive).total_mass,
    bernoulliWaitingRecord_den] at hp
  apply Nat.add_right_cancel (m := b ^ (cap + 1))
  exact hp.trans (by simpa [Nat.add_comm] using (geomSumHomog_bernoulli a b cap).symm)

/-- Condition the actual independent trial record on success in the
window, then read its failure count on the original finite support. -/
def geometricFromBernoulli (cap a b : Nat) (ha : 0 < a) : Distro (Fin (cap + 1)) where
  record :=
    let source := bernoulliWaitingRecord (cap + 1) a b (Nat.add_pos_right b ha)
    have supported : source.EventPositive (waitingSucceeded cap) := by
      change 0 < FiniteProbRecord.eventMass source.atoms (waitingSucceeded cap)
      rw [waitingSucceeded_mass]
      exact Nat.mul_pos ha (geomSumHomog_pos _ _ _ (Nat.add_pos_left ha _))
    (source.conditionOn (waitingSucceeded cap) supported).map (censorWaitingValue cap)

theorem geometricFromBernoulli_den (cap a b : Nat) (ha : 0 < a) :
    (geometricFromBernoulli cap a b ha).record.den =
      a * geomSumHomog b (a + b) cap := by
  simp [geometricFromBernoulli, FiniteProbRecord.map, FiniteProbRecord.conditionOn,
    waitingSucceeded_mass]

theorem geometricFromBernoulli_mass (cap a b : Nat) (ha : 0 < a)
    (k : Fin (cap + 1)) :
    FiniteProbRecord.eventMass (geometricFromBernoulli cap a b ha).record.atoms
      (FiniteProbRecord.singletonEvent k) = geometricWeight cap a b k := by
  let j : Fin (cap + 2) := ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
  have hevent : forall x : Fin (cap + 2),
      (waitingSucceeded cap x &&
          FiniteProbRecord.singletonEvent k (censorWaitingValue cap x)) =
        FiniteProbRecord.singletonEvent j x := by
    intro x
    by_cases hx : x.val ≤ cap
    · simp [waitingSucceeded, hx, FiniteProbRecord.singletonEvent,
        censorWaitingValue, Fin.ext_iff, Nat.min_eq_left hx, j]
    · have hne : x.val ≠ k.val := by have := k.isLt; omega
      simp [waitingSucceeded, hx, FiniteProbRecord.singletonEvent, Fin.ext_iff, j, hne]
  simp only [geometricFromBernoulli, FiniteProbRecord.map, FiniteProbRecord.conditionOn,
    FiniteProbRecord.eventMass_map_labels, FiniteProbRecord.eventMass_filter_event]
  rw [FiniteProbRecord.eventMass_congr _ _ _ hevent, bernoulliWaitingRecord_mass]
  simp [j, k.isLt, geometricWeight, Nat.add_comm]

theorem geometricFromBernoulli_pmf (cap a b : Nat) (ha : 0 < a)
    (k : Fin (cap + 1)) :
    QProb.Equiv ((geometricFromBernoulli cap a b ha).pmf k)
      ((geometricDistro cap a b ha).pmf k) := by
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (geometric_pmf cap a b ha k))
  simp [Distro.pmf, FiniteProbRecord.probVal, QProb.Equiv,
    geometricFromBernoulli_mass, geometricFromBernoulli_den, geometric_den]

theorem geometricFromBernoulli_event (cap a b : Nat) (ha : 0 < a)
    (event : Event (Fin (cap + 1))) :
    QProb.Equiv ((geometricFromBernoulli cap a b ha).record.probVal event)
      ((geometricDistro cap a b ha).record.probVal event) := by
  exact FiniteProbRecord.probVal_extensional_of_singletons _ _ (List.finRange (cap + 1))
    (finRange_nodup _) (fun value => List.mem_finRange value)
    (geometricFromBernoulli_pmf cap a b ha) event

end Distros
end Probability
end Thesis
