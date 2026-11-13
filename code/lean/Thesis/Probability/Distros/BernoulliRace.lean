import Thesis.Probability.Distros.BernoulliWaiting

namespace Thesis
namespace Probability
namespace Distros

/-!
Finite Bernoulli stopping races.  Stop when either the requested successes
or the failure threshold is reached.  The unused suffix is integrated out
on one fixed trial horizon, preserving the common Bernoulli denominator.
-/

open Combinatorics FiniteProduct

def bernoulliTrialList : (n : Nat) → (Fin n → Bool) → List Bool
  | 0, _ => []
  | n + 1, assignment =>
      assignment (Fin.last n) :: bernoulliTrialList n (fun i => assignment i.castSucc)

theorem bernoulliTrialList_extend (n : Nat) (last : Bool) (front : Fin n → Bool) :
    bernoulliTrialList (n + 1) (extend last front) = last :: bernoulliTrialList n front := by
  simp only [bernoulliTrialList, extend_last, extend_castSucc]

def bernoulliRaceFailures : List Bool → Nat → Nat → Nat
  | [], _, _ => 0
  | _ :: _, 0, _ => 0
  | _ :: _, _ + 1, 0 => 0
  | last :: front, r + 1, m + 1 =>
      if last then bernoulliRaceFailures front r (m + 1)
      else bernoulliRaceFailures front (r + 1) m + 1

theorem bernoulliRaceFailures_zero_successes (trials : List Bool) (m : Nat) :
    bernoulliRaceFailures trials 0 m = 0 := by cases trials <;> rfl

theorem bernoulliRaceFailures_zero_failures (trials : List Bool) (r : Nat) :
    bernoulliRaceFailures trials r 0 = 0 := by cases trials <;> cases r <;> rfl

theorem bernoulliRaceFailures_cons (last : Bool) (front : List Bool) (r m : Nat) :
    bernoulliRaceFailures (last :: front) (r + 1) (m + 1) =
      if last then bernoulliRaceFailures front r (m + 1)
      else bernoulliRaceFailures front (r + 1) m + 1 := rfl

/-- Terminal path atoms.  Boundary records keep the weight of the entire
unused suffix rather than treating terminal paths of unequal lengths as
equally normalized. -/
def bernoulliRaceAtoms (a b : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, m => [(0, (a + b) ^ (m - 1))]
  | r + 1, m =>
      Nat.rec [(0, (a + b) ^ r)]
        (fun m previous =>
          (bernoulliRaceAtoms a b r (m + 1)).map (fun atom => (atom.1, a * atom.2)) ++
            previous.map (fun atom => (atom.1 + 1, b * atom.2))) m

theorem bernoulliRaceAtoms_zero_successes (a b m : Nat) :
    bernoulliRaceAtoms a b 0 m = [(0, (a + b) ^ (m - 1))] := rfl

theorem bernoulliRaceAtoms_zero_failures (a b r : Nat) :
    bernoulliRaceAtoms a b (r + 1) 0 = [(0, (a + b) ^ r)] := rfl

theorem bernoulliRaceAtoms_step (a b r m : Nat) :
    bernoulliRaceAtoms a b (r + 1) (m + 1) =
      (bernoulliRaceAtoms a b r (m + 1)).map (fun atom => (atom.1, a * atom.2)) ++
        (bernoulliRaceAtoms a b (r + 1) m).map (fun atom => (atom.1 + 1, b * atom.2)) := rfl

theorem bernoulliRaceAtoms_totalMass (a b r m : Nat) :
    FiniteProbRecord.totalMass (bernoulliRaceAtoms a b r m) = (a + b) ^ (r + m - 1) := by
  induction r generalizing m with
  | zero => simp [bernoulliRaceAtoms_zero_successes, FiniteProbRecord.totalMass]
  | succ r ih =>
      induction m with
      | zero => simp [bernoulliRaceAtoms_zero_failures, FiniteProbRecord.totalMass]
      | succ m inner =>
          rw [bernoulliRaceAtoms_step, FiniteProbRecord.totalMass_append]
          rw [FiniteProbRecord.totalMass_map_weight
              (bernoulliRaceAtoms a b r (m + 1)) (fun k : Nat => k) a,
            FiniteProbRecord.totalMass_map_weight
              (bernoulliRaceAtoms a b (r + 1) m) (fun k : Nat => k + 1) b, ih, inner]
          have hfirst : r + (m + 1) - 1 = r + m := by omega
          have hsecond : r + 1 + m - 1 = r + m := by omega
          have hwhole : r + 1 + (m + 1) - 1 = r + m + 1 := by omega
          rw [hfirst, hsecond, hwhole, Nat.pow_succ, ← Nat.add_mul]
          ac_rfl

theorem bernoulliProduct_constant_mass (n a b : Nat) (positive : 0 < b + a) (flag : Bool) :
    FiniteProbRecord.eventMass (bernoulliProductAtoms n a b positive) (fun _ => flag) =
      if flag then (b + a) ^ n else 0 := by
  cases flag with
  | false => exact FiniteProbRecord.eventMass_false _
  | true =>
      rw [if_pos rfl]
      change FiniteProbRecord.eventMass _ topEvent = _
      rw [FiniteProbRecord.eventMass_top, bernoulliProduct_totalMass]

/-- Inspecting one leading trial on the actual independent product gives
the two Bernoulli branches with their genuine atom weights. -/
theorem bernoulliProduct_cons_mass (n a b : Nat) (positive : 0 < b + a)
    (event : Event (List Bool)) :
    FiniteProbRecord.eventMass (bernoulliProductAtoms (n + 1) a b positive)
        (fun assignment => event (bernoulliTrialList (n + 1) assignment)) =
      b * FiniteProbRecord.eventMass (bernoulliProductAtoms n a b positive)
          (fun assignment => event (false :: bernoulliTrialList n assignment)) +
        a * FiniteProbRecord.eventMass (bernoulliProductAtoms n a b positive)
          (fun assignment => event (true :: bernoulliTrialList n assignment)) := by
  have hatoms : bernoulliProductAtoms (n + 1) a b positive =
      (FiniteProbRecord.weightedCartesian
        (bernoulliDistro a b positive).record.atoms
        (bernoulliProductAtoms n a b positive)).map
          (fun atom => (extend atom.1.1 atom.1.2, atom.2)) := rfl
  rw [hatoms, eventMass_map_extend]
  simp only [bernoulliTrialList_extend]
  rw [bernoulli_atoms, eventMass_bernoulli_cartesian]

/-- Every race event is exactly the same event on the actual independent
Bernoulli product, with its unused suffix integrated out. -/
theorem bernoulliRace_eventMass (a b r m : Nat) (positive : 0 < b + a)
    (event : Event Nat) :
    FiniteProbRecord.eventMass (bernoulliProductAtoms (r + m - 1) a b positive)
        (fun assignment => event
          (bernoulliRaceFailures (bernoulliTrialList (r + m - 1) assignment) r m)) =
      FiniteProbRecord.eventMass (bernoulliRaceAtoms a b r m) event := by
  induction r generalizing m event with
  | zero =>
      simp only [bernoulliRaceAtoms_zero_successes, bernoulliRaceFailures_zero_successes,
        FiniteProbRecord.eventMass, Nat.add_zero]
      rw [bernoulliProduct_constant_mass]
      simp only [Nat.zero_add, Nat.add_comm a b]
  | succ r ih =>
      induction m generalizing event with
      | zero =>
          have hn : r + 1 + 0 - 1 = r := by omega
          rw [hn, bernoulliRaceAtoms_zero_failures]
          simp only [bernoulliRaceFailures_zero_failures, FiniteProbRecord.eventMass,
            Nat.add_zero]
          rw [bernoulliProduct_constant_mass]
          simp only [Nat.add_comm a b]
      | succ m inner =>
          have hn : r + 1 + (m + 1) - 1 = r + m + 1 := by omega
          rw [hn, bernoulliProduct_cons_mass (r + m) a b positive
            (fun trials => event (bernoulliRaceFailures trials (r + 1) (m + 1)))]
          simp only [bernoulliRaceFailures_cons, Bool.false_eq_true, if_false, if_true]
          rw [bernoulliRaceAtoms_step, FiniteProbRecord.eventMass_append,
            FiniteProbRecord.eventMass_map_weight
              (bernoulliRaceAtoms a b r (m + 1)) (fun k : Nat => k) a event,
            FiniteProbRecord.eventMass_map_weight
              (bernoulliRaceAtoms a b (r + 1) m) (fun k : Nat => k + 1) b event]
          have hfirst := ih (m + 1) event
          have hsecond := inner (fun k => event (k + 1))
          have hfirstN : r + (m + 1) - 1 = r + m := by omega
          have hsecondN : r + 1 + m - 1 = r + m := by omega
          rw [hfirstN] at hfirst
          rw [hsecondN] at hsecond
          rw [hfirst, hsecond]
          ac_rfl

/-- The same stopping law as a finite probability record. -/
def bernoulliRaceRecord (a b r m : Nat) (positive : 0 < b + a) : FiniteProbRecord Nat where
  atoms := bernoulliRaceAtoms a b r m
  den := (a + b) ^ (r + m - 1)
  den_pos := Nat.pow_pos (by simpa [Nat.add_comm] using positive)
  total_mass := bernoulliRaceAtoms_totalMass a b r m

def bernoulliRaceFromProduct (a b r m : Nat) (positive : 0 < b + a) : FiniteProbRecord Nat :=
  (record (r + m - 1) (fun _ => Bool)
    (fun _ => (bernoulliDistro a b positive).record)).map
      (fun assignment =>
        bernoulliRaceFailures (bernoulliTrialList (r + m - 1) assignment) r m)

theorem bernoulliRaceFromProduct_event (a b r m : Nat) (positive : 0 < b + a)
    (event : Event Nat) :
    QProb.Equiv ((bernoulliRaceFromProduct a b r m positive).probVal event)
      ((bernoulliRaceRecord a b r m positive).probVal event) := by
  refine QProb.equiv_trans (FiniteProbRecord.map_probVal
    (record (r + m - 1) (fun _ => Bool)
      (fun _ => (bernoulliDistro a b positive).record))
    (fun assignment => bernoulliRaceFailures (bernoulliTrialList (r + m - 1) assignment) r m)
    event) ?_
  change FiniteProbRecord.eventMass (bernoulliProductAtoms (r + m - 1) a b positive)
      (fun assignment => event
        (bernoulliRaceFailures (bernoulliTrialList (r + m - 1) assignment) r m)) *
        (a + b) ^ (r + m - 1) =
    FiniteProbRecord.eventMass (bernoulliRaceAtoms a b r m) event *
      denominator (r + m - 1) (fun _ => Bool) (fun _ => (bernoulliDistro a b positive).record)
  rw [bernoulliRace_eventMass, bernoulliProduct_den]
  simp only [Nat.add_comm a b]

theorem eventMass_map_successor_zero (source : List (Nat × Nat)) (factor : Nat) :
    FiniteProbRecord.eventMass
        (source.map fun atom => (atom.1 + 1, factor * atom.2))
        (FiniteProbRecord.singletonEvent 0) = 0 := by
  rw [FiniteProbRecord.eventMass_map_weight source (fun k : Nat => k + 1) factor]
  have hzero : forall k : Nat, k + 1 ≠ 0 := fun k => Nat.ne_of_gt (Nat.succ_pos k)
  simp only [FiniteProbRecord.singletonEvent, hzero, decide_false,
    FiniteProbRecord.eventMass_false, Nat.mul_zero]

theorem eventMass_map_successor (source : List (Nat × Nat)) (factor k : Nat) :
    FiniteProbRecord.eventMass
        (source.map fun atom => (atom.1 + 1, factor * atom.2))
        (FiniteProbRecord.singletonEvent (k + 1)) =
      factor * FiniteProbRecord.eventMass source (FiniteProbRecord.singletonEvent k) := by
  rw [FiniteProbRecord.eventMass_map_weight source (fun k : Nat => k + 1) factor]
  simp only [FiniteProbRecord.singletonEvent, Nat.add_right_cancel_iff]
  rfl

/-- Ordinary occupancy of the stopping race is the corrected closed
negative-binomial term.  The last cell is reserved for failure exhaustion. -/
theorem bernoulliRace_mass_success (a b r m k : Nat) (hk : k < m) :
    FiniteProbRecord.eventMass (bernoulliRaceAtoms a b (r + 1) m)
        (FiniteProbRecord.singletonEvent k) =
      binom (k + r) k * a ^ (r + 1) * b ^ k * (a + b) ^ (m - 1 - k) := by
  induction r generalizing m k with
  | zero =>
      induction m generalizing k with
      | zero => exact False.elim ((Nat.not_lt_zero k) hk)
      | succ m inner =>
          rw [bernoulliRaceAtoms_step, FiniteProbRecord.eventMass_append,
            FiniteProbRecord.eventMass_map_weight
              (bernoulliRaceAtoms a b 0 (m + 1)) (fun k : Nat => k) a]
          cases k with
          | zero =>
              rw [eventMass_map_successor_zero, bernoulliRaceAtoms_zero_successes]
              simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
          | succ k =>
              rw [eventMass_map_successor, bernoulliRaceAtoms_zero_successes]
              simp only [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
                Nat.zero_ne_add_one k, decide_false, Nat.zero_add]
              rw [inner k (Nat.succ_lt_succ_iff.mp hk)]
              have hexp : m - (k + 1) = m - 1 - k := by
                rw [Nat.sub_sub, Nat.add_comm k 1]
              simp only [Nat.add_zero, binom_self, Nat.one_mul,
                Nat.add_sub_cancel, hexp, Nat.pow_succ]
              ac_rfl
  | succ r ih =>
      induction m generalizing k with
      | zero => exact False.elim ((Nat.not_lt_zero k) hk)
      | succ m inner =>
          rw [bernoulliRaceAtoms_step, FiniteProbRecord.eventMass_append,
            FiniteProbRecord.eventMass_map_weight
              (bernoulliRaceAtoms a b (r + 1) (m + 1)) (fun k : Nat => k) a]
          cases k with
          | zero =>
              rw [eventMass_map_successor_zero, ih (m + 1) 0 (Nat.succ_pos _)]
              simp only [Nat.zero_add, binom_zero_right, Nat.one_mul, Nat.pow_zero,
                Nat.mul_one, Nat.add_zero, Nat.sub_zero, Nat.add_sub_cancel,
                Nat.pow_succ]
              ac_rfl
          | succ k =>
              rw [eventMass_map_successor, ih (m + 1) (k + 1) hk,
                inner k (Nat.succ_lt_succ_iff.mp hk)]
              have hfirst : k + 1 + r = k + r + 1 := by omega
              have hsecond : k + (r + 1) = k + r + 1 := by omega
              have hwhole : k + 1 + (r + 1) = (k + r + 1) + 1 := by omega
              have hexp : m - (k + 1) = m - 1 - k := by
                rw [Nat.sub_sub, Nat.add_comm k 1]
              simp only [hfirst, hsecond, hwhole, Nat.add_sub_cancel, hexp,
                binom_succ_succ, Nat.pow_succ, Nat.add_mul, Nat.mul_add]
              ac_rfl

/-- The failure-exhaustion cell is the complete complementary stopped-path
sum, on the same trial denominator as the ordinary occupancies. -/
theorem bernoulliRace_mass_failure (a b r m : Nat) :
    FiniteProbRecord.eventMass (bernoulliRaceAtoms a b (r + 1) (m + 1))
        (FiniteProbRecord.singletonEvent (m + 1)) =
      b ^ (m + 1) * nbSumHomog (m + 1) a (a + b) r := by
  induction r generalizing m with
  | zero =>
      induction m with
      | zero =>
          rw [bernoulliRaceAtoms_step, FiniteProbRecord.eventMass_append,
            FiniteProbRecord.eventMass_map_weight
              (bernoulliRaceAtoms a b 0 1) (fun k : Nat => k) a,
            eventMass_map_successor, bernoulliRaceAtoms_zero_successes,
            bernoulliRaceAtoms_zero_failures]
          simp only [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
            Nat.zero_ne_add_one 0, decide_false, eq_self, decide_true,
            Nat.add_zero, Nat.zero_add]
          simp [nbSumHomog, natSum]
      | succ m inner =>
          rw [bernoulliRaceAtoms_step, FiniteProbRecord.eventMass_append,
            FiniteProbRecord.eventMass_map_weight
              (bernoulliRaceAtoms a b 0 (m + 1 + 1)) (fun k : Nat => k) a,
            eventMass_map_successor, bernoulliRaceAtoms_zero_successes, inner]
          simp only [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
            Nat.zero_ne_add_one (m + 1), decide_false]
          simp [nbSumHomog, natSum, Nat.pow_succ, Nat.mul_comm]
  | succ r ih =>
      induction m with
      | zero =>
          rw [bernoulliRaceAtoms_step, FiniteProbRecord.eventMass_append,
            FiniteProbRecord.eventMass_map_weight
              (bernoulliRaceAtoms a b (r + 1) 1) (fun k : Nat => k) a,
            eventMass_map_successor, bernoulliRaceAtoms_zero_failures, ih 0]
          simp only [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
            eq_self, decide_true, if_true, Nat.add_zero, Nat.zero_add,
            Nat.pow_one, nbSumHomog_one_success]
          rw [geomSumHomog_head]
          simp only [Nat.mul_add]
          ac_rfl
      | succ m inner =>
          rw [bernoulliRaceAtoms_step, FiniteProbRecord.eventMass_append,
            FiniteProbRecord.eventMass_map_weight
              (bernoulliRaceAtoms a b (r + 1) (m + 1 + 1)) (fun k : Nat => k) a,
            eventMass_map_successor, ih (m + 1), inner, nbSumHomog_pascal]
          simp only [Nat.pow_succ, Nat.mul_add]
          ac_rfl

theorem bernoulliRace_mass_occupancy (a b r cap : Nat) (hr : 0 < r)
    (k : Fin (cap + 1)) :
    FiniteProbRecord.eventMass (bernoulliRaceAtoms a b r (cap + 1))
        (FiniteProbRecord.singletonEvent k.val) = negativeBinomialWeight r cap a b k := by
  cases r with
  | zero => exact False.elim ((Nat.not_lt_zero _) hr)
  | succ r =>
      simpa [negativeBinomialWeight, Nat.add_assoc] using
        bernoulliRace_mass_success a b r (cap + 1) k.val k.isLt

theorem bernoulliRace_mass_tail (a b r cap : Nat) (hr : 0 < r) :
    FiniteProbRecord.eventMass (bernoulliRaceAtoms a b r (cap + 1))
        (FiniteProbRecord.singletonEvent (cap + 1)) =
      negativeBinomialCensorTail r cap a b := by
  cases r with
  | zero => exact False.elim ((Nat.not_lt_zero _) hr)
  | succ r =>
      rw [bernoulliRace_mass_failure]
      unfold nbSumHomog negativeBinomialCensorTail
      apply congrArg (fun mass => b ^ (cap + 1) * mass)
      apply natSum_congr
      intro k _
      have hindex : k + (cap + 1) - 1 = cap + k := by omega
      simp only [hindex, Nat.add_sub_cancel]

/-- All generated labels stay inside the displayed failure threshold. -/
theorem bernoulliRaceAtoms_support (a b r m : Nat) (value weight : Nat)
    (member : (value, weight) ∈ bernoulliRaceAtoms a b r m) : value ≤ m := by
  induction r generalizing m value weight with
  | zero =>
      rw [bernoulliRaceAtoms_zero_successes] at member
      have same : (value, weight) = (0, (a + b) ^ (m - 1)) := List.mem_singleton.mp member
      have label : value = 0 := congrArg Prod.fst same
      rw [label]
      exact Nat.zero_le _
  | succ r ih =>
      induction m generalizing value weight with
      | zero =>
          rw [bernoulliRaceAtoms_zero_failures] at member
          have same : (value, weight) = (0, (a + b) ^ r) := List.mem_singleton.mp member
          have label : value = 0 := congrArg Prod.fst same
          rw [label]
          exact Nat.zero_le _
      | succ m inner =>
          rw [bernoulliRaceAtoms_step] at member
          rcases List.mem_append.mp member with left | right
          · rcases List.mem_map.mp left with ⟨atom, source, same⟩
            have label : atom.1 = value := congrArg Prod.fst same
            exact label ▸ ih (m + 1) atom.1 atom.2 source
          · rcases List.mem_map.mp right with ⟨atom, source, same⟩
            have label : atom.1 + 1 = value := congrArg Prod.fst same
            exact label ▸ Nat.succ_le_succ (inner atom.1 atom.2 source)

/-- Finite lower-tail mass is the sum of its singleton masses, even when
the atom list contains repeated labels or zero weights. -/
theorem eventMass_lt_eq_natSum (source : List (Nat × Nat)) (n : Nat) :
    FiniteProbRecord.eventMass source (fun value => decide (value < n)) =
      natSum n (fun k => FiniteProbRecord.eventMass source (FiniteProbRecord.singletonEvent k)) := by
  induction source with
  | nil => simp [FiniteProbRecord.eventMass, natSum_zero_fun]
  | cons atom rest ih =>
      rcases atom with ⟨value, weight⟩
      have hsum :
          natSum n (fun k => FiniteProbRecord.eventMass ((value, weight) :: rest)
            (FiniteProbRecord.singletonEvent k)) =
            natSum n (fun k => (if k = value then weight else 0) * 1 +
              FiniteProbRecord.eventMass rest (FiniteProbRecord.singletonEvent k)) := by
        apply natSum_congr
        intro k _
        by_cases same : k = value
        · subst k
          simp [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
        · simp only [FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
            Ne.symm same, same, decide_false, Bool.false_eq_true, if_false,
            Nat.zero_mul, Nat.zero_add]
      rw [hsum, natSum_add, natSum_spike, ← ih]
      by_cases selected : value < n <;>
        simp [FiniteProbRecord.eventMass, selected]

theorem eventMass_lt_add_last (source : List (Nat × Nat)) (m : Nat)
    (support : forall value weight, (value, weight) ∈ source → value ≤ m) :
    FiniteProbRecord.eventMass source (fun value => decide (value < m)) +
        FiniteProbRecord.eventMass source (FiniteProbRecord.singletonEvent m) =
      FiniteProbRecord.totalMass source := by
  induction source with
  | nil => rfl
  | cons atom rest ih =>
      rcases atom with ⟨value, weight⟩
      have bounded := support value weight List.mem_cons_self
      have tail := ih (fun value weight member => support value weight (List.mem_cons_of_mem _ member))
      rcases Nat.lt_or_eq_of_le bounded with selected | last
      · simp only [FiniteProbRecord.eventMass, FiniteProbRecord.totalMass,
          FiniteProbRecord.singletonEvent, selected, decide_true, if_true,
          Nat.ne_of_lt selected, decide_false, Bool.false_eq_true, if_false]
        rw [Nat.add_assoc, tail]
      · simp only [FiniteProbRecord.eventMass, FiniteProbRecord.totalMass,
          FiniteProbRecord.singletonEvent, last, Nat.lt_irrefl, decide_false,
          Bool.false_eq_true, if_false,
          eq_self, decide_true, if_true]
        rw [← tail]
        ac_rfl

theorem bernoulliRace_success_mass (a b r cap : Nat) (hr : 0 < r) :
    FiniteProbRecord.eventMass (bernoulliRaceAtoms a b r (cap + 1))
        (fun value => decide (value < cap + 1)) =
      a ^ r * nbSumHomog r b (a + b) cap := by
  rw [eventMass_lt_eq_natSum]
  have hsum :
      natSum (cap + 1) (fun k => FiniteProbRecord.eventMass
          (bernoulliRaceAtoms a b r (cap + 1)) (FiniteProbRecord.singletonEvent k)) =
        natSum (cap + 1) (finWeight (negativeBinomialWeight r cap a b)) := by
    apply natSum_congr
    intro k hk
    simpa only [finWeight, dif_pos hk] using bernoulliRace_mass_occupancy a b r cap hr ⟨k, hk⟩
  rw [hsum, negativeBinomialWeight_sum]

/-- Ordinary NB occupancy and the failure tail exhaust exactly the fixed
Bernoulli horizon.  This is an equality of natural masses before division. -/
theorem negativeBinomialCensored_exhaustion (a b r cap : Nat) (hr : 0 < r) :
    a ^ r * nbSumHomog r b (a + b) cap + negativeBinomialCensorTail r cap a b =
      (a + b) ^ (cap + r) := by
  have partition := eventMass_lt_add_last (bernoulliRaceAtoms a b r (cap + 1)) (cap + 1)
    (bernoulliRaceAtoms_support a b r (cap + 1))
  rw [bernoulliRace_success_mass a b r cap hr, bernoulliRace_mass_tail a b r cap hr,
    bernoulliRaceAtoms_totalMass] at partition
  have horizon : r + (cap + 1) - 1 = cap + r := by omega
  simpa only [horizon] using partition

theorem negativeBinomialCensored_den_trials (r cap a b : Nat) (hr : 0 < r) (ha : 0 < a) :
    (negativeBinomialCensoredDistro r cap a b hr ha).record.den = (a + b) ^ (cap + r) := by
  rw [negativeBinomialCensored_den, negativeBinomialCensored_exhaustion a b r cap hr]

theorem eventMass_censor_last (source : List (Nat × Nat)) (cap : Nat)
    (support : forall value weight, (value, weight) ∈ source → value ≤ cap + 1) :
    FiniteProbRecord.eventMass source (fun value => decide (min value cap = cap)) =
      FiniteProbRecord.eventMass source (FiniteProbRecord.singletonEvent cap) +
        FiniteProbRecord.eventMass source (FiniteProbRecord.singletonEvent (cap + 1)) := by
  have hevent : (fun value => decide (min value cap = cap)) =
      (fun value => !(decide (value < cap))) := by
    funext value
    by_cases selected : value < cap
    · simp only [Nat.min_eq_left (Nat.le_of_lt selected), Nat.ne_of_lt selected,
        selected, decide_false, decide_true, Bool.not_true]
    · simp only [Nat.min_eq_right (Nat.le_of_not_lt selected), eq_self,
        selected, decide_false, decide_true, Bool.not_false]
  rw [hevent]
  have first := FiniteProbRecord.eventMass_add_complement source (fun value => decide (value < cap))
  have second := eventMass_lt_add_last source (cap + 1) support
  rw [eventMass_lt_eq_natSum, natSum_succ, ← eventMass_lt_eq_natSum source cap] at second
  exact Nat.add_left_cancel (first.trans (second.symm.trans (Nat.add_assoc _ _ _)))

/-- The censored NB law is the actual Bernoulli product stopped at either
the requested successes or `cap + 1` failures, with the final count clipped. -/
def negativeBinomialCensoredFromBernoulli (r cap a b : Nat)
    (_hr : 0 < r) (ha : 0 < a) : Distro (Fin (cap + 1)) where
  record := (bernoulliRaceFromProduct a b r (cap + 1) (Nat.add_pos_right b ha)).map
    (censorFailureCount cap)

theorem negativeBinomialCensoredFromBernoulli_pmf (r cap a b : Nat)
    (hr : 0 < r) (ha : 0 < a) (k : Fin (cap + 1)) :
    QProb.Equiv ((negativeBinomialCensoredFromBernoulli r cap a b hr ha).pmf k)
      ((negativeBinomialCensoredDistro r cap a b hr ha).pmf k) := by
  let event : Event Nat :=
    fun value => FiniteProbRecord.singletonEvent k (censorFailureCount cap value)
  have hmap : QProb.Equiv ((negativeBinomialCensoredFromBernoulli r cap a b hr ha).pmf k)
      ((bernoulliRaceFromProduct a b r (cap + 1) (Nat.add_pos_right b ha)).probVal event) :=
    FiniteProbRecord.map_probVal _ (censorFailureCount cap) (FiniteProbRecord.singletonEvent k)
  have hmass : FiniteProbRecord.eventMass (bernoulliRaceAtoms a b r (cap + 1)) event =
      negativeBinomialCensoredWeight r cap a b k := by
    by_cases selected : k.val < cap
    · have hevent : event = FiniteProbRecord.singletonEvent k.val := by
        funext value
        simp only [event, FiniteProbRecord.singletonEvent, censorFailureCount, Fin.ext_iff]
        by_cases low : value ≤ cap
        · rw [Nat.min_eq_left low]
        · have high : cap ≤ value := Nat.le_of_not_le low
          have different : value ≠ k.val := by omega
          simp only [Nat.min_eq_right high, Nat.ne_of_gt selected, different, decide_false]
      rw [hevent, bernoulliRace_mass_occupancy a b r cap hr k]
      simp only [negativeBinomialCensoredWeight, selected, if_true]
    · have last : k.val = cap := by have := k.isLt; omega
      simp only [event, FiniteProbRecord.singletonEvent, censorFailureCount, Fin.ext_iff]
      rw [last, eventMass_censor_last _ cap (bernoulliRaceAtoms_support a b r (cap + 1)),
        bernoulliRace_mass_occupancy a b r cap hr ⟨cap, Nat.lt_succ_self cap⟩,
        bernoulliRace_mass_tail a b r cap hr]
      simp only [negativeBinomialCensoredWeight, last, Nat.lt_irrefl, if_false]
      congr 1
      exact congrArg (negativeBinomialWeight r cap a b) (Fin.ext last.symm)
  refine QProb.equiv_trans hmap
    (QProb.equiv_trans (bernoulliRaceFromProduct_event a b r (cap + 1) _ event)
      (QProb.equiv_trans ?_ (QProb.equiv_symm (negativeBinomialCensored_pmf r cap a b hr ha k))))
  change FiniteProbRecord.eventMass (bernoulliRaceAtoms a b r (cap + 1)) event *
      (negativeBinomialCensoredDistro r cap a b hr ha).record.den =
    negativeBinomialCensoredWeight r cap a b k * (a + b) ^ (r + (cap + 1) - 1)
  have horizon : r + (cap + 1) - 1 = cap + r := by omega
  rw [hmass, negativeBinomialCensored_den_trials, horizon]

theorem negativeBinomialCensoredFromBernoulli_event (r cap a b : Nat)
    (hr : 0 < r) (ha : 0 < a) (event : Event (Fin (cap + 1))) :
    QProb.Equiv ((negativeBinomialCensoredFromBernoulli r cap a b hr ha).record.probVal event)
      ((negativeBinomialCensoredDistro r cap a b hr ha).record.probVal event) := by
  exact FiniteProbRecord.probVal_extensional_of_singletons _ _ (List.finRange (cap + 1))
    (finRange_nodup _) (fun value => List.mem_finRange value)
    (negativeBinomialCensoredFromBernoulli_pmf r cap a b hr ha) event

theorem bernoulliRaceFromProduct_mass (a b r m : Nat) (positive : 0 < b + a)
    (event : Event Nat) :
    FiniteProbRecord.eventMass (bernoulliRaceFromProduct a b r m positive).atoms event =
      FiniteProbRecord.eventMass (bernoulliRaceAtoms a b r m) event := by
  change FiniteProbRecord.eventMass
    ((bernoulliProductAtoms (r + m - 1) a b positive).map fun atom =>
      (bernoulliRaceFailures (bernoulliTrialList (r + m - 1) atom.1) r m, atom.2)) event = _
  rw [FiniteProbRecord.eventMass_map_labels
    (bernoulliProductAtoms (r + m - 1) a b positive)
    (fun assignment => bernoulliRaceFailures (bernoulliTrialList (r + m - 1) assignment) r m) event]
  exact bernoulliRace_eventMass a b r m positive event

/-- The truncated NB law conditions the actual stopped Bernoulli product
on reaching its successes before failure exhaustion. -/
def negativeBinomialFromBernoulli (r cap a b : Nat) (hr : 0 < r) (ha : 0 < a) :
    Distro (Fin (cap + 1)) where
  record :=
    let source := bernoulliRaceFromProduct a b r (cap + 1) (Nat.add_pos_right b ha)
    have supported : source.EventPositive (fun value => decide (value < cap + 1)) := by
      change 0 < FiniteProbRecord.eventMass source.atoms (fun value => decide (value < cap + 1))
      rw [bernoulliRaceFromProduct_mass, bernoulliRace_success_mass a b r cap hr]
      exact Nat.mul_pos (Nat.pow_pos ha)
        (nbSumHomog_pos _ _ _ _ (Nat.add_pos_left ha _))
    (source.conditionOn (fun value => decide (value < cap + 1)) supported).map
      (censorFailureCount cap)

theorem negativeBinomialFromBernoulli_den (r cap a b : Nat) (hr : 0 < r) (ha : 0 < a) :
    (negativeBinomialFromBernoulli r cap a b hr ha).record.den =
      a ^ r * nbSumHomog r b (a + b) cap := by
  simp only [negativeBinomialFromBernoulli, FiniteProbRecord.map, FiniteProbRecord.conditionOn,
    bernoulliRaceFromProduct_mass, bernoulliRace_success_mass a b r cap hr]

theorem negativeBinomialFromBernoulli_mass (r cap a b : Nat) (hr : 0 < r) (ha : 0 < a)
    (k : Fin (cap + 1)) :
    FiniteProbRecord.eventMass (negativeBinomialFromBernoulli r cap a b hr ha).record.atoms
        (FiniteProbRecord.singletonEvent k) = negativeBinomialWeight r cap a b k := by
  have hevent : forall value : Nat,
      (decide (value < cap + 1) &&
          FiniteProbRecord.singletonEvent k (censorFailureCount cap value)) =
        FiniteProbRecord.singletonEvent k.val value := by
    intro value
    by_cases low : value ≤ cap
    · have selected : value < cap + 1 := Nat.lt_succ_of_le low
      simp only [FiniteProbRecord.singletonEvent, censorFailureCount, Fin.ext_iff,
        Nat.min_eq_left low, selected, decide_true, Bool.true_and]
    · have excluded : ¬ value < cap + 1 := by omega
      have different : value ≠ k.val := by have := k.isLt; omega
      simp only [FiniteProbRecord.singletonEvent, excluded, different, decide_false, Bool.false_and]
  simp only [negativeBinomialFromBernoulli, FiniteProbRecord.map, FiniteProbRecord.conditionOn,
    FiniteProbRecord.eventMass_map_labels]
  rw [FiniteProbRecord.eventMass_filter_event _
    (fun value : Nat => decide (value < cap + 1))
    (fun value => FiniteProbRecord.singletonEvent k (censorFailureCount cap value))]
  rw [FiniteProbRecord.eventMass_congr _ _ _ hevent,
    bernoulliRaceFromProduct_mass, bernoulliRace_mass_occupancy a b r cap hr k]

theorem negativeBinomialFromBernoulli_pmf (r cap a b : Nat) (hr : 0 < r) (ha : 0 < a)
    (k : Fin (cap + 1)) :
    QProb.Equiv ((negativeBinomialFromBernoulli r cap a b hr ha).pmf k)
      ((negativeBinomialDistro r cap a b hr ha).pmf k) := by
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (negativeBinomial_pmf r cap a b hr ha k))
  simp only [Distro.pmf, FiniteProbRecord.probVal, QProb.Equiv,
    negativeBinomialFromBernoulli_mass, negativeBinomialFromBernoulli_den, negativeBinomial_den]

theorem negativeBinomialFromBernoulli_event (r cap a b : Nat) (hr : 0 < r) (ha : 0 < a)
    (event : Event (Fin (cap + 1))) :
    QProb.Equiv ((negativeBinomialFromBernoulli r cap a b hr ha).record.probVal event)
      ((negativeBinomialDistro r cap a b hr ha).record.probVal event) := by
  exact FiniteProbRecord.probVal_extensional_of_singletons _ _ (List.finRange (cap + 1))
    (finRange_nodup _) (fun value => List.mem_finRange value)
    (negativeBinomialFromBernoulli_pmf r cap a b hr ha) event

end Distros
end Probability
end Thesis
