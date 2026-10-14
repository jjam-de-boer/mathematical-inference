import Thesis.Probability.Distros.FactorialMoments
import Thesis.Probability.Distros.BetaBinomial

namespace Thesis.Probability.Distros
open Combinatorics

/-!
Sequential sampling without replacement from a two-colour finite urn.
Each step is a Bernoulli colour draw from the current ball counts and
removes one ball of the selected colour.  Raw path mass has denominator
`(marked + unmarked)↓draws`, counting ordered ball choices.  The marked-count
pushforward agrees with hypergeometric on every event after cancelling the
common `draws!` factor.  Positive-mass counts respect both colour capacities.
The existing mean and finite-population variance transport to this process.
-/

def depletingTerm (n marked unmarked k : Nat) : Nat :=
  binom n k * fallingFactorial marked k * fallingFactorial unmarked (n - k)

theorem depletingTerm_outside (n marked unmarked k : Nat) (outside : n < k) :
    depletingTerm n marked unmarked k = 0 := by
  simp only [depletingTerm, binom_eq_zero_of_lt outside, Nat.zero_mul]

theorem depletingTerm_step_zero (n marked unmarked : Nat) :
    depletingTerm (n + 1) marked unmarked 0 =
      unmarked * depletingTerm n marked (unmarked - 1) 0 := by
  simp only [depletingTerm, binom_zero_right, fallingFactorial,
    Nat.sub_zero, Nat.one_mul, Nat.mul_one]

theorem depletingTerm_step (n marked unmarked k : Nat) (within : k ≤ n) :
    depletingTerm (n + 1) marked unmarked (k + 1) =
      marked * depletingTerm n (marked - 1) unmarked k +
        unmarked * depletingTerm n marked (unmarked - 1) (k + 1) := by
  rw [depletingTerm, binom_succ_succ, Nat.succ_sub_succ, fallingFactorial,
    Nat.add_mul, Nat.add_mul]
  by_cases inside : k < n
  · have index : n - k = (n - (k + 1)) + 1 := by omega
    have second : binom n (k + 1) * (marked * fallingFactorial (marked - 1) k) *
        fallingFactorial unmarked (n - k) =
      unmarked * depletingTerm n marked (unmarked - 1) (k + 1) := by
      rw [index, fallingFactorial]
      simp only [depletingTerm, fallingFactorial]
      ac_rfl
    rw [second]
    simp only [depletingTerm]
    ac_rfl
  · have eq : k = n := by omega
    rw [eq, binom_eq_zero_of_lt (Nat.lt_succ_self n)]
    simp only [Nat.zero_mul, depletingTerm, binom_eq_zero_of_lt (Nat.lt_succ_self n),
      Nat.mul_zero, Nat.add_zero]
    ac_rfl

/-- Actual colour paths: choose a ball with its current colour weight,
then remove one ball of that colour before the next draw. -/
def depletingPathAtoms : Nat → Nat → Nat → List (List Bool × Nat)
  | 0, _, _ => [([], 1)]
  | n + 1, marked, unmarked =>
      (depletingPathAtoms n (marked - 1) unmarked).map
        (fun atom => (true :: atom.1, marked * atom.2)) ++
      (depletingPathAtoms n marked (unmarked - 1)).map
        (fun atom => (false :: atom.1, unmarked * atom.2))

def depletingCountAtoms : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => [(0, 1)]
  | n + 1, marked, unmarked =>
      (depletingCountAtoms n (marked - 1) unmarked).map
        (fun atom => (atom.1 + 1, marked * atom.2)) ++
      (depletingCountAtoms n marked (unmarked - 1)).map
        (fun atom => (atom.1, unmarked * atom.2))

theorem depletingPath_count_atoms (n marked unmarked : Nat) :
    (depletingPathAtoms n marked unmarked).map (fun atom => (polyaSuccesses atom.1, atom.2)) =
      depletingCountAtoms n marked unmarked := by
  induction n generalizing marked unmarked with
  | zero => rfl
  | succ n ih =>
      simp only [depletingPathAtoms, depletingCountAtoms, List.map_append, List.map_map,
        Function.comp_def, polyaSuccesses]
      have ht := congrArg (fun atoms : List (Nat × Nat) =>
        atoms.map (fun atom => (atom.1 + 1, marked * atom.2))) (ih (marked - 1) unmarked)
      have hf := congrArg (fun atoms : List (Nat × Nat) =>
        atoms.map (fun atom => (atom.1, unmarked * atom.2))) (ih marked (unmarked - 1))
      simp only [List.map_map, Function.comp_def] at ht hf
      rw [ht, hf]

theorem depletingPath_totalMass (n marked unmarked : Nat) :
    FiniteProbRecord.totalMass (depletingPathAtoms n marked unmarked) =
      fallingFactorial (marked + unmarked) n := by
  induction n generalizing marked unmarked with
  | zero => rfl
  | succ n ih =>
      rw [depletingPathAtoms, FiniteProbRecord.totalMass_append,
        FiniteProbRecord.totalMass_map_weight _ (fun path => true :: path) marked,
        FiniteProbRecord.totalMass_map_weight _ (fun path => false :: path) unmarked, ih, ih]
      change marked * fallingFactorial (marked - 1 + unmarked) n +
        unmarked * fallingFactorial (marked + (unmarked - 1)) n =
          (marked + unmarked) * fallingFactorial (marked + unmarked - 1) n
      have first : marked * fallingFactorial (marked - 1 + unmarked) n =
          marked * fallingFactorial (marked + unmarked - 1) n := by
        by_cases zero : marked = 0
        · subst marked
          simp only [Nat.zero_mul]
        · have index : marked - 1 + unmarked = marked + unmarked - 1 := by omega
          rw [index]
      have second : unmarked * fallingFactorial (marked + (unmarked - 1)) n =
          unmarked * fallingFactorial (marked + unmarked - 1) n := by
        by_cases zero : unmarked = 0
        · subst unmarked
          simp only [Nat.zero_mul]
        · have index : marked + (unmarked - 1) = marked + unmarked - 1 := by omega
          rw [index]
      rw [first, second, ← Nat.add_mul]

theorem depletingCount_mass (n marked unmarked k : Nat) :
    FiniteProbRecord.eventMass (depletingCountAtoms n marked unmarked) (FiniteProbRecord.singletonEvent k) =
      depletingTerm n marked unmarked k := by
  induction n generalizing marked unmarked k with
  | zero =>
      cases k with
      | zero => rfl
      | succ k =>
          simp only [depletingCountAtoms, FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
            Nat.zero_ne_add_one k, decide_false, if_neg (by decide : false ≠ true), depletingTerm,
            binom_zero_succ, Nat.zero_mul]
  | succ n ih =>
      rw [depletingCountAtoms, FiniteProbRecord.eventMass_append,
        FiniteProbRecord.eventMass_map_weight _ (fun value : Nat => value) unmarked]
      cases k with
      | zero => rw [eventMass_map_successor_zero, Nat.zero_add, ih, depletingTerm_step_zero]
      | succ k =>
          rw [eventMass_map_successor, ih, ih]
          by_cases within : k ≤ n
          · exact (depletingTerm_step n marked unmarked k within).symm
          · have outside : n < k := by omega
            rw [depletingTerm_outside n (marked - 1) unmarked k outside,
              depletingTerm_outside n marked (unmarked - 1) (k + 1) (by omega),
              depletingTerm_outside (n + 1) marked unmarked (k + 1) (by omega)]
            simp only [Nat.mul_zero, Nat.add_zero]

theorem depletingCount_support (n marked unmarked : Nat) (atom : Nat × Nat)
    (member : atom ∈ depletingCountAtoms n marked unmarked) : atom.1 ≤ n := by
  induction n generalizing marked unmarked atom with
  | zero => simp only [depletingCountAtoms, List.mem_singleton] at member; cases member; exact Nat.le_refl _
  | succ n ih =>
      simp only [depletingCountAtoms, List.mem_append, List.mem_map] at member
      rcases member with ⟨source, hs, he⟩ | ⟨source, hs, he⟩
      · cases he
        exact Nat.succ_le_succ (ih (marked - 1) unmarked source hs)
      · cases he
        exact Nat.le_succ_of_le (ih marked (unmarked - 1) source hs)

/-- A finite sequential without-replacement path record. -/
def depletingPathRecord (n marked unmarked : Nat) (within : n ≤ marked + unmarked) : FiniteProbRecord (List Bool) :=
  ⟨depletingPathAtoms n marked unmarked, fallingFactorial (marked + unmarked) n,
    fallingFactorial_pos _ _ within, depletingPath_totalMass n marked unmarked⟩

def depletingCountRecord (n marked unmarked : Nat) (within : n ≤ marked + unmarked) : FiniteProbRecord Nat :=
  (depletingPathRecord n marked unmarked within).map polyaSuccesses

def depletingUrnDistro (n marked unmarked : Nat) (within : n ≤ marked + unmarked) : Distro (Fin (n + 1)) :=
  ⟨(depletingCountRecord n marked unmarked within).map (polyaCountFin n)⟩

theorem depletingUrn_mass (n marked unmarked : Nat) (within : n ≤ marked + unmarked) (k : Fin (n + 1)) :
    FiniteProbRecord.eventMass (depletingUrnDistro n marked unmarked within).record.atoms
      (FiniteProbRecord.singletonEvent k) = depletingTerm n marked unmarked k.val := by
  change FiniteProbRecord.eventMass
    ((depletingCountRecord n marked unmarked within).atoms.map
      (fun atom => (polyaCountFin n atom.1, atom.2))) _ = _
  rw [FiniteProbRecord.eventMass_map_labels]
  have atoms : (depletingCountRecord n marked unmarked within).atoms = depletingCountAtoms n marked unmarked :=
    depletingPath_count_atoms n marked unmarked
  rw [atoms]
  have h := eventMass_congr_on_support (depletingCountAtoms n marked unmarked)
    (fun value => FiniteProbRecord.singletonEvent k (polyaCountFin n value))
    (FiniteProbRecord.singletonEvent k.val) (fun atom member => ?_)
  · rw [h, depletingCount_mass]
  · have bound := depletingCount_support n marked unmarked atom member
    simp only [FiniteProbRecord.singletonEvent, polyaCountFin]
    have hi : (⟨min atom.1 n, Nat.lt_succ_of_le (Nat.min_le_right atom.1 n)⟩ : Fin (n + 1)) = k ↔
        atom.1 = k.val := by
      constructor
      · intro eq
        have value := congrArg Fin.val eq
        simpa only [Nat.min_eq_left bound] using value
      · intro eq
        apply Fin.ext
        exact (Nat.min_eq_left bound).trans eq
    simp only [hi]

theorem depletingTerm_hypergeometric (n marked unmarked k : Nat) (within : k ≤ n) :
    depletingTerm n marked unmarked k =
      fallingFactorial n n * binom marked k * binom unmarked (n - k) := by
  rw [depletingTerm, fallingFactorial_binom marked k, fallingFactorial_binom unmarked (n - k)]
  calc
    _ = (binom n k * fallingFactorial k k * fallingFactorial (n - k) (n - k)) *
        binom marked k * binom unmarked (n - k) := by ac_rfl
    _ = _ := by rw [binom_factorial_split n k within]

/-- Draw without replacement from the actual sequential two-colour urn,
then expose the number of marked balls as a finite outcome. -/
def hypergeometricFromUrn (marked total draws : Nat) (hmarked : marked ≤ total)
    (positive : 0 < binom total draws) : Distro (Fin (draws + 1)) :=
  depletingUrnDistro draws marked (total - marked) (by
    rw [Nat.add_sub_of_le hmarked]
    exact hypergeometric_draws_le_total total draws positive)

/-- Every event of the hypergeometric constructor is the marked-count
pushforward of finite sequential sampling without replacement. -/
theorem hypergeometric_urn_correspondence (marked total draws : Nat) (hmarked : marked ≤ total)
    (positive : 0 < binom total draws) :
    (hypergeometricFromUrn marked total draws hmarked positive).SameLaw
      (hypergeometricDistro marked total draws hmarked positive) := by
  apply Distro.sameLaw_of_singletons _ _ (List.finRange (draws + 1))
    (finRange_nodup _) (fun value => List.mem_finRange value)
  intro k
  change FiniteProbRecord.eventMass (depletingUrnDistro draws marked (total - marked) _).record.atoms
      (FiniteProbRecord.singletonEvent k) * (hypergeometricDistro marked total draws hmarked positive).record.den =
    FiniteProbRecord.eventMass (finWeighted (draws + 1) (hypergeometricWeight marked total draws))
      (FiniteProbRecord.singletonEvent k) * fallingFactorial (marked + (total - marked)) draws
  rw [depletingUrn_mass, hypergeometric_den, eventMass_finWeighted_singleton,
    depletingTerm_hypergeometric draws marked (total - marked) k.val (Nat.le_of_lt_succ k.isLt),
    Nat.add_sub_of_le hmarked, fallingFactorial_binom total draws]
  simp only [hypergeometricWeight]
  ac_rfl

/-- Each draw is the actual Bernoulli colour draw from the remaining urn,
followed by the continuation with one ball of the drawn colour removed. -/
theorem depletingPath_first_step (n marked unmarked : Nat) (within : n + 1 ≤ marked + unmarked)
    (event : Event (List Bool)) :
    QProb.Equiv ((depletingPathRecord (n + 1) marked unmarked within).probVal event)
      (QProb.add
        (QProb.mul ((bernoulliDistro marked unmarked (by omega)).pmf true)
          ((depletingPathRecord n (marked - 1) unmarked (by omega)).probVal
            (fun path => event (true :: path))))
        (QProb.mul ((bernoulliDistro marked unmarked (by omega)).pmf false)
          ((depletingPathRecord n marked (unmarked - 1) (by omega)).probVal
            (fun path => event (false :: path))))) := by
  let s := marked + unmarked
  let d := fallingFactorial (s - 1) n
  let dt := fallingFactorial (marked - 1 + unmarked) n
  let df := fallingFactorial (marked + (unmarked - 1)) n
  let a := FiniteProbRecord.eventMass (depletingPathAtoms n (marked - 1) unmarked)
    (fun path => event (true :: path))
  let b := FiniteProbRecord.eventMass (depletingPathAtoms n marked (unmarked - 1))
    (fun path => event (false :: path))
  have ht : marked * dt = marked * d := by
    by_cases zero : marked = 0
    · rw [zero, Nat.zero_mul, Nat.zero_mul]
    · have index : marked - 1 + unmarked = s - 1 := by dsimp only [s]; omega
      dsimp only [dt, d]
      rw [index]
  have hf : unmarked * df = unmarked * d := by
    by_cases zero : unmarked = 0
    · rw [zero, Nat.zero_mul, Nat.zero_mul]
    · have index : marked + (unmarked - 1) = s - 1 := by dsimp only [s]; omega
      dsimp only [df, d]
      rw [index]
  have htrue : ((bernoulliDistro marked unmarked (by omega)).pmf true).num = marked := by
    simp [Distro.pmf, bernoulliDistro, FiniteProbRecord.probVal,
      FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
  have hfalse : ((bernoulliDistro marked unmarked (by omega)).pmf false).num = unmarked := by
    simp [Distro.pmf, bernoulliDistro, FiniteProbRecord.probVal,
      FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
  simp only [QProb.Equiv, QProb.add, QProb.mul]
  rw [htrue, hfalse]
  simp only [Distro.pmf, bernoulliDistro, FiniteProbRecord.probVal, depletingPathRecord]
  rw [depletingPathAtoms, FiniteProbRecord.eventMass_append,
    FiniteProbRecord.eventMass_map_weight _ (fun path => true :: path) marked,
    FiniteProbRecord.eventMass_map_weight _ (fun path => false :: path) unmarked]
  have comm : unmarked + marked = s := Nat.add_comm _ _
  rw [comm]
  change (marked * a + unmarked * b) * (s * dt * (s * df)) =
    (marked * a * (s * df) + unmarked * b * (s * dt)) * (s * d)
  rw [Nat.add_mul (marked * a) (unmarked * b) (s * dt * (s * df)),
    Nat.add_mul (marked * a * (s * df)) (unmarked * b * (s * dt)) (s * d)]
  congr 1
  · calc
      _ = a * (s * s * df) * (marked * dt) := by ac_rfl
      _ = a * (s * s * df) * (marked * d) := by rw [ht]
      _ = _ := by ac_rfl
  · calc
      _ = b * (s * s * dt) * (unmarked * df) := by ac_rfl
      _ = b * (s * s * dt) * (unmarked * d) := by rw [hf]
      _ = _ := by ac_rfl

theorem depletingUrn_colour_bounds (n marked unmarked : Nat) (within : n ≤ marked + unmarked)
    (k : Fin (n + 1)) (positive : 0 < ((depletingUrnDistro n marked unmarked within).pmf k).num) :
    k.val ≤ marked ∧ n - k.val ≤ unmarked := by
  change 0 < FiniteProbRecord.eventMass (depletingUrnDistro n marked unmarked within).record.atoms
    (FiniteProbRecord.singletonEvent k) at positive
  rw [depletingUrn_mass, depletingTerm_hypergeometric n marked unmarked k.val
    (Nat.le_of_lt_succ k.isLt)] at positive
  constructor
  · by_cases bound : k.val ≤ marked
    · exact bound
    · rw [binom_eq_zero_of_lt (by omega : marked < k.val), Nat.mul_zero, Nat.zero_mul] at positive
      omega
  · by_cases bound : n - k.val ≤ unmarked
    · exact bound
    · rw [binom_eq_zero_of_lt (by omega : unmarked < n - k.val), Nat.mul_zero] at positive
      omega

theorem hypergeometricFromUrn_mean (marked total draws : Nat) (hmarked : marked ≤ total)
    (positive : 0 < binom total draws) (nonempty : 0 < total) :
    QProb.Equiv (mean (⟨hypergeometricFromUrn marked total draws hmarked positive, Fin.val⟩ : NatDistro _))
      ⟨draws * marked, total, nonempty⟩ :=
  QProb.equiv_trans
    (NatDistro.sameLaw_of_distro (hypergeometric_urn_correspondence marked total draws hmarked positive) Fin.val).mean
    (hypergeometric_mean marked total draws hmarked positive nonempty)

theorem hypergeometricFromUrn_variance (marked total draws : Nat) (hmarked : marked ≤ total)
    (positive : 0 < binom total draws) (nontrivial : 1 < total) :
    QProb.Equiv (variance (⟨hypergeometricFromUrn marked total draws hmarked positive, Fin.val⟩ : NatDistro _))
      ⟨draws * marked * (total - marked) * (total - draws), total * total * (total - 1),
        Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)⟩ :=
  QProb.equiv_trans
    (NatDistro.sameLaw_of_distro (hypergeometric_urn_correspondence marked total draws hmarked positive) Fin.val).variance
    (hypergeometric_variance marked total draws hmarked positive nontrivial)

end Thesis.Probability.Distros
