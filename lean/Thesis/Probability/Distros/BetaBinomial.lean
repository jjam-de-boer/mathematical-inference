import Thesis.Probability.Distros.LimitAnalogs
import Thesis.Probability.Distros.Moments
import Thesis.Probability.Distros.BernoulliRace

namespace Thesis.Probability

namespace Combinatorics

theorem risingFactorial_head (a n : Nat) :
    risingFactorial a (n + 1) = a * risingFactorial (a + 1) n := by
  induction n with
  | zero => simp only [risingFactorial, Nat.add_zero, Nat.mul_one]
  | succ n ih =>
      rw [risingFactorial_succ, ih, risingFactorial_succ]
      have h : a + (n + 1) = a + 1 + n := by omega
      rw [h]
      ac_rfl

def betaBinomialTerm (n a b k : Nat) : Nat :=
  binom n k * risingFactorial a k * risingFactorial b (n - k)

theorem betaBinomialTerm_outside (n a b k : Nat) (h : n < k) :
    betaBinomialTerm n a b k = 0 := by
  simp only [betaBinomialTerm, binom_eq_zero_of_lt h, Nat.zero_mul]

theorem betaBinomialTerm_step_zero (n a b : Nat) :
    betaBinomialTerm (n + 1) a b 0 = b * betaBinomialTerm n a (b + 1) 0 := by
  simp only [betaBinomialTerm, binom_zero_right, risingFactorial_zero,
    Nat.sub_zero, Nat.mul_one, Nat.one_mul, risingFactorial_head]

theorem betaBinomialTerm_step (n a b k : Nat) (h : k ≤ n) :
    betaBinomialTerm (n + 1) a b (k + 1) =
      a * betaBinomialTerm n (a + 1) b k + b * betaBinomialTerm n a (b + 1) (k + 1) := by
  rw [betaBinomialTerm, binom_succ_succ, Nat.succ_sub_succ, risingFactorial_head,
    Nat.add_mul, Nat.add_mul]
  by_cases hk : k < n
  · have hs : n - k = (n - (k + 1)) + 1 := by omega
    have hsecond :
        binom n (k + 1) * (a * risingFactorial (a + 1) k) * risingFactorial b (n - k) =
          b * betaBinomialTerm n a (b + 1) (k + 1) := by
      rw [hs, risingFactorial_head]
      simp only [betaBinomialTerm, risingFactorial_head]
      ac_rfl
    rw [hsecond]
    simp only [betaBinomialTerm]
    ac_rfl
  · have he : k = n := by omega
    rw [he, binom_eq_zero_of_lt (Nat.lt_succ_self n)]
    simp only [Nat.zero_mul, betaBinomialTerm, binom_eq_zero_of_lt (Nat.lt_succ_self n),
      Nat.mul_zero, Nat.add_zero]
    ac_rfl

/-- Rising-factorial Vandermonde, including zero parameters. -/
theorem risingFactorial_vandermonde (n a b : Nat) :
    natSum (n + 1) (betaBinomialTerm n a b) = risingFactorial (a + b) n := by
  induction n generalizing a b with
  | zero => simp only [natSum, betaBinomialTerm, binom_zero_right,
      risingFactorial_zero, Nat.sub_self, Nat.mul_one]
  | succ n ih =>
      rw [natSum_head, betaBinomialTerm_step_zero]
      have htail : natSum (n + 1) (fun k => betaBinomialTerm (n + 1) a b (k + 1)) =
          a * natSum (n + 1) (betaBinomialTerm n (a + 1) b) +
            b * natSum (n + 1) (fun k => betaBinomialTerm n a (b + 1) (k + 1)) := by
        rw [← natSum_mul_left, ← natSum_mul_left, ← natSum_add]
        apply natSum_congr
        intro k hk
        exact betaBinomialTerm_step n a b k (Nat.le_of_lt_succ hk)
      rw [htail]
      have hfalse : betaBinomialTerm n a (b + 1) 0 +
          natSum (n + 1) (fun k => betaBinomialTerm n a (b + 1) (k + 1)) =
            natSum (n + 1) (betaBinomialTerm n a (b + 1)) := by
        rw [← natSum_head, natSum_succ, betaBinomialTerm_outside n a (b + 1) (n + 1)
          (Nat.lt_succ_self n), Nat.add_zero]
      calc
        _ = a * natSum (n + 1) (betaBinomialTerm n (a + 1) b) +
            b * (betaBinomialTerm n a (b + 1) 0 +
              natSum (n + 1) (fun k => betaBinomialTerm n a (b + 1) (k + 1))) := by
          rw [Nat.mul_add]; ac_rfl
        _ = a * risingFactorial (a + 1 + b) n + b * risingFactorial (a + (b + 1)) n := by
          rw [hfalse, ih, ih]
        _ = (a + b) * risingFactorial (a + b + 1) n := by
          have h : a + 1 + b = a + b + 1 := by omega
          rw [h, Nat.add_assoc, Nat.add_mul]
        _ = risingFactorial (a + b) (n + 1) := (risingFactorial_head _ _).symm

end Combinatorics

namespace Distros

open Combinatorics

/-- The beta-binomial constructor's denominator is the rising trial total. -/
theorem betaBinomial_den (trials a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    (betaBinomialDistro trials a b ha hb).record.den = risingFactorial (a + b) trials := by
  change FiniteProbRecord.totalMass (finWeighted (trials + 1) (betaBinomialWeight trials a b)) = _
  rw [totalMass_finWeighted]
  have h : natSum (trials + 1) (finWeight (betaBinomialWeight trials a b)) =
      natSum (trials + 1) (betaBinomialTerm trials a b) := by
    apply natSum_congr
    intro k hk
    simp only [finWeight, dif_pos hk, betaBinomialWeight, betaBinomialTerm]
  rw [h, risingFactorial_vandermonde]

/-- Actual colour paths of a finite urn: draw a ball, return it and add one
of the same colour before continuing.  Every branch uses its updated urn. -/
def polyaPathAtoms : Nat → Nat → Nat → List (List Bool × Nat)
  | 0, _, _ => [([], 1)]
  | n + 1, a, b =>
      (polyaPathAtoms n (a + 1) b).map (fun atom => (true :: atom.1, a * atom.2)) ++
        (polyaPathAtoms n a (b + 1)).map (fun atom => (false :: atom.1, b * atom.2))

def polyaSuccesses : List Bool → Nat
  | [] => 0
  | true :: rest => polyaSuccesses rest + 1
  | false :: rest => polyaSuccesses rest

def polyaCountAtoms : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => [(0, 1)]
  | n + 1, a, b =>
      (polyaCountAtoms n (a + 1) b).map (fun atom => (atom.1 + 1, a * atom.2)) ++
        (polyaCountAtoms n a (b + 1)).map (fun atom => (atom.1, b * atom.2))

theorem polyaPath_count_atoms (n a b : Nat) :
    (polyaPathAtoms n a b).map (fun atom => (polyaSuccesses atom.1, atom.2)) =
      polyaCountAtoms n a b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
      simp only [polyaPathAtoms, polyaCountAtoms, List.map_append, List.map_map,
        Function.comp_def, polyaSuccesses]
      have ht := congrArg (fun atoms : List (Nat × Nat) =>
        atoms.map (fun atom => (atom.1 + 1, a * atom.2))) (ih (a + 1) b)
      have hf := congrArg (fun atoms : List (Nat × Nat) =>
        atoms.map (fun atom => (atom.1, b * atom.2))) (ih a (b + 1))
      simp only [List.map_map, Function.comp_def] at ht hf
      rw [ht, hf]

theorem polyaPath_totalMass (n a b : Nat) :
    FiniteProbRecord.totalMass (polyaPathAtoms n a b) = risingFactorial (a + b) n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
      rw [polyaPathAtoms, FiniteProbRecord.totalMass_append,
        FiniteProbRecord.totalMass_map_weight _ (fun path => true :: path) a,
        FiniteProbRecord.totalMass_map_weight _ (fun path => false :: path) b, ih, ih]
      have hs : a + 1 + b = a + b + 1 := by omega
      have hs' : a + (b + 1) = a + b + 1 := by omega
      rw [hs, hs', ← Nat.add_mul]
      exact (risingFactorial_head _ _).symm

theorem polyaCount_totalMass (n a b : Nat) :
    FiniteProbRecord.totalMass (polyaCountAtoms n a b) = risingFactorial (a + b) n := by
  rw [← polyaPath_count_atoms, FiniteProbRecord.totalMass_map_labels, polyaPath_totalMass]

theorem polyaCount_mass (n a b k : Nat) :
    FiniteProbRecord.eventMass (polyaCountAtoms n a b) (FiniteProbRecord.singletonEvent k) =
      betaBinomialTerm n a b k := by
  induction n generalizing a b k with
  | zero =>
      cases k with
      | zero => rfl
      | succ k =>
          simp only [polyaCountAtoms, FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
            Nat.zero_ne_add_one k, decide_false, if_neg (by decide : false ≠ true), betaBinomialTerm,
            binom_zero_succ, Nat.zero_mul]
  | succ n ih =>
      rw [polyaCountAtoms, FiniteProbRecord.eventMass_append,
        FiniteProbRecord.eventMass_map_weight _ (fun value : Nat => value) b]
      cases k with
      | zero =>
          rw [eventMass_map_successor_zero, Nat.zero_add, ih, betaBinomialTerm_step_zero]
      | succ k =>
          rw [eventMass_map_successor, ih, ih]
          by_cases hk : k ≤ n
          · exact (betaBinomialTerm_step n a b k hk).symm
          · have h : n < k := by omega
            rw [betaBinomialTerm_outside n (a + 1) b k h,
              betaBinomialTerm_outside n a (b + 1) (k + 1) (by omega),
              betaBinomialTerm_outside (n + 1) a b (k + 1) (by omega)]
            simp only [Nat.mul_zero, Nat.add_zero]

theorem polyaCount_support (n a b : Nat) (atom : Nat × Nat)
    (member : atom ∈ polyaCountAtoms n a b) : atom.1 ≤ n := by
  induction n generalizing a b atom with
  | zero => simp only [polyaCountAtoms, List.mem_singleton] at member; cases member; exact Nat.le_refl _
  | succ n ih =>
      simp only [polyaCountAtoms, List.mem_append, List.mem_map] at member
      rcases member with ⟨source, hs, he⟩ | ⟨source, hs, he⟩
      · cases he
        exact Nat.succ_le_succ (ih (a + 1) b source hs)
      · cases he
        exact Nat.le_succ_of_le (ih a (b + 1) source hs)

/-- The finite sequential Pólya colour-path record. -/
def polyaPathRecord (n a b : Nat) (positive : 0 < a + b) : FiniteProbRecord (List Bool) :=
  ⟨polyaPathAtoms n a b, risingFactorial (a + b) n,
    risingFactorial_pos (a + b) n positive, polyaPath_totalMass n a b⟩

/-- One step is the actual Bernoulli colour draw from the current urn,
followed by the appropriate reinforced continuation. -/
theorem polyaPath_first_step (n a b : Nat) (positive : 0 < a + b)
    (event : Event (List Bool)) :
    QProb.Equiv ((polyaPathRecord (n + 1) a b positive).probVal event)
      (QProb.add
        (QProb.mul ((bernoulliDistro a b (by omega)).pmf true)
          ((polyaPathRecord n (a + 1) b (by omega)).probVal (fun path => event (true :: path))))
        (QProb.mul ((bernoulliDistro a b (by omega)).pmf false)
          ((polyaPathRecord n a (b + 1) (by omega)).probVal (fun path => event (false :: path))))) := by
  have htrue : ((bernoulliDistro a b (by omega)).pmf true).num = a := by
    simp [Distro.pmf, bernoulliDistro, FiniteProbRecord.probVal,
      FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
  have hfalse : ((bernoulliDistro a b (by omega)).pmf false).num = b := by
    simp [Distro.pmf, bernoulliDistro, FiniteProbRecord.probVal,
      FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent]
  have htotal : a + 1 + b = a + b + 1 := by omega
  have htotal' : a + (b + 1) = a + b + 1 := by omega
  simp only [QProb.Equiv, QProb.add, QProb.mul]
  rw [htrue, hfalse]
  simp only [Distro.pmf, bernoulliDistro, FiniteProbRecord.probVal, polyaPathRecord]
  rw [polyaPathAtoms, FiniteProbRecord.eventMass_append,
    FiniteProbRecord.eventMass_map_weight _ (fun path => true :: path) a,
    FiniteProbRecord.eventMass_map_weight _ (fun path => false :: path) b,
    htotal, htotal', risingFactorial_head]
  simp only [Nat.add_mul, Nat.mul_add]
  ac_rfl

def polyaCountRecord (n a b : Nat) (positive : 0 < a + b) : FiniteProbRecord Nat :=
  (polyaPathRecord n a b positive).map polyaSuccesses

theorem polyaCountRecord_atoms (n a b : Nat) (positive : 0 < a + b) :
    (polyaCountRecord n a b positive).atoms = polyaCountAtoms n a b := polyaPath_count_atoms n a b

def polyaCountFin (n k : Nat) : Fin (n + 1) := ⟨min k n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- The success-count pushforward of the actual reinforced urn paths. -/
def polyaUrnDistro (n a b : Nat) (positive : 0 < a + b) : Distro (Fin (n + 1)) :=
  ⟨(polyaCountRecord n a b positive).map (polyaCountFin n)⟩

theorem eventMass_congr_on_support (atoms : List (Ω × Nat)) (f g : Event Ω)
    (same : forall atom, atom ∈ atoms → f atom.1 = g atom.1) :
    FiniteProbRecord.eventMass atoms f = FiniteProbRecord.eventMass atoms g := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      have h := same atom (List.mem_cons_self)
      have ht := ih (fun value member => same value (List.mem_cons_of_mem _ member))
      simp only [FiniteProbRecord.eventMass, h, ht]

theorem polyaUrn_mass (n a b : Nat) (positive : 0 < a + b) (k : Fin (n + 1)) :
    FiniteProbRecord.eventMass (polyaUrnDistro n a b positive).record.atoms
      (FiniteProbRecord.singletonEvent k) = betaBinomialWeight n a b k := by
  change FiniteProbRecord.eventMass
    ((polyaCountRecord n a b positive).atoms.map
      (fun atom => (polyaCountFin n atom.1, atom.2))) _ = _
  rw [FiniteProbRecord.eventMass_map_labels, polyaCountRecord_atoms]
  have h := eventMass_congr_on_support (polyaCountAtoms n a b)
    (fun value => FiniteProbRecord.singletonEvent k (polyaCountFin n value))
    (FiniteProbRecord.singletonEvent k.val) (fun atom member => ?_)
  · rw [h, polyaCount_mass]
    rfl
  · have hs := polyaCount_support n a b atom member
    simp only [FiniteProbRecord.singletonEvent, polyaCountFin]
    have hi : (⟨min atom.1 n, Nat.lt_succ_of_le (Nat.min_le_right atom.1 n)⟩ : Fin (n + 1)) = k ↔
        atom.1 = k.val := by
      constructor
      · intro he
        have he' := congrArg Fin.val he
        simpa only [Nat.min_eq_left hs] using he'
      · intro he
        apply Fin.ext
        exact (Nat.min_eq_left hs).trans he
    simp only [hi]

/-- Every event of the beta-binomial law agrees with the reinforced urn. -/
theorem polyaUrn_correspondence (n a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (event : Event (Fin (n + 1))) :
    QProb.Equiv ((polyaUrnDistro n a b (Nat.add_pos_left ha b)).record.probVal event)
      ((betaBinomialDistro n a b ha hb).record.probVal event) := by
  apply FiniteProbRecord.probVal_extensional_of_singletons _ _ (List.finRange (n + 1))
    (finRange_nodup _) (fun value => List.mem_finRange value) _ event
  intro k
  have hm := polyaUrn_mass n a b (Nat.add_pos_left ha b) k
  have hd := betaBinomial_den n a b ha hb
  refine QProb.equiv_trans ?_ (QProb.equiv_symm (betaBinomial_pmf n a b ha hb k))
  change FiniteProbRecord.eventMass _ _ * (betaBinomialDistro n a b ha hb).record.den =
    betaBinomialWeight n a b k * risingFactorial (a + b) n
  rw [hm, hd]

theorem betaBinomial_pmf_rising (n a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (k : Fin (n + 1)) :
    QProb.Equiv ((betaBinomialDistro n a b ha hb).pmf k)
      ⟨betaBinomialWeight n a b k, risingFactorial (a + b) n,
        risingFactorial_pos (a + b) n (Nat.add_pos_left ha b)⟩ := by
  have h := betaBinomial_pmf n a b ha hb k
  simpa only [betaBinomial_den] using h

theorem betaBinomialTerm_succ_mul (n a b k : Nat) :
    (k + 1) * betaBinomialTerm (n + 1) a b (k + 1) =
      (n + 1) * a * betaBinomialTerm n (a + 1) b k := by
  simp only [betaBinomialTerm, Nat.succ_sub_succ, risingFactorial_head]
  calc
    _ = ((k + 1) * binom (n + 1) (k + 1)) *
        (a * risingFactorial (a + 1) k) * risingFactorial b (n - k) := by ac_rfl
    _ = _ := by rw [binom_succ_mul]; ac_rfl

theorem betaBinomialTerm_first_moment (n a b : Nat) :
    natSum (n + 1) (fun k => k * betaBinomialTerm n a b k) =
      n * a * risingFactorial (a + b + 1) (n - 1) := by
  cases n with
  | zero => simp only [natSum, Nat.zero_mul, Nat.add_zero]
  | succ n =>
      rw [natSum_head]
      have htail : natSum (n + 1) (fun k => (k + 1) * betaBinomialTerm (n + 1) a b (k + 1)) =
          (n + 1) * a * risingFactorial (a + 1 + b) n := by
        have h := natSum_congr (n := n + 1)
          (f := fun k => (k + 1) * betaBinomialTerm (n + 1) a b (k + 1))
          (g := fun k => (n + 1) * a * betaBinomialTerm n (a + 1) b k)
          (fun k _ => betaBinomialTerm_succ_mul n a b k)
        rw [h, natSum_mul_left, risingFactorial_vandermonde]
      rw [htail]
      have hs : a + 1 + b = a + b + 1 := by omega
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_sub_cancel, hs]

theorem betaBinomial_mean (n a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    QProb.Equiv (mean (betaBinomialNatDistro n a b ha hb))
      ⟨n * a, a + b, Nat.add_pos_left ha b⟩ := by
  have hn : (mean (betaBinomialNatDistro n a b ha hb)).num =
      natSum (n + 1) (fun k => k * betaBinomialTerm n a b k) := by
    rw [mean_expectNat]
    change natIntegral (finWeighted (n + 1) (betaBinomialWeight n a b)) Fin.val = _
    have hf := natIntegral_finWeighted (n + 1) (betaBinomialWeight n a b) id
    simp only [id] at hf
    rw [hf]
    apply natSum_congr
    intro k hk
    simp only [finWeight, dif_pos hk, betaBinomialWeight, betaBinomialTerm]
    ac_rfl
  change (mean (betaBinomialNatDistro n a b ha hb)).num * (a + b) =
    n * a * (betaBinomialDistro n a b ha hb).record.den
  rw [hn, betaBinomialTerm_first_moment, betaBinomial_den]
  cases n with
  | zero => simp only [Nat.zero_mul]
  | succ n =>
      rw [Nat.add_sub_cancel, risingFactorial_head]
      ac_rfl

end Distros
end Thesis.Probability
