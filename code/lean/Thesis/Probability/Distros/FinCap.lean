import Thesis.Probability.Distros.LawEquivalence

namespace Thesis.Probability.Distros
open Combinatorics

/-!
Finite-window conditioning and right censoring.  Common scaling of prefix
weights suffices for conditional-law equality; for censored laws, agreement
below the final cell and normalization determine the retained tail.
-/

theorem natSum_restrict_le (small large : Nat) (f : Nat → Nat) (bound : small ≤ large) :
    natSum (large + 1) (fun i => if i ≤ small then f i else 0) = natSum (small + 1) f := by
  induction large generalizing small with
  | zero =>
      have eq : small = 0 := by omega
      subst small
      simp only [natSum, Nat.le_refl, if_true, Nat.zero_add]
  | succ large ih =>
      by_cases within : small ≤ large
      · rw [natSum_succ, ih small within, if_neg (by omega : ¬large + 1 ≤ small), Nat.add_zero]
      · have eq : small = large + 1 := by omega
        subst small
        apply natSum_congr
        intro i hi
        rw [if_pos (by omega : i ≤ large + 1)]

def liftFinCap {small large : Nat} (bound : small ≤ large) (k : Fin (small + 1)) : Fin (large + 1) :=
  ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_succ bound)⟩

theorem finWeighted_prefix_mass (small large : Nat) (bound : small ≤ large)
    (w : Fin (large + 1) → Nat) :
    FiniteProbRecord.eventMass (finWeighted (large + 1) w) (fun x => decide (x.val ≤ small)) =
      natSum (small + 1) (finWeight w) := by
  rw [eventMass_finWeighted]
  have terms : natSum (large + 1) (fun i =>
        if h : i < large + 1 then if decide (i ≤ small) then w ⟨i, h⟩ else 0 else 0) =
      natSum (large + 1) (fun i => if i ≤ small then finWeight w i else 0) := by
    apply natSum_congr
    intro i hi
    simp only [finWeight, dif_pos hi, decide_eq_true_eq]
  rw [terms, natSum_restrict_le small large (finWeight w) bound]

theorem finWeighted_prefix_scaled (small large : Nat) (bound : small ≤ large)
    (largeWeights : Fin (large + 1) → Nat) (smallWeights : Fin (small + 1) → Nat)
    (factor : Nat) (weights : ∀ k, largeWeights (liftFinCap bound k) = factor * smallWeights k) :
    FiniteProbRecord.eventMass (finWeighted (large + 1) largeWeights) (fun x => decide (x.val ≤ small)) =
      factor * natSum (small + 1) (finWeight smallWeights) := by
  rw [finWeighted_prefix_mass small large bound, ← natSum_mul_left]
  apply natSum_congr
  intro i hi
  have largeBound : i < large + 1 := by omega
  simp only [finWeight, dif_pos hi, dif_pos largeBound]
  exact weights ⟨i, hi⟩

def conditionFinCap {large : Nat} (μ : Distro (Fin (large + 1))) (small : Nat)
    (positive : μ.record.EventPositive (fun x => decide (x.val ≤ small))) : Distro (Fin (small + 1)) :=
  (μ.conditionOn (fun x => decide (x.val ≤ small)) positive).map
    (fun x => censorFailureCount small x.val)

theorem ofFinWeights_prefix_positive (small large : Nat) (bound : small ≤ large)
    (largeWeights : Fin (large + 1) → Nat) (smallWeights : Fin (small + 1) → Nat)
    (hlarge : 0 < natSum (large + 1) (finWeight largeWeights))
    (hsmall : 0 < natSum (small + 1) (finWeight smallWeights))
    (factor : Nat) (hfactor : 0 < factor)
    (weights : ∀ k, largeWeights (liftFinCap bound k) = factor * smallWeights k) :
    (ofFinWeights (large + 1) largeWeights hlarge).EventPositive (fun x => decide (x.val ≤ small)) := by
  change 0 < FiniteProbRecord.eventMass (finWeighted (large + 1) largeWeights) _
  rw [finWeighted_prefix_scaled small large bound largeWeights smallWeights factor weights]
  exact Nat.mul_pos hfactor hsmall

theorem ofFinWeights_conditionCap (small large : Nat) (bound : small ≤ large)
    (largeWeights : Fin (large + 1) → Nat) (smallWeights : Fin (small + 1) → Nat)
    (hlarge : 0 < natSum (large + 1) (finWeight largeWeights))
    (hsmall : 0 < natSum (small + 1) (finWeight smallWeights))
    (factor : Nat)
    (weights : ∀ k, largeWeights (liftFinCap bound k) = factor * smallWeights k)
    (positive : (ofFinWeights (large + 1) largeWeights hlarge).EventPositive
      (fun x => decide (x.val ≤ small))) :
    (conditionFinCap (⟨ofFinWeights (large + 1) largeWeights hlarge⟩ : Distro _) small positive).SameLaw
      ⟨ofFinWeights (small + 1) smallWeights hsmall⟩ := by
  apply Distro.sameLaw_of_singletons _ _ (List.finRange (small + 1))
    (finRange_nodup _) (fun value => List.mem_finRange value)
  intro k
  change FiniteProbRecord.eventMass
      (((finWeighted (large + 1) largeWeights).filter (fun atom => decide (atom.1.val ≤ small))).map
        (fun atom => (censorFailureCount small atom.1.val, atom.2))) (FiniteProbRecord.singletonEvent k) *
        FiniteProbRecord.totalMass (finWeighted (small + 1) smallWeights) =
    FiniteProbRecord.eventMass (finWeighted (small + 1) smallWeights) (FiniteProbRecord.singletonEvent k) *
      FiniteProbRecord.eventMass (finWeighted (large + 1) largeWeights) (fun x => decide (x.val ≤ small))
  rw [FiniteProbRecord.eventMass_map_labels _ (fun x : Fin (large + 1) => censorFailureCount small x.val),
    FiniteProbRecord.eventMass_filter_event _ (fun x : Fin (large + 1) => decide (x.val ≤ small))]
  have events : (fun x : Fin (large + 1) => decide (x.val ≤ small) &&
      FiniteProbRecord.singletonEvent k (censorFailureCount small x.val)) =
        FiniteProbRecord.singletonEvent (liftFinCap bound k) := by
    funext x
    simp only [FiniteProbRecord.singletonEvent, censorFailureCount, Fin.ext_iff, liftFinCap]
    by_cases within : x.val ≤ small
    · simp only [within, decide_true, Bool.true_and, Nat.min_eq_left within]
    · have ne : x.val ≠ k.val := by have hk := k.isLt; omega
      simp only [within, decide_false, Bool.false_and, ne]
  rw [events, eventMass_finWeighted_singleton, eventMass_finWeighted_singleton,
    totalMass_finWeighted, finWeighted_prefix_scaled small large bound largeWeights smallWeights factor weights,
    weights]
  ac_rfl

def censorFinCap {large : Nat} (μ : Distro (Fin (large + 1))) (small : Nat) : Distro (Fin (small + 1)) :=
  μ.map (fun x => censorFailureCount small x.val)

theorem ofFinWeights_censorCap (small large : Nat) (bound : small ≤ large)
    (largeWeights : Fin (large + 1) → Nat) (smallWeights : Fin (small + 1) → Nat)
    (hlarge : 0 < natSum (large + 1) (finWeight largeWeights))
    (hsmall : 0 < natSum (small + 1) (finWeight smallWeights)) (factor : Nat)
    (weights : ∀ k, k.val < small → largeWeights (liftFinCap bound k) = factor * smallWeights k)
    (normalizers : natSum (large + 1) (finWeight largeWeights) =
      factor * natSum (small + 1) (finWeight smallWeights)) :
    (censorFinCap (⟨ofFinWeights (large + 1) largeWeights hlarge⟩ : Distro _) small).SameLaw
      ⟨ofFinWeights (small + 1) smallWeights hsmall⟩ := by
  apply Distro.sameLaw_of_singletons_except _ _ (List.finRange (small + 1))
    (finRange_nodup _) (fun value => List.mem_finRange value) (Fin.last small)
  intro k ne
  have inside : k.val < small := by
    have hk := k.isLt
    have different : k.val ≠ small := fun h => ne (Fin.ext h)
    omega
  change FiniteProbRecord.eventMass
      ((finWeighted (large + 1) largeWeights).map
        (fun atom => (censorFailureCount small atom.1.val, atom.2))) (FiniteProbRecord.singletonEvent k) *
        FiniteProbRecord.totalMass (finWeighted (small + 1) smallWeights) =
    FiniteProbRecord.eventMass (finWeighted (small + 1) smallWeights) (FiniteProbRecord.singletonEvent k) *
      FiniteProbRecord.totalMass (finWeighted (large + 1) largeWeights)
  rw [FiniteProbRecord.eventMass_map_labels _ (fun x : Fin (large + 1) => censorFailureCount small x.val)]
  have events : (fun x : Fin (large + 1) =>
      FiniteProbRecord.singletonEvent k (censorFailureCount small x.val)) =
        FiniteProbRecord.singletonEvent (liftFinCap bound k) := by
    funext x
    simp only [FiniteProbRecord.singletonEvent, censorFailureCount, Fin.ext_iff, liftFinCap]
    by_cases within : x.val ≤ small
    · rw [Nat.min_eq_left within]
    · have smallNe : small ≠ k.val := by omega
      have largeNe : x.val ≠ k.val := by omega
      simp only [Nat.min_eq_right (by omega : small ≤ x.val), smallNe, largeNe]
  rw [events, eventMass_finWeighted_singleton, eventMass_finWeighted_singleton,
    totalMass_finWeighted, totalMass_finWeighted, normalizers, weights k inside]
  ac_rfl


end Thesis.Probability.Distros
