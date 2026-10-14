import Thesis.Probability.Distros.BetaBinomial
import Thesis.Probability.Distros.LawEquivalence

namespace Thesis.Probability.Distros
open Combinatorics

/-!
Ordered Pólya words are exchangeable.  Conditioning an actual finite path
record on a supported observed word and dropping that word gives the exact
reinforced continuation law.  The two next-colour probabilities are stated
with the updated counts, including deterministic supported prefixes.
-/

theorem polyaSuccesses_le_length (path : List Bool) : polyaSuccesses path ≤ path.length := by
  induction path with
  | nil => exact Nat.le_refl 0
  | cons head rest ih => cases head <;> simp only [polyaSuccesses, List.length_cons] <;> omega

def polyaFailures (path : List Bool) : Nat := path.length - polyaSuccesses path

theorem polyaFailures_cons_true (path : List Bool) : polyaFailures (true :: path) = polyaFailures path := by
  simp only [polyaFailures, List.length_cons, polyaSuccesses, Nat.succ_sub_succ]

theorem polyaFailures_cons_false (path : List Bool) : polyaFailures (false :: path) = polyaFailures path + 1 := by
  have bound := polyaSuccesses_le_length path
  simp only [polyaFailures, List.length_cons, polyaSuccesses]
  omega

/-- The unnormalised probability of an ordered colour word. -/
def polyaWordWeight (a b : Nat) (path : List Bool) : Nat :=
  risingFactorial a (polyaSuccesses path) * risingFactorial b (polyaFailures path)

theorem polyaWordWeight_true (a b : Nat) (path : List Bool) :
    polyaWordWeight a b (true :: path) = a * polyaWordWeight (a + 1) b path := by
  simp only [polyaWordWeight, polyaSuccesses, polyaFailures_cons_true, risingFactorial_head, Nat.mul_assoc]

theorem polyaWordWeight_false (a b : Nat) (path : List Bool) :
    polyaWordWeight a b (false :: path) = b * polyaWordWeight a (b + 1) path := by
  simp only [polyaWordWeight, polyaSuccesses, polyaFailures_cons_false, risingFactorial_head]
  ac_rfl

/-- Select an exact history, then test an event on the remaining suffix. -/
def polyaPrefixEvent : List Bool → Event (List Bool) → Event (List Bool)
  | [], event => event
  | true :: history, event => fun
      | true :: path => polyaPrefixEvent history event path
      | _ => false
  | false :: history, event => fun
      | false :: path => polyaPrefixEvent history event path
      | _ => false

/-- Every suffix event factors into the history word weight and the same
event under the urn whose two counts have been reinforced by the history. -/
theorem polyaPrefixEvent_mass (history : List Bool) (n a b : Nat) (event : Event (List Bool)) :
    FiniteProbRecord.eventMass (polyaPathAtoms (history.length + n) a b)
        (polyaPrefixEvent history event) =
      polyaWordWeight a b history *
        FiniteProbRecord.eventMass
          (polyaPathAtoms n (a + polyaSuccesses history) (b + polyaFailures history)) event := by
  induction history generalizing n a b with
  | nil => simp only [List.length_nil, Nat.zero_add, polyaPrefixEvent,
      polyaWordWeight, polyaSuccesses, polyaFailures, Nat.sub_self,
      risingFactorial, Nat.add_zero, Nat.one_mul]
  | cons head history ih =>
      have len : (head :: history).length + n = (history.length + n) + 1 := by
        simp only [List.length_cons]
        omega
      rw [len, polyaPathAtoms, FiniteProbRecord.eventMass_append,
        FiniteProbRecord.eventMass_map_weight _ (fun path => true :: path) a,
        FiniteProbRecord.eventMass_map_weight _ (fun path => false :: path) b]
      cases head with
      | true =>
          simp only [polyaPrefixEvent, FiniteProbRecord.eventMass_false,
            Nat.mul_zero, Nat.add_zero, polyaWordWeight_true,
            polyaSuccesses, polyaFailures_cons_true]
          rw [ih]
          have index : a + (polyaSuccesses history + 1) = a + 1 + polyaSuccesses history := by omega
          rw [index]
          ac_rfl
      | false =>
          simp only [polyaPrefixEvent, FiniteProbRecord.eventMass_false,
            Nat.mul_zero, Nat.zero_add, polyaWordWeight_false,
            polyaSuccesses, polyaFailures_cons_false]
          rw [ih]
          have index : b + (polyaFailures history + 1) = b + 1 + polyaFailures history := by omega
          rw [index]
          ac_rfl

theorem polyaPrefixEvent_empty (history : List Bool) :
    polyaPrefixEvent history (FiniteProbRecord.singletonEvent []) =
      FiniteProbRecord.singletonEvent history := by
  funext path
  induction history generalizing path with
  | nil => rfl
  | cons head history ih =>
      cases head <;> cases path with
      | nil => rfl
      | cons other path =>
          cases other <;> simp only [polyaPrefixEvent, ih, FiniteProbRecord.singletonEvent,
            List.cons.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and, true_and, decide_false]

theorem polyaPath_word_mass (a b : Nat) (path : List Bool) :
    FiniteProbRecord.eventMass (polyaPathAtoms path.length a b)
      (FiniteProbRecord.singletonEvent path) = polyaWordWeight a b path := by
  have h := polyaPrefixEvent_mass path 0 a b (FiniteProbRecord.singletonEvent [])
  simpa only [Nat.add_zero, polyaPrefixEvent_empty, polyaPathAtoms,
    FiniteProbRecord.eventMass, FiniteProbRecord.singletonEvent,
    decide_true, if_true, Nat.add_zero, Nat.mul_one] using h

/-- Ordered path probability depends only on its two colour counts. -/
theorem polyaPath_word_pmf (a b : Nat) (positive : 0 < a + b) (path : List Bool) :
    QProb.Equiv
      ((polyaPathRecord path.length a b positive).probVal (FiniteProbRecord.singletonEvent path))
      ⟨polyaWordWeight a b path, risingFactorial (a + b) path.length,
        risingFactorial_pos _ _ positive⟩ := by
  change FiniteProbRecord.eventMass (polyaPathAtoms path.length a b)
      (FiniteProbRecord.singletonEvent path) * risingFactorial (a + b) path.length = _
  rw [polyaPath_word_mass]
  rfl

theorem polyaPath_exchangeable (a b : Nat) (positive : 0 < a + b)
    (path other : List Bool) (length : path.length = other.length)
    (counts : polyaSuccesses path = polyaSuccesses other) :
    QProb.Equiv
      ((polyaPathRecord path.length a b positive).probVal (FiniteProbRecord.singletonEvent path))
      ((polyaPathRecord path.length a b positive).probVal (FiniteProbRecord.singletonEvent other)) := by
  have weights : polyaWordWeight a b path = polyaWordWeight a b other := by
    simp only [polyaWordWeight, polyaFailures, length, counts]
  have h := polyaPath_word_pmf a b positive other
  rw [← length, ← weights] at h
  exact QProb.equiv_trans (polyaPath_word_pmf a b positive path) (QProb.equiv_symm h)

theorem polyaSuccesses_perm {path other : List Bool} (perm : path.Perm other) :
    polyaSuccesses path = polyaSuccesses other := by
  induction perm with
  | nil => rfl
  | cons head _ ih => cases head <;> simp only [polyaSuccesses, ih]
  | swap left right tail =>
      cases left <;> cases right <;> simp only [polyaSuccesses, Nat.add_assoc]
  | trans _ _ ih ih' => exact ih.trans ih'

/-- Permuting the order of a finite colour word preserves its probability. -/
theorem polyaPath_permutation (a b : Nat) (positive : 0 < a + b)
    (path other : List Bool) (perm : path.Perm other) :
    QProb.Equiv
      ((polyaPathRecord path.length a b positive).probVal (FiniteProbRecord.singletonEvent path))
      ((polyaPathRecord path.length a b positive).probVal (FiniteProbRecord.singletonEvent other)) :=
  polyaPath_exchangeable a b positive path other perm.length_eq (polyaSuccesses_perm perm)

theorem polyaPrefixEvent_drop (history : List Bool) (event : Event (List Bool)) (path : List Bool) :
    polyaPrefixEvent history event path =
      (polyaPrefixEvent history topEvent path && event (path.drop history.length)) := by
  induction history generalizing path with
  | nil => rfl
  | cons head history ih =>
      cases head <;> cases path with
      | nil => rfl
      | cons other path =>
          cases other <;> simp only [polyaPrefixEvent, List.length_cons, List.drop_succ_cons,
            Bool.false_and, ih]

theorem polyaPrefixEvent_positive (history : List Bool) (n a b : Nat)
    (positive : 0 < a + b) (supported : 0 < polyaWordWeight a b history) :
    (polyaPathRecord (history.length + n) a b positive).EventPositive
      (polyaPrefixEvent history topEvent) := by
  change 0 < FiniteProbRecord.eventMass (polyaPathAtoms (history.length + n) a b)
    (polyaPrefixEvent history topEvent)
  rw [polyaPrefixEvent_mass, FiniteProbRecord.eventMass_top, polyaPath_totalMass]
  exact Nat.mul_pos supported (risingFactorial_pos _ _ (by omega))

/-- The suffix record after conditioning the actual path on a supported
observed word, then dropping that word. -/
def polyaContinuationDistro (history : List Bool) (n a b : Nat)
    (positive : 0 < a + b) (supported : 0 < polyaWordWeight a b history) : Distro (List Bool) :=
  ⟨((polyaPathRecord (history.length + n) a b positive).conditionOn
    (polyaPrefixEvent history topEvent) (polyaPrefixEvent_positive history n a b positive supported)).map
      (List.drop history.length)⟩

/-- Observing a supported ordered prefix gives exactly the future Pólya
law with the two initial counts increased by the observed colour counts. -/
theorem polyaContinuation_updated (history : List Bool) (n a b : Nat)
    (positive : 0 < a + b) (supported : 0 < polyaWordWeight a b history) :
    (polyaContinuationDistro history n a b positive supported).SameLaw
      ⟨polyaPathRecord n (a + polyaSuccesses history) (b + polyaFailures history) (by omega)⟩ := by
  intro event
  refine QProb.equiv_trans (FiniteProbRecord.map_probVal _ _ event) ?_
  refine QProb.equiv_trans
    (FiniteProbRecord.conditionOn_probVal _ _ _
      (polyaPrefixEvent_positive history n a b positive supported)) ?_
  have events : (fun path => polyaPrefixEvent history topEvent path &&
      event (path.drop history.length)) = polyaPrefixEvent history event := by
    funext path
    exact (polyaPrefixEvent_drop history event path).symm
  simp only [FiniteProbRecord.probVal, QProb.Equiv, QProb.div, polyaPathRecord]
  rw [events, polyaPrefixEvent_mass, polyaPrefixEvent_mass,
    FiniteProbRecord.eventMass_top, polyaPath_totalMass]
  ac_rfl

theorem polya_next_true_after_prefix (history : List Bool) (a b : Nat)
    (positive : 0 < a + b) (supported : 0 < polyaWordWeight a b history) :
    QProb.Equiv
      ((polyaContinuationDistro history 1 a b positive supported).record.probVal
        (FiniteProbRecord.singletonEvent [true]))
      ⟨a + polyaSuccesses history, a + b + history.length, by omega⟩ := by
  have counts : polyaSuccesses history + polyaFailures history = history.length :=
    Nat.add_sub_of_le (polyaSuccesses_le_length history)
  refine QProb.equiv_trans (polyaContinuation_updated history 1 a b positive supported
    (FiniteProbRecord.singletonEvent [true])) ?_
  refine QProb.equiv_trans
    (polyaPath_word_pmf (a + polyaSuccesses history) (b + polyaFailures history) (by omega) [true]) ?_
  have total : a + polyaSuccesses history + (b + polyaFailures history) = a + b + history.length := by omega
  dsimp only [polyaFailures] at total
  simp only [QProb.Equiv, polyaWordWeight, polyaSuccesses, polyaFailures,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.sub_self,
    risingFactorial, Nat.add_zero, Nat.mul_one]
  rw [total]

theorem polya_next_false_after_prefix (history : List Bool) (a b : Nat)
    (positive : 0 < a + b) (supported : 0 < polyaWordWeight a b history) :
    QProb.Equiv
      ((polyaContinuationDistro history 1 a b positive supported).record.probVal
        (FiniteProbRecord.singletonEvent [false]))
      ⟨b + polyaFailures history, a + b + history.length, by omega⟩ := by
  have counts : polyaSuccesses history + polyaFailures history = history.length :=
    Nat.add_sub_of_le (polyaSuccesses_le_length history)
  refine QProb.equiv_trans (polyaContinuation_updated history 1 a b positive supported
    (FiniteProbRecord.singletonEvent [false])) ?_
  refine QProb.equiv_trans
    (polyaPath_word_pmf (a + polyaSuccesses history) (b + polyaFailures history) (by omega) [false]) ?_
  have total : a + polyaSuccesses history + (b + polyaFailures history) = a + b + history.length := by omega
  dsimp only [polyaFailures] at total
  simp only [QProb.Equiv, polyaWordWeight, polyaSuccesses, polyaFailures,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.sub_zero,
    risingFactorial, Nat.add_zero, Nat.mul_one, Nat.one_mul]
  rw [total]

end Thesis.Probability.Distros
