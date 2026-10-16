import Thesis.Probability.FiniteRecord

namespace Thesis.Probability.FiniteProbRecord

/-!
# Positive support, without assuming a strictly positive record

A record may repeat labels or list zero-weight occurrences. Its support is
therefore the positivity of the *whole singleton mass*, not membership in
the atom list. An event is positive exactly when it contains a supported
label. The proofs use finite-list recursion and natural-number tests; they
do not choose a positive label to define any computational object.

On an explicitly enumerated carrier, `eventSupported` is an executable
finite Boolean test. It can also be run on a hypothetical support pattern,
without probabilities. Subsequent causal-expression analysis supplies the
actual assignment enumeration and proves that this abstraction is exact.
-/

theorem eventMass_pos_iff_exists_atom (atoms : List (Ω × Nat)) (event : Event Ω) :
    0 < eventMass atoms event ↔
      ∃ atom, atom ∈ atoms ∧ 0 < atom.2 ∧ event atom.1 = true := by
  induction atoms with
  | nil => simp [eventMass]
  | cons atom rest ih =>
      rcases atom with ⟨value, weight⟩
      cases selected : event value with
      | false =>
          simp only [eventMass, selected, Bool.false_eq_true, if_false]
          constructor
          · intro positive
            rcases ih.mp positive with ⟨atom, listed, positive, holds⟩
            exact ⟨atom, List.mem_cons_of_mem _ listed, positive, holds⟩
          · rintro ⟨atom, listed, positive, holds⟩
            rcases List.mem_cons.mp listed with same | later
            · subst atom
              rw [selected] at holds
              cases holds
            · exact ih.mpr ⟨atom, later, positive, holds⟩
      | true =>
          simp only [eventMass, selected, if_true]
          constructor
          · intro positive
            by_cases headPositive : 0 < weight
            · exact ⟨(value, weight), by simp, headPositive, selected⟩
            · have tailPositive : 0 < eventMass rest event := by omega
              rcases ih.mp tailPositive with ⟨atom, listed, positive, holds⟩
              exact ⟨atom, List.mem_cons_of_mem _ listed, positive, holds⟩
          · rintro ⟨atom, listed, positive, holds⟩
            rcases List.mem_cons.mp listed with same | later
            · subst atom
              exact Nat.lt_of_lt_of_le positive (Nat.le_add_right _ _)
            · have tailPositive := ih.mpr ⟨atom, later, positive, holds⟩
              omega

def support [DecidableEq Ω] (record : FiniteProbRecord Ω) (value : Ω) : Bool :=
  decide (record.EventPositive (singletonEvent value))

theorem eventPositive_iff_exists_supported [DecidableEq Ω]
    (record : FiniteProbRecord Ω) (event : Event Ω) :
    record.EventPositive event ↔ ∃ value, record.support value = true ∧ event value = true := by
  constructor
  · intro positive
    rcases (eventMass_pos_iff_exists_atom record.atoms event).mp positive with
      ⟨atom, listed, atomPositive, selected⟩
    refine ⟨atom.1, ?_, selected⟩
    change decide (record.EventPositive (singletonEvent atom.1)) = true
    apply (decide_eq_true_eq).mpr
    exact (eventMass_pos_iff_exists_atom record.atoms _).mpr
      ⟨atom, listed, atomPositive, by simp [singletonEvent]⟩
  · rintro ⟨value, supported, selected⟩
    have positive : record.EventPositive (singletonEvent value) := of_decide_eq_true supported
    rcases (eventMass_pos_iff_exists_atom record.atoms _).mp positive with
      ⟨atom, listed, atomPositive, same⟩
    have equalLabel : atom.1 = value := of_decide_eq_true same
    exact (eventMass_pos_iff_exists_atom record.atoms _).mpr
      ⟨atom, listed, atomPositive, by rw [equalLabel]; exact selected⟩

/-- The input pattern describes whole-label positivity, not atom-list
membership. Duplicate entries in the carrier list cannot change this test. -/
def eventSupported (values : List Ω) (pattern : Ω → Bool) (event : Event Ω) : Bool :=
  values.any (fun value => pattern value && event value)

theorem eventSupported_eq [DecidableEq Ω] (record : FiniteProbRecord Ω)
    (values : List Ω) (complete : ∀ value, value ∈ values) (event : Event Ω) :
    eventSupported values record.support event = decide (record.EventPositive event) := by
  apply Bool.eq_iff_iff.mpr
  simp only [eventSupported, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨value, _, supported, selected⟩
    exact (eventPositive_iff_exists_supported record event).mpr ⟨value, supported, selected⟩
  · intro positive
    rcases (eventPositive_iff_exists_supported record event).mp positive with
      ⟨value, supported, selected⟩
    exact ⟨value, complete value, supported, selected⟩

/-- Equal positive support preserves positivity of every event, although
the two records can assign entirely different nonzero rational masses. -/
theorem eventPositive_iff_of_support_eq [DecidableEq Ω]
    {left right : FiniteProbRecord Ω} (same : left.support = right.support) (event : Event Ω) :
    left.EventPositive event ↔ right.EventPositive event := by
  rw [eventPositive_iff_exists_supported, eventPositive_iff_exists_supported, same]

/-- Probability-one tests also depend only on support: all positive mass
must avoid the complement. Normalization is essential to this statement. -/
theorem probVal_one_iff_complement_not_positive (record : FiniteProbRecord Ω) (event : Event Ω) :
    QProb.Equiv (record.probVal event) QProb.one ↔
      ¬record.EventPositive (fun value => !(event value)) := by
  have partition := eventMass_add_complement record.atoms event
  rw [record.total_mass] at partition
  simp only [QProb.Equiv, probVal, QProb.one, Nat.mul_one, Nat.one_mul, EventPositive]
  omega

end Thesis.Probability.FiniteProbRecord
