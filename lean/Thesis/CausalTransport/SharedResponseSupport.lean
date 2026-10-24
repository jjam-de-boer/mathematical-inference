import Thesis.CausalTransport.SharedResponseProblem
import Thesis.Probability.FiniteRecordSupport

namespace Thesis.Causality.SharedResponse

open Probability Probability.Distros

/-!
# Observational-support coverage of the shared response grid

An atom with positive source weight must produce a factual assignment having
positive mass in the fitted observed law. Response tables whose factual
assignments are observationally impossible can therefore be omitted from a
future optimization grid. The lemmas below prove this for every fitted
rational record, including repeated labels and zero-weight occurrences, and
then for the response law of every original native model in the stated class.

Only probability coordinates are filtered. A retained atom is still a full
`Table S`: all local parent rows and all declared observed values remain.
In particular, an observationally null treatment can still select either of
its permitted off-factual responses. No intervention set is restricted.

The filtered enumeration is nonempty for every supplied probability record.
The proof uses a supported observed assignment to exhibit membership in a
proposition; it does not choose source data from propositional existence.

This module establishes coverage only. The existing `problem`, `solveBounds`
and linear elimination engine are unchanged. No speedup or successful causal
solver execution is asserted by this preprocessing theorem.
-/

variable (S : ObservedSignature.{0})

def observationSupported (observed : FiniteProbRecord S.Assignment) (table : Table S) : Bool :=
  observed.support (eval S (FiniteLatentSCM.noIntervention S) table)

def supportedEnumeration (observed : FiniteProbRecord S.Assignment) : List (Table S) :=
  (enumeration S).filter (observationSupported S observed)

/-- Every full response table is in the original grid, so the only new
membership condition is positivity of its complete factual singleton mass. -/
theorem mem_supportedEnumeration_iff (observed : FiniteProbRecord S.Assignment) (table : Table S) :
    table ∈ supportedEnumeration S observed ↔ observationSupported S observed table = true := by
  constructor
  · intro listed
    exact (List.mem_filter.mp listed).2
  · intro accepted
    exact List.mem_filter.mpr ⟨enumeration_complete S table, accepted⟩

theorem supportedEnumeration_nodup (observed : FiniteProbRecord S.Assignment) :
    (supportedEnumeration S observed).Nodup :=
  List.Sublist.nodup List.filter_sublist (enumeration_nodup S)

/-- Constant local equations realize any declared factual assignment. They
are used only to prove that a supported observed cell has a response table. -/
def constantTable (reference : S.Assignment) : Table S := fun child _ => reference child

theorem eval_constantTable_factual (reference : S.Assignment) :
    eval S (FiniteLatentSCM.noIntervention S) (constantTable S reference) = reference := by
  funext child
  change evalNode S (FiniteLatentSCM.noIntervention S) (constantTable S reference) child = reference child
  rw [evalNode]
  rfl

theorem supportedEnumeration_nonempty (observed : FiniteProbRecord S.Assignment) :
    0 < (supportedEnumeration S observed).length := by
  have positive : observed.EventPositive topEvent := by
    change 0 < FiniteProbRecord.eventMass observed.atoms topEvent
    rw [FiniteProbRecord.eventMass_top, observed.total_mass]
    exact observed.den_pos
  rcases (observed.eventPositive_iff_exists_supported topEvent).mp positive with
    ⟨reference, supported, _selected⟩
  have accepted : observationSupported S observed (constantTable S reference) = true := by
    unfold observationSupported
    rw [eval_constantTable_factual]
    exact supported
  exact List.length_pos_of_mem ((mem_supportedEnumeration_iff S observed _).mpr accepted)

/-- A positive occurrence contributes positive mass to its own factual cell.
Fitting the whole observed law transfers that positivity to the supplied data;
neither membership alone nor positivity of the ambient denominator suffices. -/
theorem observationSupported_of_positive_atom (observed : FiniteProbRecord S.Assignment)
    (law : FiniteProbRecord (Table S)) (fitted : Fits S observed law)
    (atom : Table S × Nat) (listed : atom ∈ law.atoms) (positive : 0 < atom.2) :
    observationSupported S observed atom.1 = true := by
  let reference := eval S (FiniteLatentSCM.noIntervention S) atom.1
  have selected : observedEvent S reference atom.1 = true := by
    change decide (reference = reference) = true
    exact decide_eq_true rfl
  have sourcePositive : law.EventPositive (observedEvent S reference) :=
    (FiniteProbRecord.eventMass_pos_iff_exists_atom law.atoms _).mpr ⟨atom, listed, positive, selected⟩
  have observedPositive : observed.EventPositive (FiniteProbRecord.singletonEvent reference) :=
    (QProb.equiv_num_pos_iff (fitted (FiniteProbRecord.singletonEvent reference))).mp sourcePositive
  exact decide_eq_true observedPositive

/-- All positive occurrences remain covered. Excluded zero occurrences need
not be removed from the original record, and no record presentation is changed. -/
theorem fits_supportedEnumeration (observed : FiniteProbRecord S.Assignment)
    (law : Distro (Table S)) (fitted : Fits S observed law.record) :
    law.AlmostSurely (fun table => table ∈ supportedEnumeration S observed) := by
  intro atom listed positive
  exact (mem_supportedEnumeration_iff S observed atom.1).mpr
    (observationSupported_of_positive_atom S observed law.record fitted atom listed positive)

/-- This is an exact forced-zero result, not a heuristic small-mass cutoff.
It applies separately to each occurrence even when labels are repeated. -/
theorem weight_zero_of_not_supported (observed : FiniteProbRecord S.Assignment)
    (law : FiniteProbRecord (Table S)) (fitted : Fits S observed law)
    (atom : Table S × Nat) (listed : atom ∈ law.atoms)
    (excluded : atom.1 ∉ supportedEnumeration S observed) : atom.2 = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro positive
  exact excluded ((mem_supportedEnumeration_iff S observed atom.1).mpr
    (observationSupported_of_positive_atom S observed law fitted atom listed positive))

/-- Coverage ranges over the full original projection-wide native class,
with no source-size, denominator or observational-positivity assumption. -/
theorem lawOfNative_supportedEnumeration (observed : FiniteProbRecord S.Assignment)
    (original : ProjectedHiddenDAGModel (graph S)) (fitted : NativeFits S observed original) :
    (⟨lawOfNative S original.model⟩ : Distro (Table S)).AlmostSurely
      (fun table => table ∈ supportedEnumeration S observed) :=
  fits_supportedEnumeration S observed ⟨lawOfNative S original.model⟩
    (lawOfNative_fits S observed original fitted)

end Thesis.Causality.SharedResponse
