import Thesis.Probability.FiniteRecordCatalogue

namespace Thesis.Probability.Examples.FiniteRecordCatalogue

open Probability.FiniteRecordCatalogue

/-!
# Bounded source laws retain repeated labels, zeros and empty boundaries

Small exact computations test the actual catalogue, not a declared coverage
interface. The general coverage theorem separately retains an original record
with repeated labels and a zero-weight occurrence. A zero denominator bound
or an empty alphabet cannot manufacture a normalized law; an empty family of
sources still has its one legitimate empty assignment.
-/

theorem no_empty_alphabet_law : (catalogue 0 3).length = 0 := by decide +kernel
theorem no_zero_denominator_law : (catalogue 2 0).length = 0 := by decide +kernel
theorem two_unit_denominator_laws : (catalogue 2 1).length = 2 := by decide +kernel
theorem five_small_binary_laws : (catalogue 2 2).length = 5 := by decide +kernel
theorem empty_factor_family : (factorCatalogue 0 (fun index => Fin.elim0 index) 0).length = 1 := by decide +kernel

def repeated : FiniteProbRecord (Fin 2) :=
  ⟨[(0, 1), (0, 0), (1, 2), (0, 1)], 4, by decide, rfl⟩

theorem original_denominator_retained : (canonical repeated).den = 4 := canonical_den repeated
theorem canonical_is_listed : canonical repeated ∈ catalogue 2 4 := canonical_mem repeated 4 (Nat.le_refl 4)

theorem every_event_preserved (event : Event (Fin 2)) :
    QProb.Equiv ((canonical repeated).probVal event) (repeated.probVal event) := canonical_probVal repeated event

theorem repeated_zero_occurrences_aggregate : (canonical repeated).atoms = [(0, 2), (1, 2)] := by decide +kernel

end Thesis.Probability.Examples.FiniteRecordCatalogue
