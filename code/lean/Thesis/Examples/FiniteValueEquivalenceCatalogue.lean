import Thesis.CausalTransport.FiniteValueEquivalenceCatalogue

namespace Thesis.Causality.Examples.FiniteValueEquivalenceCatalogue

open Probability ValueEquivalenceCatalogue

/-!
# Genuine bijections, incompatible sizes and empty boundaries

Both Boolean permutations are accepted, not just one preferred conversion.
The checker rejects a constant forward map. A nonempty public domain cannot
be represented by zero codes, whereas two empty domains have one empty
conversion. These are tiny kernel checks, not an exhaustive native-table run.
-/

def booleans : List Bool := [false, true]
theorem booleans_complete (value : Bool) : value ∈ booleans := by cases value <;> simp [booleans]

theorem two_boolean_permutations : (catalogue 2 booleans booleans_complete).length = 2 := by decide +kernel

def collapsed : Raw 2 Bool := ⟨fun _ => false, fun _ => 0⟩

theorem collapsed_conversion_rejected : check booleans collapsed = false := by decide +kernel

theorem no_codes_cannot_represent_booleans : (catalogue 0 booleans booleans_complete).length = 0 := by decide +kernel

theorem unique_empty_conversion :
    (catalogue 0 ([] : List (Fin 0)) (fun value => Fin.elim0 value)).length = 1 := by decide +kernel

theorem every_boolean_conversion_listed (conversion : ValueEquivalence (Fin 2) Bool) :
    conversion ∈ catalogue 2 booleans booleans_complete := catalogue_complete _ _ _ conversion

end Thesis.Causality.Examples.FiniteValueEquivalenceCatalogue
