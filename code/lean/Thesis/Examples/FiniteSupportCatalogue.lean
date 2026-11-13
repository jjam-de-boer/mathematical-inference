import Thesis.Probability.FiniteSupportCatalogue
import Thesis.Probability.FiniteProductSupportLaw

namespace Thesis.Probability.Examples.FiniteSupportCatalogue

open FiniteProbRecord

/-!
# Uniform support representatives retain zeros, not numerical weights

The original law repeats a label and includes an explicit zero cell. Its
uniform representative keeps precisely the two positive codes, with mass
one half at each instead of the original one quarter and three quarters.
All mixed-event positivity in a dependent product is nevertheless unchanged.
Empty alphabets reject normalization; empty source families keep their one
empty independent assignment. No original denominator bound is supplied.
-/

def original : FiniteProbRecord (Fin 3) := ⟨[(0, 2), (0, 0), (1, 6), (2, 0)], 8, by decide, rfl⟩

theorem empty_alphabet : Probability.FiniteSupportCatalogue.catalogue 0 = [] :=
  Probability.FiniteSupportCatalogue.empty_alphabet
theorem singleton_alphabet_count : (Probability.FiniteSupportCatalogue.catalogue 1).length = 1 := by decide +kernel
theorem binary_alphabet_count : (Probability.FiniteSupportCatalogue.catalogue 2).length = 3 := by decide +kernel
theorem uniform_denominator : (Probability.FiniteSupportCatalogue.uniformSupport original).den = 2 := by decide +kernel
theorem null_code_retained : (Probability.FiniteSupportCatalogue.uniformSupport original).support 2 = false := by decide +kernel
theorem numerical_probability_changes :
    ¬ QProb.Equiv ((Probability.FiniteSupportCatalogue.uniformSupport original).probVal (singletonEvent 0))
      (original.probVal (singletonEvent 0)) := by decide +kernel

theorem all_event_positivity (event : Event (Fin 3)) :
    (Probability.FiniteSupportCatalogue.uniformSupport original).EventPositive event ↔ original.EventPositive event :=
  eventPositive_iff_of_support_eq (Probability.FiniteSupportCatalogue.uniformSupport_support original) event

theorem all_mixed_product_events (event : Event (Fin 2 → Fin 3)) :
    (FiniteProduct.record 2 (fun _ => Fin 3) (fun _ => Probability.FiniteSupportCatalogue.uniformSupport original)).EventPositive event ↔
      (FiniteProduct.record 2 (fun _ => Fin 3) (fun _ => original)).EventPositive event :=
  FiniteProduct.record_eventPositive_iff_of_factor_support_eq _ _
    (fun _ => Probability.FiniteSupportCatalogue.uniformSupport_support original) event

theorem empty_factor_family_count :
    (Probability.FiniteSupportCatalogue.factorCatalogue 0 (fun source => Fin.elim0 source)).length = 1 := rfl

end Thesis.Probability.Examples.FiniteSupportCatalogue
