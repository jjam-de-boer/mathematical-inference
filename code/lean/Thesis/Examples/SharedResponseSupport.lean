import Thesis.CausalTransport.SharedResponseSupport
import Thesis.Examples.SharedResponseLinearBounds

namespace Thesis.Causality.Examples.SharedResponseSupport

open Probability Causality.SharedResponse

/-!
# Support pruning does not prune off-factual response rows

The binary bow's factual point law leaves two of its eight complete response
tables supported. Both remain: after forcing the observationally null action,
one returns false and the other returns true. These are small checks of the
filter and structural evaluator, not executions of the linear optimizer.

The three-valued fixture separately retains a repeated-label rational record
with zero occurrences and an unreduced denominator. Its constant response at
the null observed value is excluded as a positive source atom, but that value
remains in the observed domain and can still be forced by hard intervention.
Coverage also passes through the actual original-native-model adapter.
-/

namespace Bow

open BinaryBow
open SharedResponseLinearBounds.Bow (observed original original_fits)

def responseTable (offFactual : Bool) : Table signature :=
  responseOf signature (BinaryBow.model observed offFactual) (fun _ _ => false)

theorem full_grid_has_eight : (enumeration signature).length = 8 := by decide +kernel

theorem supported_grid_has_two : (supportedEnumeration signature observed).length = 2 := by decide +kernel

theorem both_off_factual_tables_remain (offFactual : Bool) :
    responseTable offFactual ∈ supportedEnumeration signature observed := by
  cases offFactual <;> decide +kernel

theorem retained_intervention_response (offFactual : Bool) :
    eval signature (intervention true).value (responseTable offFactual) y = offFactual := by
  cases offFactual <;> decide +kernel

theorem original_native_law_covered (offFactual : Bool) :
    (⟨lawOfNative signature (original offFactual).model⟩ : Distros.Distro (Table signature)).AlmostSurely
      (fun table => table ∈ supportedEnumeration signature observed) :=
  lawOfNative_supportedEnumeration signature observed (original offFactual) (original_fits offFactual)

end Bow

namespace Unary

open SharedResponseLinearBounds.Unary

theorem supported_grid_has_two : (supportedEnumeration signature observed).length = 2 := by decide +kernel

theorem null_response_atom_excluded : table (2 : Fin 3) ∉ supportedEnumeration signature observed := by decide +kernel

/-- Coverage is almost sure, not literal membership of every listed atom:
the old record still contains its excluded zero occurrence at value two. -/
theorem repeated_zero_record_covered :
    (⟨law⟩ : Distros.Distro (Table signature)).AlmostSurely
      (fun response => response ∈ supportedEnumeration signature observed) :=
  fits_supportedEnumeration signature observed ⟨law⟩ law_fits

/-- Filtering source coordinates leaves every declared intervention value
and every local response row available to the unchanged evaluator. -/
theorem null_target_still_allowed (response : Table signature) :
    eval signature forceTwo.value response node = (2 : Fin 3) := by
  change evalNode signature forceTwo.value response node = (2 : Fin 3)
  rw [evalNode]
  rfl

end Unary
end Thesis.Causality.Examples.SharedResponseSupport
