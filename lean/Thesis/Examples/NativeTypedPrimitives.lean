import Thesis.CausalTransport.NativeTypedPrimitives
import Thesis.Examples.NativeDemandTypes

namespace Thesis.Causality.Examples.NativeTypedPrimitives

open Probability ProbabilityCode NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping

/-!
# Typed primitive certificates at a declared null reference

The small three-valued fixture distinguishes a zero outcome from undefined
conditioning. Its direct empty-chain primitive remains supported at the
declared null value, while a rule-1 conditional carrier is accepted only
where that carrier is supported (or where nothing is demanded).

Catalogue membership is obtained symbolically from each actual checked
certificate. These tests do not normalize the full primitive catalogue,
run proof search, or claim that two same-typed endpoints are substitutable.
-/

def emptyQuad : QuadCode := ⟨0, 0, 0, 0⟩

theorem finite_demand_count : (demandCatalogue family).length = 8 := by decide +kernel

/-- All seven tags reach their existing primitive checker. This uses the
small empty-mask instances, not a new axiom about any graphical leaf. -/
theorem every_tag_has_supported_instance (kind : PrimitiveCode) :
    (TypedPrimitive.check family kind emptyQuad (atReference (reference 2))).isSome = true := by
  cases kind <;> decide +kernel

/-- Retain the actual decoder's certificate, rather than supplying a
derivation and assuming that it is the checker's returned proof tree. -/
def unitPrimitive : TypedPrimitive family :=
  (TypedPrimitive.check family .chain emptyQuad (atReference (reference 2))).get
    (every_tag_has_supported_instance .chain)

theorem direct_primitive_is_catalogued : unitPrimitive ∈ primitiveCatalogue family :=
  mem_primitiveCatalogue unitPrimitive

theorem direct_primitive_preserves_types : unitPrimitive.leftType = unitPrimitive.rightType :=
  unitPrimitive.types_eq

theorem direct_primitive_grades :
    unitPrimitive.leftType profileIndex (reference 2) = .positive ∧
      unitPrimitive.rightType profileIndex (reference 2) = .positive ∧
      unitPrimitive.leftType profileIndex (reference 0) = .unused := by decide +kernel

/-- P(empty | Z) can be erased where defined, but not at the null value of
Z. An empty demand remains allowed; it does not assign that conditional a value. -/
theorem conditional_carrier_boundaries :
    (TypedPrimitive.check family .rule1 ⟨0, 0, 1, 0⟩ (atReference (reference 0))).isSome = true ∧
      (TypedPrimitive.check family .rule1 ⟨0, 0, 1, 0⟩ (atReference (reference 2))).isSome = false ∧
      (TypedPrimitive.check family .rule1 ⟨0, 0, 1, 0⟩ (fun _ _ => false)).isSome = true := by decide +kernel

/-- A zero-probability outcome is still a defined primitive endpoint.
This differs from the unsupported conditional in the preceding regression. -/
theorem zero_outcome_is_supported :
    (TypedPrimitive.check family .chain ⟨0, 1, 0, 0⟩ (atReference (reference 2))).isSome = true := by decide +kernel

def zeroPrimitive : TypedPrimitive family :=
  (TypedPrimitive.check family .chain ⟨0, 1, 0, 0⟩ (atReference (reference 2))).get zero_outcome_is_supported

theorem zero_outcome_types :
    zeroPrimitive.leftType profileIndex (reference 2) = .zero ∧
      zeroPrimitive.rightType profileIndex (reference 2) = .zero := by decide +kernel

theorem invalid_codes_are_rejected :
    (TypedPrimitive.check family .chain ⟨2, 0, 0, 0⟩ (fun _ _ => false)).isSome = false ∧
      (TypedPrimitive.check family .chain ⟨1, 1, 0, 0⟩ (fun _ _ => false)).isSome = false := by decide +kernel

/-- The preservation theorem applies beyond primitive leaves: a defined
zero weight legitimately omits the unsupported carrier detour. -/
theorem zero_weight_preserves_types :
    typeOf family (.weightedMultiply .zero unitTerm) (atReference (reference 2)) =
      typeOf family (.weightedMultiply .zero productTerm) (atReference (reference 2)) :=
  typeOf_eq_of_checked family (atReference (reference 2))
    (.weightedMultiplyCongr (.refl .zero) carrierDetour) (by decide +kernel)

/-- A checked change of weight keeps precisely the same positive-factor
mask. This does not authorize a detour through an undefined weight. -/
theorem direct_weight_preserves_factor_demand :
    positiveDemand family (atReference (reference 2)) (termStatus family unitTerm) =
      positiveDemand family (atReference (reference 2)) (termStatus family productTerm) :=
  positiveDemand_eq_of_checked family (atReference (reference 2)) expandUnit (by decide +kernel)

end Thesis.Causality.Examples.NativeTypedPrimitives
