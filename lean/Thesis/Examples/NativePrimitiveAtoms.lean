import Thesis.CausalTransport.NativePrimitiveAtoms
import Thesis.Causality.BinaryBowModel
import Thesis.Examples.NativeTypedPrimitives

namespace Thesis.Causality.Examples.NativePrimitiveAtoms

open Probability ProbabilityCode NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping

/-!
# Primitive reflection, literal finite codes and null support boundaries

The two-node mask checks exercise actual dictionary positions rather than
assuming that a selected Boolean function is definitionally the dictionary
function. The native three-valued fixture then runs all seven decoder tags
through atom reflection and back through the opt-in supported constructor.

Graph-valid decoding does not supply missing conditional support. The null
carrier is rejected when demanded, and a transitivity detour is not accepted
as one leaf even when its final endpoints have values. AC retains its own
schema instead of being silently inserted into the seven primitive tags.
No full catalogue enumeration, path search or optimizer is run here.
-/

theorem two_node_mask_codes :
    encodeMask BinaryBow.signature (NodeSet.singleton BinaryBow.x) = 1 ∧
      encodeMask BinaryBow.signature (NodeSet.singleton BinaryBow.y) = 2 ∧
      mask BinaryBow.signature 4 = none := by decide +kernel

example (nodes : NodeSet BinaryBow.signature) :
    mask BinaryBow.signature (encodeMask BinaryBow.signature nodes) = some nodes := mask_encodeMask _ _

def requested : Demand family := atReference (reference 2)

def everyEntry (kind : PrimitiveCode) : TypedPrimitive family :=
  (TypedPrimitive.check family kind NativeTypedPrimitives.emptyQuad requested).get
    (NativeTypedPrimitives.every_tag_has_supported_instance kind)

theorem all_seven_reflect (kind : PrimitiveCode) :
    (reflectPrimitive? (everyEntry kind).checked.derivation).isSome = true :=
  checkPrimitive_reflects _ _ _ _ (everyEntry kind).decoded

theorem all_seven_round_trip (kind : PrimitiveCode) :
    (TypedPrimitive.ofAtom? family requested (everyEntry kind).atom).isSome = true := by
  cases kind <;> decide +kernel

def carrierAtom : DoCalculusAtom projection.observedGraph (.kernel carrier) unitTerm :=
  ((reflectPrimitive? eraseNullCondition).get (by decide +kernel)).atom

theorem carrier_code : carrierAtom.primitiveCode? = some (.rule1, ⟨0, 0, 1, 0⟩) := by decide +kernel

theorem carrier_support_boundary :
    (TypedPrimitive.ofAtom? family (atReference (reference 0)) carrierAtom).isSome = true ∧
      (TypedPrimitive.ofAtom? family requested carrierAtom).isSome = false ∧
      (TypedPrimitive.ofAtom? family (fun _ _ => false) carrierAtom).isSome = true := by decide +kernel

def carrierEntry : TypedPrimitive family :=
  .ofAtom family (atReference (reference 0)) carrierAtom .rule1 ⟨0, 0, 1, 0⟩ carrier_code (by decide +kernel)

/-- Catalogue coverage is obtained from the constructed entry's theorem;
the potentially large list is never normalized to locate this witness. -/
theorem carrier_is_catalogued : carrierEntry ∈ primitiveCatalogue family :=
  TypedPrimitive.ofAtom_mem_catalogue family (atReference (reference 0)) carrierAtom .rule1 ⟨0, 0, 1, 0⟩ carrier_code (by decide +kernel)

theorem carrier_endpoints_are_literal :
    carrierEntry.checked.left = .kernel carrier ∧ carrierEntry.checked.right = unitTerm := ⟨rfl, rfl⟩

theorem reflected_proof_agrees : carrierEntry.atom.toDerivation = carrierEntry.checked.derivation :=
  carrierEntry.atom_toDerivation

theorem hidden_transitivity_is_rejected :
    check family unitTerm requested = true ∧ check family productTerm requested = true ∧
      (reflectPrimitive? carrierDetour).isSome = false ∧
      (reflectPrimitive? (DoCalculusDerivation.refl (G := projection.observedGraph) unitTerm)).isSome = false := by decide +kernel

def commAtom := DoCalculusAtom.multiplyComm (G := projection.observedGraph) unitTerm unitTerm

theorem ac_is_a_separate_schema :
    commAtom.primitiveCode?.isSome = false ∧
      (reflectPrimitive? commAtom.toDerivation).isSome = false ∧
      (TypedPrimitive.ofAtom? family requested commAtom).isSome = false := by decide +kernel

/-- Empty-outcome rule 3 remains defined at a declared, observationally
null action value. This does not assert identification of arbitrary effects
at unobserved actions. -/
def nullActionEntry : TypedPrimitive family :=
  (TypedPrimitive.check family .rule3 ⟨0, 0, 1, 0⟩ requested).get (by decide +kernel)

theorem declared_null_action_is_retained :
    nullActionEntry.atom.primitiveCode? = some (.rule3, ⟨0, 0, 1, 0⟩) ∧
      (TypedPrimitive.ofAtom? family requested nullActionEntry.atom).isSome = true := by decide +kernel

end Thesis.Causality.Examples.NativePrimitiveAtoms
