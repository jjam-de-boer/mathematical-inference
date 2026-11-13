import Thesis.CausalTransport.NativeDerivationTyping
import Thesis.Examples.NativeDerivationReplacement

namespace Thesis.Causality.Examples.NativeDemandTypes

open Probability NativeSupportProfiles NativeKernelInterfaceObstruction
open Thesis.Causality.NativeDemandTyping

/-!
# Demand typing at null, substituted and conflicting profile cells

The existing three-valued native fixture has a declared null reference.
The tests distinguish unused cells, defined zero and defined positive cells;
retain every marginal substitution and fixed-reference obligation; and reject
an undefined weight even though its factor would otherwise be omitted.

The direct proof and the null-carrier detour have identical endpoint terms.
Only the direct proof passes. A second fixture makes the formerly null value
positive in one profile, confirming that a favorable profile cannot certify
another profile's demanded cell. These are small kernel checks and symbolic
exactness applications, not proof search or a rewrite-completion pilot.
-/

def family : List (NativeTemplateInstance projection) := [entry.uniformSupport]
def profileIndex : Fin family.length := ⟨0, by decide⟩

def atReference (fixed : signature.Assignment) : Demand family := fun _ reference => decide (reference = fixed)

theorem finite_type_count : (typeCatalogue family).length = 27 := by decide +kernel

theorem three_distinct_cell_grades :
    typeOf family unitTerm (atReference (reference 0)) profileIndex (reference 0) = .positive ∧
      typeOf family .zero (atReference (reference 0)) profileIndex (reference 0) = .zero ∧
      typeOf family unitTerm (atReference (reference 0)) profileIndex (reference 2) = .unused := by decide +kernel

theorem null_is_rejected_when_demanded :
    (infer family nullConditional (atReference (reference 2))).isSome = false ∧
      (infer family nullConditional (fun _ _ => false)).isSome = true := by decide +kernel

theorem fixed_and_marginal_demands :
    check family (.kernel carrier) (atReference (reference 0)) = true ∧
      check family (.evaluateAt (reference 2) (.kernel carrier)) (atReference (reference 0)) = false ∧
      check family (.marginalize NodeSet.full (.kernel carrier)) (atReference (reference 0)) = false := by decide +kernel

theorem weighted_branch_boundaries :
    check family (.weightedMultiply .zero nullConditional) (atReference (reference 2)) = true ∧
      check family (.multiply .zero nullConditional) (atReference (reference 2)) = false ∧
      check family (.weightedMultiply unitTerm nullConditional) (atReference (reference 2)) = false ∧
      check family (.weightedMultiply nullConditional .zero) (atReference (reference 2)) = false := by decide +kernel

/-- Checking the endpoint types is insufficient: the actual intermediate
carrier remains part of the supplied derivation's type check. -/
theorem detour_keeps_its_intermediate_obligation :
    check family unitTerm (atReference (reference 2)) = true ∧
      check family productTerm (atReference (reference 2)) = true ∧
      checkDerivation family (atReference (reference 2)) expandUnit = true ∧
      checkDerivation family (atReference (reference 2)) carrierDetour = false := by decide +kernel

theorem proof_context_demands :
    checkDerivation family (atReference (reference 2)) (NativeDerivationReplacement.zeroWeight.fill carrierDetour) = true ∧
      checkDerivation family (atReference (reference 2)) (NativeDerivationReplacement.positiveWeight.fill carrierDetour) = false ∧
      checkDerivation family (atReference (reference 0)) (NativeDerivationReplacement.fixedNull.fill carrierDetour) = false ∧
      checkDerivation family (atReference (reference 0)) (NativeDerivationReplacement.marginal.fill carrierDetour) = false := by decide +kernel

/-- The original full support tree is reconstructed from the successful
finite check at its actual requested cell, using that model's own values. -/
noncomputable def direct_support : HiddenDAGLocalDerivationSupport (family.get profileIndex).model (reference 2) expandUnit :=
  supportAt family (atReference (reference 2)) expandUnit (by decide +kernel) profileIndex (reference 2) (by decide +kernel)

def fullSupport : NativeTemplateInstance projection :=
  ⟨entry.template, by
    intro source
    change FiniteProbRecord (Fin 3)
    exact ⟨[(0, 1), (1, 1), (2, 1)], 3, by decide, rfl⟩⟩

def conflicting : List (NativeTemplateInstance projection) := [fullSupport, entry.uniformSupport]

def nullInProfiles (which : Fin conflicting.length → Bool) : Demand conflicting :=
  fun index value => which index && decide (value = reference 2)

theorem every_requested_profile_is_checked :
    check conflicting (.kernel carrier) (nullInProfiles (fun index => decide (index.val = 0))) = true ∧
      check conflicting (.kernel carrier) (nullInProfiles (fun index => decide (index.val = 1))) = false ∧
      check conflicting (.kernel carrier) (nullInProfiles (fun _ => true)) = false := by decide +kernel

/-- The exactness theorem applies to arbitrary terms, proofs and masks on
these same cells; the examples do not replace that quantified bridge. -/
example {left right : ProbabilityTerm signature} (proof : DoCalculusDerivation projection.observedGraph left right)
    (demand : Demand conflicting) :
    (inferDerivation conflicting demand proof).isSome = allNeeded conflicting demand
      (fun index reference => HiddenDAGLocalDerivationSupport.check (conflicting.get index).model reference proof) :=
  inferDerivation_isSome conflicting demand proof

end Thesis.Causality.Examples.NativeDemandTypes
