import Thesis.CausalTransport.CausalEquivalence
import Thesis.Causality.BinaryBowModel
import Thesis.Examples.CausalAbstractionExtension

namespace Thesis.Examples.CausalEquivalence

open Probability Causality CausalEquivalence
open Thesis.Examples.CausalAbstraction
open FiniteProduct

/-!
Pointer theorems for the support-aware equivalence hierarchy. AND/OR models
and τ/ω data are imported from the existing abstraction examples. The
chain/bow pair reuses `BinaryBow.model` at the copy-chain's observational
law, the same generative comparison as the catalogue examples, without
rebuilding the bow SCM.
-/

/-- AND exact ω implies interventional agreement on every allowed pair. -/
theorem and_agrees_on_allowed (intervention : HardIntervention microSignature)
    (action : HardIntervention macroSignature)
    (defined : andInterventionMap.omega intervention = some action) :
    InterventionalAgreeAlong andInterventionMap.microModel
      andInterventionMap.macroModel andInterventionMap.assignmentMap
      intervention action :=
  interventionalAgreeAlong_of_exact andInterventionMap and_intervention_exact
    intervention action defined

private theorem and_empty_omega :
    andOmega (HardIntervention.empty microSignature) =
      some (coarseAction none none) :=
  rfl

theorem and_empty_defined :
    andInterventionMap.omega (HardIntervention.empty microSignature) =
      some (HardIntervention.empty macroSignature) := by
  refine Eq.trans and_empty_omega ?_
  apply congrArg some
  apply HardIntervention.extensional
  intro node
  simp [coarseAction, HardIntervention.empty, FiniteLatentSCM.noIntervention]
  rfl

/-- Empty `do` is in the AND ω domain, so exactness yields observational
agreement along the merge. -/
theorem and_observational_along :
    ObservationalAgreeAlong andInterventionMap.microModel
      andInterventionMap.macroModel andInterventionMap.assignmentMap :=
  observationalAgreeAlong_of_exact_empty andInterventionMap
    and_intervention_exact and_empty_defined

/-- OR: the coarse observational cells match the τ-pushforward of the micro
joint, including zeros. -/
theorem or_observational_along :
    ObservationalAgreeAlong microModel orMacro (mergeAssignment Bool.or) := by
  have h : observationalAgreeAlongBool microModel orMacro (mergeAssignment Bool.or) =
      true := by
    decide +kernel
  exact observationalAgreeAlong_of_bool h

/-- OR: observational CPT match does not give interventional agreement at
the declared double surgery. -/
theorem or_not_interventional_along :
    ¬ InterventionalAgreeAlong microModel orMacro (mergeAssignment Bool.or)
        microDoubleTrue macroDoTrue := by
  intro agrees
  exact or_merge_fails.2.2 (agrees yTrue)

/-- Observational agreement along τ does not imply exact ω. The OR
coarsening is the witness: joints match, the declared surgery does not. -/
theorem or_observational_not_exact :
    ObservationalAgreeAlong microModel orMacro (mergeAssignment Bool.or) ∧
      ¬ InterventionalAgreeAlong microModel orMacro (mergeAssignment Bool.or)
          microDoubleTrue macroDoTrue :=
  ⟨or_observational_along, or_not_interventional_along⟩

section ChainBow
open BinaryBow

private def fairBit : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- Copy-chain on the bow host signature: `X` is a fair bit and `Y` copies
`X`. This is the catalogue chain generator, not a new SCM family. -/
private def chainLatent : LatentExtension signature where
  count := 1
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun _ child => decide (child.val = 0)

def chainModel : ExactModel signature where
  latent := chainLatent
  factor := fun _ => fairBit
  prior := record 1 (fun _ => Bool) (fun _ => fairBit)
  product_law := record_rectangular_probVal 1 (fun _ => Bool) (fun _ => fairBit)
  mechanism := fun child parents inputs =>
    if hx : child = x then
      inputs ⟨0, by decide⟩ (by simp [chainLatent, hx, x])
    else
      parents x (by
        rcases node_cases child with same | same
        · exact (hx same).elim
        · simp [signature, x, y, same])

/-- Bow lower endpoint at the chain's actual observational law. -/
def bowLowerModel : ExactModel signature :=
  model chainModel.observationalDist false

def doX : HardIntervention signature := intervention true

private def yTrue : Event signature.Assignment := fun assignment => assignment y

theorem chain_bow_observational :
    ObservationalEquiv chainModel bowLowerModel := by
  intro event
  exact QProb.equiv_symm
    (observationalValue_preserved chainModel.observationalDist false event)

theorem chain_doX_y :
    QProb.Equiv (chainModel.interventionalValue doX.value yTrue) QProb.one := by
  decide +kernel

private def half : QProb := ⟨1, 2, by decide⟩

theorem bow_doX_y :
    QProb.Equiv (bowLowerModel.interventionalValue doX.value yTrue) half := by
  decide +kernel

/-- Same `P(V)` does not give the same `P(Y | do(X))`. The family is the
single declared intervention `do(X{=}true)`. -/
theorem chain_bow_not_interventional :
    ¬ InterventionalEquiv (fun action => action = doX)
        chainModel bowLowerModel := by
  intro agrees
  have same := agrees doX rfl yTrue
  have collapsed : QProb.Equiv QProb.one half :=
    QProb.equiv_trans (QProb.equiv_symm chain_doX_y)
      (QProb.equiv_trans same bow_doX_y)
  exact of_decide_eq_false (by decide) collapsed

theorem chain_bow_observational_not_interventional :
    ObservationalEquiv chainModel bowLowerModel ∧
      ¬ InterventionalEquiv (fun action => action = doX)
          chainModel bowLowerModel :=
  ⟨chain_bow_observational, chain_bow_not_interventional⟩

end ChainBow

end Thesis.Examples.CausalEquivalence
