import Thesis.CausalTransport.QualitativeCausalScale

namespace Thesis
namespace Causality
namespace Examples
namespace QualitativeCausalScale

open Probability
open Probability.ClaytonWaddington
open Probability.ClaytonWaddington.UrnRatio
open QualitativeDoCalculus
open Causality.QualitativeCausalScale

/-!
Finite checks of the qualitative causal scale.  These fixtures are not
foundations: the theorems live in `Thesis.Causality.QualitativeCausalScale`
and `Thesis.CausalTransport.QualitativeCausalScale`.
-/

def independentScale : QualitativeCausalScale twoBoolSignature :=
  inducedCausal twoBoolIndependentModel rationalScale

theorem independent_scale_inhabited :
    Nonempty (QualitativeCausalScale.{0} twoBoolSignature) :=
  ⟨independentScale⟩

theorem independent_realized :
    RealizedBy independentScale twoBoolIndependentModel :=
  inducedCausal_realized twoBoolIndependentModel rationalScale

/-- Two Boolean nodes with a single arrow `first → second`. -/
def chainSignature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by
    intro _ value
    cases value <;> simp
  value_nodup := by
    intro _
    simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val + 1 = child.val)
  directed_earlier := by
    intro parent child h
    have : parent.val + 1 = child.val := of_decide_eq_true h
    omega

def chainFirst : Fin chainSignature.count := ⟨0, by decide⟩
def chainSecond : Fin chainSignature.count := ⟨1, by decide⟩

def chainLatent : LatentExtension chainSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by
    intro _ value
    cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun l i => decide (l.val = i.val)

def chainCopyModel : ExactModel chainSignature where
  latent := chainLatent
  factor := fun _ => twoBoolFairBit
  prior := FiniteProduct.record 2 (fun _ => Bool) (fun _ => twoBoolFairBit)
  product_law :=
    FiniteProduct.record_rectangular_probVal 2 (fun _ => Bool)
      (fun _ => twoBoolFairBit)
  mechanism := fun child parents latents =>
    if h : child.val = 0 then
      latents ⟨0, by decide⟩ (by
        simp [chainLatent, h])
    else
      parents chainFirst (by
        have h1 : child.val = 1 := by
          have hlt : child.val < 2 := child.isLt
          omega
        simp [chainSignature, chainFirst, h1])

def chainScale : QualitativeCausalScale chainSignature :=
  inducedCausal chainCopyModel rationalScale

theorem chain_scale_inhabited :
    Nonempty (QualitativeCausalScale.{0} chainSignature) :=
  ⟨chainScale⟩

def secondTrue : Event twoBoolSignature.Assignment :=
  fun a => decide (a twoBoolSecond = true)

theorem secondTrue_depends_only_on_second :
    dependsOnlyOn (NodeSet.singleton twoBoolSecond) secondTrue := by
  intro x y agree
  have h := agree twoBoolSecond (by simp [NodeSet.singleton])
  simp [secondTrue, h]

theorem twoBool_second_not_descendant_of_first :
    descendantsOf twoBoolSignature (NodeSet.singleton twoBoolFirst)
      twoBoolSecond = false := by
  decide +kernel

theorem twoBool_second_is_nonDescendant_of_doFirst :
    nonDescendantsOf twoBoolSignature
      ((HardIntervention.empty twoBoolSignature).set twoBoolFirst false).targets
      twoBoolSecond = true := by
  decide +kernel

/-- Setting the first node does not change a claim that mentions only the
second node. -/
theorem doFirst_leaves_secondTrue :
    sameRatio
      (ofUrnEvent
        (independentScale.slice
          ((HardIntervention.empty twoBoolSignature).set twoBoolFirst false))
        secondTrue)
      (ofUrnEvent
        (independentScale.slice (HardIntervention.empty twoBoolSignature))
        secondTrue) :=
  independentScale.nonDescendantInvariance
    ((HardIntervention.empty twoBoolSignature).set twoBoolFirst false)
    secondTrue (by
      intro x y agree
      have hnd := twoBool_second_is_nonDescendant_of_doFirst
      have h := agree twoBoolSecond hnd
      simp [secondTrue, h])

theorem chain_second_depends_only_on_second :
    dependsOnlyOn (NodeSet.singleton chainSecond)
      (fun a => decide (a chainSecond = true)) := by
  intro x y agree
  have h := agree chainSecond (by simp [NodeSet.singleton])
  simp [h]

theorem chain_first_is_parent :
    chainSignature.directed chainFirst chainSecond = true := by
  decide

/-- Once the parent of the second node is set, idle versus a further idle
extension is not the interesting case; two settings of that parent to the
same value agree on claims about the child. -/
theorem chain_parentModularity_same_parent_value :
    sameRatio
      (ofUrnEvent
        (chainScale.slice
          ((HardIntervention.empty chainSignature).set chainFirst true))
        (fun a => decide (a chainSecond = true)))
      (ofUrnEvent
        (chainScale.slice
          ((HardIntervention.empty chainSignature).set chainFirst true))
        (fun a => decide (a chainSecond = true))) :=
  chainScale.parentModularity chainSecond
    ((HardIntervention.empty chainSignature).set chainFirst true)
    ((HardIntervention.empty chainSignature).set chainFirst true)
    (fun a => decide (a chainSecond = true))
    (fun _parent _edge => rfl)
    (fun parent hedge => by
      have : parent = chainFirst := by
        match hp : parent.val with
        | 0 =>
            exact Fin.eq_of_val_eq hp
        | 1 =>
            have hfalse : chainSignature.directed parent chainSecond = false := by
              have heq : parent = chainSecond :=
                Fin.eq_of_val_eq (by simp [chainSecond, hp])
              subst heq
              decide
            simp [hfalse] at hedge
        | n + 2 =>
            have : parent.val < 2 := parent.isLt
            omega
      subst this
      rw [HardIntervention.set_at_target]
      rfl)
    (by
      have hne : chainSecond ≠ chainFirst := by decide
      simp [HardIntervention.set, HardIntervention.empty,
        FiniteLatentSCM.noIntervention, hne])
    (by
      have hne : chainSecond ≠ chainFirst := by decide
      simp [HardIntervention.set, HardIntervention.empty,
        FiniteLatentSCM.noIntervention, hne])
    chain_second_depends_only_on_second

theorem induced_empty_not_sure :
    ¬ rationalScale.eqv
        (independentScale.plaus (HardIntervention.empty twoBoolSignature)
          bottomEvent)
        (independentScale.plaus (HardIntervention.empty twoBoolSignature)
          topEvent) :=
  induced_not_eqv_bottom_top twoBoolIndependentModel rationalScale
    (HardIntervention.empty twoBoolSignature)

def idleAction : NodeSet twoBoolSignature := NodeSet.empty
def secondOutcome : NodeSet twoBoolSignature :=
  NodeSet.singleton twoBoolSecond
def falseReference : twoBoolSignature.Assignment := fun _ => false

theorem kernelPlausOf_eq_kernelPlaus_idle :
    kernelPlausOf independentScale
        ⟨secondOutcome, idleAction, idleAction⟩ falseReference =
      kernelPlaus rationalScale twoBoolIndependentModel
        ⟨secondOutcome, idleAction, idleAction⟩ falseReference :=
  kernelPlausOf_eq_kernelPlaus rationalScale twoBoolIndependentModel
    ⟨secondOutcome, idleAction, idleAction⟩ falseReference

end QualitativeCausalScale
end Examples
end Causality
end Thesis
