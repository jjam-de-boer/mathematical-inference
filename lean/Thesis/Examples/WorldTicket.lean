import Thesis.CausalTransport.QualitativeDoCalculus
import Thesis.Causality.WorldTicket
import Thesis.Examples.QualitativeDoCalculus

namespace Thesis
namespace Causality
namespace Examples
namespace WorldTicket

open Probability
open Probability.ClaytonWaddington
open Probability.ClaytonWaddington.UrnRatio
open Causality.QualitativeDoCalculus
open Causality.WorldTicket

/-!
Finite checks of world-ticket readings.  These fixtures are not foundations:
the theorems live in `Thesis.Causality.WorldTicket` and `Thesis.Causality.Model`.
Pearl identities used below are the existing qualitative 2a transport.
-/

/-- Pearl's Rule 1 on independent coins, by the existing soundness transport. -/
theorem pearl_via_existing_2a :
    KernelPlausEqv rationalScale
      (kernelPlaus rationalScale twoBoolIndependentModel
        (rule1Left
          Examples.QualitativeDoCalculus.idle
          Examples.QualitativeDoCalculus.y
          Examples.QualitativeDoCalculus.z
          Examples.QualitativeDoCalculus.idle)
        Examples.QualitativeDoCalculus.reference)
      (kernelPlaus rationalScale twoBoolIndependentModel
        (rule1Right
          Examples.QualitativeDoCalculus.idle
          Examples.QualitativeDoCalculus.y
          Examples.QualitativeDoCalculus.z
          Examples.QualitativeDoCalculus.idle)
        Examples.QualitativeDoCalculus.reference) :=
  Examples.QualitativeDoCalculus.rule1_qualitative

theorem independent_private_balls :
    twoBoolIndependentModel.IsMarkovian :=
  twoBoolIndependentModel_markovian

theorem independent_worldPile_product
    (events : (l : Fin twoBoolIndependentModel.latent.count) → Bool → Bool) :
    QProb.Equiv
      (twoBoolIndependentModel.prior.probVal
        (twoBoolIndependentModel.latent.rectangularEvent events))
      (FiniteProduct.qProduct twoBoolIndependentModel.latent.count
        (fun l => (twoBoolIndependentModel.factor l).probVal (events l))) :=
  worldPile_product twoBoolIndependentModel events

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

/-- `U1` prints `X`; the `Y`-machine copies the current `X` writing. -/
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

def chainDoFirst (value : Bool) : HardIntervention chainSignature :=
  (HardIntervention.empty chainSignature).set chainFirst value

/-- Forcing `X` skips the `U1` print. -/
theorem chain_doFirst_skips_U1 (u : chainCopyModel.latent.Assignment)
    (value : Bool) :
    chainCopyModel.evalUnder (chainDoFirst value).value u chainFirst = value :=
  reading_effectiveness chainCopyModel (chainDoFirst value) u chainFirst value
    (HardIntervention.set_at_target _ _ _)

/-- After `do(X)`, `Y` still runs its machine on the current `X` writing. -/
theorem chain_doFirst_still_runs_Y (u : chainCopyModel.latent.Assignment)
    (value : Bool) :
    chainCopyModel.evalUnder (chainDoFirst value).value u chainSecond = value := by
  have hunforced : (chainDoFirst value).value chainSecond = none := by
    have hne : chainSecond ≠ chainFirst := by decide
    simp [chainDoFirst, HardIntervention.set, HardIntervention.empty,
      FiniteLatentSCM.noIntervention, hne]
  have hread :=
    reading_unforced chainCopyModel (chainDoFirst value) u chainSecond hunforced
  change
    chainCopyModel.evalNodeUnder (chainDoFirst value).value u chainSecond = value
  rw [hread]
  have hchild : chainSecond.val ≠ 0 := by decide
  simp [chainCopyModel, hchild]
  exact chain_doFirst_skips_U1 u value

/-- Two nodes, no arrow, one hidden ball fed to both print rules. -/
def sharedSignature : ObservedSignature := twoBoolSignature

def sharedFirst : Fin sharedSignature.count := twoBoolFirst
def sharedSecond : Fin sharedSignature.count := twoBoolSecond

def sharedLatent : LatentExtension sharedSignature where
  count := 1
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by
    intro _ value
    cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun _ _ => true

def sharedModel : ExactModel sharedSignature where
  latent := sharedLatent
  factor := fun _ => twoBoolFairBit
  prior := FiniteProduct.record 1 (fun _ => Bool) (fun _ => twoBoolFairBit)
  product_law :=
    FiniteProduct.record_rectangular_probVal 1 (fun _ => Bool)
      (fun _ => twoBoolFairBit)
  mechanism := fun _ _ latents =>
    latents ⟨0, by decide⟩ (by simp [sharedLatent])

theorem shared_ball_feeds_two :
    SharedBall sharedModel :=
  ⟨⟨0, by decide⟩, sharedFirst, sharedSecond, by decide, by decide, by decide⟩

def sharedDoFirst (value : Bool) : HardIntervention sharedSignature :=
  (HardIntervention.empty sharedSignature).set sharedFirst value

theorem shared_doFirst_skips_first_print (u : sharedModel.latent.Assignment)
    (value : Bool) :
    sharedModel.evalUnder (sharedDoFirst value).value u sharedFirst = value :=
  reading_effectiveness sharedModel (sharedDoFirst value) u sharedFirst value
    (HardIntervention.set_at_target _ _ _)

/-- Doing `X` keeps the hidden ball, so `Y` still copies it. -/
theorem shared_doFirst_second_copies_ball (u : sharedModel.latent.Assignment)
    (value : Bool) :
    sharedModel.evalUnder (sharedDoFirst value).value u sharedSecond =
      u ⟨0, by decide⟩ := by
  have hunforced : (sharedDoFirst value).value sharedSecond = none := by
    have hne : sharedSecond ≠ sharedFirst := by decide
    simp [sharedDoFirst, HardIntervention.set, HardIntervention.empty,
      FiniteLatentSCM.noIntervention, hne]
  have hread :=
    reading_unforced sharedModel (sharedDoFirst value) u sharedSecond hunforced
  change sharedModel.evalUnder (sharedDoFirst value).value u sharedSecond =
    u ⟨0, by decide⟩
  rw [show sharedModel.evalUnder (sharedDoFirst value).value u sharedSecond =
      sharedModel.evalNodeUnder (sharedDoFirst value).value u sharedSecond
      from rfl, hread]
  simp [sharedModel, sharedLatent]

def secondTrue : Event sharedSignature.Assignment :=
  fun a => decide (a sharedSecond = true)

def firstTrue : Event sharedSignature.Assignment :=
  fun a => decide (a sharedFirst = true)

theorem shared_see_firstTrue_positive :
    sharedModel.observationalDist.EventPositive firstTrue := by
  decide +kernel

/-- Seeing `X=true` discards world-tickets with `X=false`, so `Y` is true. -/
theorem shared_see_first_makes_second_sure :
    QProb.Equiv
      ((sharedModel.observationalDist.conditionOn firstTrue
        shared_see_firstTrue_positive).probVal secondTrue)
      QProb.one := by
  decide +kernel

/-- Doing `X=true` does not discard the hidden ball, so `Y` is still fair. -/
theorem shared_do_first_leaves_second_fair :
    QProb.Equiv
      (sharedModel.interventionalValue (sharedDoFirst true).value secondTrue)
      ⟨1, 2, by decide⟩ := by
  decide +kernel

end WorldTicket
end Examples
end Causality
end Thesis
