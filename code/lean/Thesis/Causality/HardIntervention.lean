import Thesis.Causality.Semantics

namespace Thesis
namespace Causality

open Probability

/-!
Hard interventions and the exact-model alias used by structural execution.

These definitions live in the intrinsic causal development so model and
intervention code does not depend on the external completeness interfaces.
-/

/-- The correspondence keeps observed and latent finite values in one universe. -/
abbrev ExactModel.{u} (S : ObservedSignature.{u}) :=
  FiniteLatentSCM.{u, u} S

/-- A hard intervention on a dependently typed observed signature. -/
structure HardIntervention (S : ObservedSignature) where
  value : (i : Fin S.count) -> Option (S.Value i)

namespace HardIntervention

theorem extensional {I J : HardIntervention S}
    (equal : forall node, I.value node = J.value node) : I = J := by
  cases I with
  | mk left =>
      cases J with
      | mk right =>
          congr
          funext node
          exact equal node

def targets (I : HardIntervention S) : NodeSet S :=
  fun i => (I.value i).isSome

def empty (S : ObservedSignature) : HardIntervention S where
  value := FiniteLatentSCM.noIntervention S

def set (I : HardIntervention S) (target : Fin S.count)
    (value : S.Value target) : HardIntervention S where
  value := fun i =>
    if h : i = target then some (h.symm ▸ value) else I.value i

def unset (I : HardIntervention S) (target : Fin S.count) :
    HardIntervention S where
  value := fun i => if i = target then none else I.value i

theorem set_at_target (I : HardIntervention S) (target : Fin S.count)
    (value : S.Value target) :
    (I.set target value).value target = some value := by
  simp [set]

theorem set_away_from_target (I : HardIntervention S)
    (target i : Fin S.count) (value : S.Value target) (h : i ≠ target) :
    (I.set target value).value i = I.value i := by
  simp [set, h]

theorem unset_at_target (I : HardIntervention S) (target : Fin S.count) :
    (I.unset target).value target = none := by
  simp [unset]

def referenceFor (I : HardIntervention S) (assignment : S.Assignment) :
    S.Assignment :=
  fun i => match I.value i with
    | some value => value
    | none => assignment i

theorem intervention_referenceFor (I : HardIntervention S)
    (outcome condition : NodeSet S) (assignment : S.Assignment) :
    (Kernel.mk outcome I.targets condition).intervention
        (I.referenceFor assignment) = I.value := by
  funext i
  cases hValue : I.value i with
  | none => simp [Kernel.intervention, targets, hValue]
  | some value => simp [Kernel.intervention, targets, referenceFor, hValue]

theorem referenceFor_eq_of_target_false (I : HardIntervention S)
    (assignment : S.Assignment) (i : Fin S.count)
    (notTarget : I.targets i = false) :
    I.referenceFor assignment i = assignment i := by
  cases hValue : I.value i with
  | none => simp [referenceFor, hValue]
  | some value => simp [targets, hValue] at notTarget

end HardIntervention

end Causality
end Thesis
