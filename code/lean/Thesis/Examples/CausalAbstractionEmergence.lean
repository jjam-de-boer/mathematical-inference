import Thesis.Examples.CausalAbstractionExtension

namespace Thesis.Examples.CausalAbstraction
open Probability Causality

/-! A coarse-only coordinate E is constructed as X_M ∧ Y. There is no
fine node E and no micro hard intervention representing do(E). The added
node is a finite derived observable, not a claim about gravitational physics. -/

def emergentSignature : ObservedSignature where
  count := 3
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed parent child := decide (parent.val < child.val)
  directed_earlier := by intro _ _ edge; exact of_decide_eq_true edge

def emergentLatent : LatentExtension emergentSignature where
  count := 1
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq _ := inferInstance
  incident _ child := decide (child.val = 0)

def emergentModel : ExactModel emergentSignature where
  latent := emergentLatent
  factor _ := andMacro.factor (0 : Fin 1)
  prior := FiniteProduct.record 1 (fun _ => Bool) (fun _ => andMacro.factor (0 : Fin 1))
  product_law := FiniteProduct.record_rectangular_probVal _ _ _
  mechanism child parents inputs :=
    if root : child.val = 0 then inputs (0 : Fin 1) (by simp [emergentLatent, root])
    else if response : child.val = 1 then parents (0 : Fin 3) (by simp [emergentSignature, response])
    else
      have atEmergent : child.val = 2 := by have bound : child.val < 3 := child.isLt; omega
      (parents (0 : Fin 3) (by simp [emergentSignature, atEmergent])) &&
        (parents (1 : Fin 3) (by simp [emergentSignature, atEmergent]))

def appendEmergent (state : macroSignature.Assignment) : emergentSignature.Assignment :=
  fun node => if node.val = 0 then state (0 : Fin 2)
    else if node.val = 1 then state (1 : Fin 2)
    else state (0 : Fin 2) && state (1 : Fin 2)

def emergentOrigin (node : Fin emergentSignature.count) : Option (NodeSet macroSignature) :=
  if node.val = 0 then some (NodeSet.singleton (0 : Fin 2))
  else if node.val = 1 then some (NodeSet.singleton (1 : Fin 2)) else none

private theorem emergent_node_cases (node : Fin emergentSignature.count) :
    node = (0 : Fin 3) ∨ node = (1 : Fin 3) ∨ node = (2 : Fin 3) := by
  have bound : node.val < 3 := node.isLt
  by_cases zero : node.val = 0
  · exact Or.inl (Fin.ext zero)
  · by_cases one : node.val = 1
    · exact Or.inr (Or.inl (Fin.ext one))
    · exact Or.inr (Or.inr (Fin.ext (by change node.val = 2; omega)))

/-- `none` in origin is genuinely a new coordinate, not an empty block
smuggled into the nonempty-cluster merge constructor. -/
def emergentCoarsening : EmergentCausalCoarseGraining macroSignature emergentSignature where
  microModel := andMacro
  macroModel := emergentModel
  origin := emergentOrigin
  has_emergent := ⟨(2 : Fin 3), rfl⟩
  merged_nonempty := by
    intro node members origin
    rcases emergent_node_cases node with rfl | rfl | rfl
    · cases Option.some.inj origin; exact ⟨(0 : Fin 2), by decide +kernel⟩
    · cases Option.some.inj origin; exact ⟨(1 : Fin 2), by decide +kernel⟩
    · cases origin
  merged_disjoint := by
    intro first second left right distinct firstOrigin secondOrigin
    rcases emergent_node_cases first with rfl | rfl | rfl <;>
      rcases emergent_node_cases second with rfl | rfl | rfl
    all_goals solve
      | exact False.elim (distinct rfl)
      | cases firstOrigin
      | cases secondOrigin
      | cases Option.some.inj firstOrigin; cases Option.some.inj secondOrigin; unfold NodeSet.Disjoint; decide +kernel
  assignmentMap := appendEmergent
  merged_local := by
    intro node members origin first second agree
    rcases emergent_node_cases node with rfl | rfl | rfl
    · cases Option.some.inj origin
      exact agree (0 : Fin 2) (by decide +kernel)
    · cases Option.some.inj origin
      exact agree (1 : Fin 2) (by decide +kernel)
    · cases origin

def emergentZoom : FiniteCausalZoom macroSignature emergentSignature :=
  .emergent emergentCoarsening

/-- Lift the original surgeries while leaving E's new equation in place.
No surgery on E is in the image of this map. -/
def emergentLift (intervention : HardIntervention macroSignature) : HardIntervention emergentSignature where
  value node := if node.val = 0 then intervention.value (0 : Fin 2)
    else if node.val = 1 then intervention.value (1 : Fin 2) else none

def emergentInterventionMap : CausalInterventionMap macroSignature emergentSignature where
  microModel := andMacro
  macroModel := emergentModel
  assignmentMap := appendEmergent
  omega intervention := some (emergentLift intervention)
  respects := by
    intro intervention action defined state realizes
    cases Option.some.inj defined
    intro node value forced
    rcases emergent_node_cases node with rfl | rfl | rfl
    · exact realizes (0 : Fin 2) value forced
    · exact realizes (1 : Fin 2) value forced
    · cases forced

private theorem optionBool_cases (value : Option Bool) :
    value = none ∨ value = some false ∨ value = some true := by
  cases value with
  | none => exact Or.inl rfl
  | some value => cases value with
    | false => exact Or.inr (Or.inl rfl)
    | true => exact Or.inr (Or.inr rfl)

private theorem emergent_cells : ∀ (cause response : Option Bool) (x y z : Bool),
    QProb.Equiv
      ((emergentModel.interventionalDist (emergentLift (coarseAction cause response)).value).probVal
        (FiniteProbRecord.singletonEvent (fineState x y z)))
      (((andMacro.interventionalDist (coarseAction cause response).value).map appendEmergent).probVal
        (FiniteProbRecord.singletonEvent (fineState x y z))) := by
  intro cause response
  rcases optionBool_cases cause with rfl | rfl | rfl <;>
    rcases optionBool_cases response with rfl | rfl | rfl <;> decide +kernel

/-- Adding the derived coordinate preserves every original surgery's full
law, while hard interventions on the new coordinate remain outside the image. -/
theorem emergent_intervention_exact : emergentInterventionMap.Exact := by
  intro intervention action defined event
  cases Option.some.inj defined
  have singletons : ∀ state, QProb.Equiv
      ((emergentModel.interventionalDist (emergentLift intervention).value).probVal (FiniteProbRecord.singletonEvent state))
      (((andMacro.interventionalDist intervention.value).map appendEmergent).probVal (FiniteProbRecord.singletonEvent state)) := by
    intro state
    have stateEq : state = fineState (state (0 : Fin 3)) (state (1 : Fin 3)) (state (2 : Fin 3)) := fineState_eta state
    rw [coarseAction_eta intervention, stateEq]
    exact emergent_cells _ _ _ _ _
  exact QProb.equiv_trans
    (FiniteProbRecord.probVal_extensional_of_singletons _ _ emergentSignature.assignmentEnumeration
      emergentSignature.assignmentEnumeration_nodup emergentSignature.assignmentEnumeration_complete singletons event)
    (FiniteProbRecord.map_probVal _ _ _)

/-- A hard do on the new node overrides its equation in the coarse SCM.
It has no micro do, because no fine observed node has that coordinate. -/
def doEmergentTrue : HardIntervention emergentSignature :=
  (HardIntervention.empty emergentSignature).set (2 : Fin 3) true

theorem emergent_do_has_no_micro_representative (intervention : HardIntervention macroSignature) :
    emergentInterventionMap.omega intervention ≠ some doEmergentTrue := by
  intro equal
  have actions := Option.some.inj equal
  have atNew := congrArg (fun action : HardIntervention emergentSignature => action.value (2 : Fin 3)) actions
  cases atNew

theorem emergent_do_meaning : QProb.Equiv
    (emergentModel.interventionalValue doEmergentTrue.value (fun state => state (2 : Fin 3))) QProb.one := by
  decide +kernel

theorem emergence_changes_signature : macroSignature.count = 2 ∧ emergentSignature.count = 3 ∧
    emergentCoarsening.origin (2 : Fin 3) = none := by decide +kernel

end Thesis.Examples.CausalAbstraction
