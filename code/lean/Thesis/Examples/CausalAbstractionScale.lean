import Thesis.Examples.CausalAbstractionExtension

namespace Thesis.Examples.CausalAbstraction
open Probability Causality

/-! Three discrete grains, indexed by an input depth cap. These are finite
SCMs and partial intervention maps, not a physical length or RG flow. -/

def terminalSignature : ObservedSignature where
  count := 1
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed _ _ := false
  directed_earlier := by decide +kernel

def terminalLatent : LatentExtension terminalSignature where
  count := 1
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq _ := inferInstance
  incident _ _ := true

def terminalModel : ExactModel terminalSignature where
  latent := terminalLatent
  factor _ := andMacro.factor (0 : Fin 1)
  prior := FiniteProduct.record 1 (fun _ => Bool) (fun _ => andMacro.factor (0 : Fin 1))
  product_law := FiniteProduct.record_rectangular_probVal _ _ _
  mechanism _ _ inputs := inputs (0 : Fin 1) rfl

def terminalAction (value : Option Bool) : HardIntervention terminalSignature where
  value _ := value

def terminalState (value : Bool) : terminalSignature.Assignment := fun _ => value

theorem terminalState_eta (state : terminalSignature.Assignment) : state = terminalState (state (0 : Fin 1)) := by
  funext node
  have bound : node.val < 1 := node.isLt
  have equal : node = (0 : Fin 1) := Fin.ext (by change node.val = 0; omega)
  subst node; rfl

def collapseAssignment (state : macroSignature.Assignment) : terminalSignature.Assignment :=
  terminalState (state (0 : Fin 2) && state (1 : Fin 2))

def collapseOmega (intervention : HardIntervention macroSignature) : Option (HardIntervention terminalSignature) :=
  match intervention.value (0 : Fin 2), intervention.value (1 : Fin 2) with
  | none, none => some (terminalAction none)
  | some true, some true => some (terminalAction (some true))
  | _, _ => none

private theorem collapse_fibre_finite (first second : Option Bool) (action)
    (defined : collapseOmega (coarseAction first second) = some action) :
    (coarseAction first second = coarseAction none none ∧ action = terminalAction none) ∨
    (coarseAction first second = coarseAction (some true) (some true) ∧ action = terminalAction (some true)) := by
  cases first with
  | none =>
    cases second with
    | none => exact Or.inl ⟨rfl, (Option.some.inj defined).symm⟩
    | some value => cases value <;> cases defined
  | some value =>
    cases value with
    | false => cases second <;> cases defined
    | true =>
      cases second with
      | none => cases defined
      | some value =>
        cases value with
        | false => cases defined
        | true => exact Or.inr ⟨rfl, (Option.some.inj defined).symm⟩

theorem collapse_fibre (intervention action) (defined : collapseOmega intervention = some action) :
    (intervention = coarseAction none none ∧ action = terminalAction none) ∨
    (intervention = coarseAction (some true) (some true) ∧ action = terminalAction (some true)) := by
  have canonical := coarseAction_eta intervention
  rw [canonical] at defined ⊢
  exact collapse_fibre_finite _ _ _ defined

def collapseInterventionMap : CausalInterventionMap macroSignature terminalSignature where
  microModel := andMacro
  macroModel := terminalModel
  assignmentMap := collapseAssignment
  omega := collapseOmega
  respects := by
    intro intervention action defined state realizes
    rcases collapse_fibre intervention action defined with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro node value forced; cases forced
    · intro node value forced
      have selected : true = value := Option.some.inj forced
      have first : state (0 : Fin 2) = true := realizes (0 : Fin 2) true rfl
      have second : state (1 : Fin 2) = true := realizes (1 : Fin 2) true rfl
      change (state (0 : Fin 2) && state (1 : Fin 2)) = value
      rw [first, second, ← selected]
      rfl

private theorem collapse_cells : ∀ forced x : Bool,
    QProb.Equiv
      ((terminalModel.interventionalDist (terminalAction (if forced then some true else none)).value).probVal
        (FiniteProbRecord.singletonEvent (terminalState x)))
      (((andMacro.interventionalDist (coarseAction (if forced then some true else none)
        (if forced then some true else none)).value).map collapseAssignment).probVal
        (FiniteProbRecord.singletonEvent (terminalState x))) := by decide +kernel

theorem collapse_intervention_exact : collapseInterventionMap.Exact := by
  intro intervention action defined event
  have singletonAgreement : ∀ state, QProb.Equiv
      ((terminalModel.interventionalDist action.value).probVal (FiniteProbRecord.singletonEvent state))
      (((andMacro.interventionalDist intervention.value).map collapseAssignment).probVal (FiniteProbRecord.singletonEvent state)) := by
    intro state
    rw [terminalState_eta state]
    rcases collapse_fibre intervention action defined with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact collapse_cells false _
    · exact collapse_cells true _
  exact QProb.equiv_trans
    (FiniteProbRecord.probVal_extensional_of_singletons _ _ terminalSignature.assignmentEnumeration
      terminalSignature.assignmentEnumeration_nodup terminalSignature.assignmentEnumeration_complete singletonAgreement event)
    (FiniteProbRecord.map_probVal _ _ _)

/-- The second step merges both remaining observed coordinates into one. -/
def collapsedCoarsening : FiniteCausalCoarseGraining macroSignature terminalSignature where
  microModel := andMacro
  macroModel := terminalModel
  cluster _ _ := true
  cluster_nonempty _ := ⟨(0 : Fin 2), rfl⟩
  cluster_disjoint := by
    intro first second distinct
    have equal : first = second := Fin.ext (by have f : first.val < 1 := first.isLt; have s : second.val < 1 := second.isLt; change first.val = second.val; omega)
    exact False.elim (distinct equal)
  assignmentMap := collapseAssignment
  coordinate_local := by
    intro node first second agree
    change (first (0 : Fin 2) && first (1 : Fin 2)) = (second (0 : Fin 2) && second (1 : Fin 2))
    rw [agree (0 : Fin 2) rfl, agree (1 : Fin 2) rfl]
  admissible action := action = terminalAction none ∨ action = terminalAction (some true)
  representative action _ := coarseAction (action.value (0 : Fin 1)) (action.value (0 : Fin 1))
  representative_respects := by
    intro action admitted state realizes
    rcases admitted with rfl | rfl
    · intro node value forced; cases forced
    · intro node value forced
      have selected : true = value := Option.some.inj forced
      have first : state (0 : Fin 2) = true := realizes (0 : Fin 2) true rfl
      have second : state (1 : Fin 2) = true := realizes (1 : Fin 2) true rfl
      change (state (0 : Fin 2) && state (1 : Fin 2)) = value
      rw [first, second, ← selected]
      rfl

theorem collapsed_section : collapseInterventionMap.IsSection
    collapsedCoarsening.admissible collapsedCoarsening.representative := by
  intro action admitted
  rcases admitted with rfl | rfl <;> rfl

theorem collapsed_preservesAt (action) (admitted : collapsedCoarsening.admissible action) :
    collapsedCoarsening.PreservesAt action admitted :=
  collapsedCoarsening.preservesAt_of_section collapseInterventionMap rfl rfl rfl
    collapsed_section collapse_intervention_exact action admitted

/-- A nontrivial chain of two exact steps: three observed coordinates,
then two, then one. The theorem applies precisely where both ω maps succeed. -/
def twoStepMap : CausalInterventionMap microSignature terminalSignature :=
  andInterventionMap.comp collapseInterventionMap rfl

theorem scale_composition_preserves : twoStepMap.Exact :=
  CausalInterventionMap.comp_exact _ _ rfl and_intervention_exact collapse_intervention_exact

theorem chain_domain : ∀ first second response : Option Bool,
    twoStepMap.omega (fineAction first second response) =
      match first, second, response with
      | none, none, none => some (terminalAction none)
      | some true, some true, some true => some (terminalAction (some true))
      | _, _, _ => none := by
  intro first second response
  cases first with
  | none => cases second with
    | none => cases response with
      | none => rfl
      | some value => cases value <;> rfl
    | some value => cases value <;> rfl
  | some value => cases value with
    | false => cases second <;> rfl
    | true => cases second with
      | none => rfl
      | some value => cases value with
        | false => rfl
        | true => cases response with
          | none => rfl
          | some value => cases value <;> rfl

inductive Grain where
  | fine | merged | collapsed
  deriving DecidableEq

def Grain.signature : Grain → ObservedSignature
  | .fine => microSignature
  | .merged => macroSignature
  | .collapsed => terminalSignature

def Grain.model : (grain : Grain) → ExactModel grain.signature
  | .fine => microModel
  | .merged => andMacro
  | .collapsed => terminalModel

def Grain.complexity (grain : Grain) : Nat := grain.signature.count

/-- The induced blocks at every grain, expressed in the original micro
coordinates. The finest blocks are singletons, not already merged pairs. -/
def Grain.microCluster : (grain : Grain) → Fin grain.signature.count → NodeSet microSignature
  | .fine => NodeSet.singleton
  | .merged => clusters
  | .collapsed => fun _ _ => true

/-- The depth cap is supplied by the caller; at most three discrete grains. -/
def scaleFamily (depthCap : Nat) : List Grain :=
  [Grain.fine, Grain.merged, Grain.collapsed].take (depthCap + 1)

theorem scale_depth_zero : scaleFamily 0 = [.fine] := rfl

theorem scale_depth_one : scaleFamily 1 = [.fine, .merged] := rfl

theorem scale_depth_two : scaleFamily 2 = [.fine, .merged, .collapsed] := rfl

theorem scale_saturates (depthCap : Nat) : scaleFamily (depthCap + 2) = [.fine, .merged, .collapsed] := by
  simp [scaleFamily, List.take]

/-- At depth zero the two causes are distinct; depth one places exactly
those two causes in the same block. At depth two both macro nodes merge. -/
theorem scale_merge_blocks :
    (0 : Fin 3) ≠ (1 : Fin 3) ∧
    clusters (0 : Fin 2) (0 : Fin 3) = true ∧ clusters (0 : Fin 2) (1 : Fin 3) = true ∧
    clusters (0 : Fin 2) (2 : Fin 3) = false ∧
    collapsedCoarsening.cluster (0 : Fin 1) (0 : Fin 2) = true ∧
    collapsedCoarsening.cluster (0 : Fin 1) (1 : Fin 2) = true := by decide +kernel

theorem scale_blocks_at_depths :
    Grain.fine.microCluster (0 : Fin 3) (1 : Fin 3) = false ∧
    Grain.merged.microCluster (0 : Fin 2) (0 : Fin 3) = true ∧
    Grain.merged.microCluster (0 : Fin 2) (1 : Fin 3) = true ∧
    Grain.merged.microCluster (0 : Fin 2) (2 : Fin 3) = false ∧
    (∀ node : Fin 3, Grain.collapsed.microCluster (0 : Fin 1) node = true) := by decide +kernel

end Thesis.Examples.CausalAbstraction
