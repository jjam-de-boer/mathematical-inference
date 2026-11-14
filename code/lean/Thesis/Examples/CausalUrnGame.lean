import Thesis.Causality.CausalUrnFreshness
import Thesis.Causality.CausalUrnConditioning
import Thesis.Causality.CausalUrnRenaming
import Thesis.CausalTransport.CausalUrnDoCalculus

namespace Thesis.Examples.CausalUrnGame
open Probability Causality
open Probability.ClaytonWaddington

/-!
# Recorded X,Y and an unrecorded common source U

These fixtures are built from finite urn instructions, never from an SCM.
Both basic games draw a fair U and copy it to X. One copies X to Y; the
other copies U to Y. Their recorded observational laws coincide, but setting
X=true forces Y=true only in the copy game. The common-cause game still
draws U and records Y=U, giving probability 1/2.

A third game has an always-false X. Y has two false cells when X=false and
three cells labelled false,true,true when X=true. The latter recipe is
observationally unreachable but must remain defined: setting X=true reaches
it and gives P(Y=true)=2/3. This also tests unequal parent-dependent cell
counts, supported zero conditionals and genuinely undefined conditionals.
-/

def signature (copy : Bool) : ObservedSignature where
  count := 2
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed parent child := copy && decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by cases copy <;> decide +kernel

/-- Full positions are U,X,Y. Only the edge entering Y changes between the
copy and common-cause games. U is always unrecorded and is always executed. -/
def fullGraph (copy : Bool) : FiniteHiddenDAG (signature copy) where
  count := 3
  observedNode node := ⟨node.val + 1, by have bound : node.val < 2 := node.isLt; omega⟩
  observedNode_injective := by cases copy <;> unfold Function.Injective <;> decide +kernel
  hidden node := decide (node.val = 0)
  observed_not_hidden := by cases copy <;> decide +kernel
  node_classified := by cases copy <;> decide +kernel
  edge parent child := decide ((parent.val = 0 ∧ child.val = 1) ∨
    ((if copy then parent.val = 1 else parent.val = 0) ∧ child.val = 2))
  rank := Fin.val
  edge_rank_lt := by cases copy <;> decide +kernel

private theorem projected_arrows (copy : Bool) : ∀ first second : Fin (signature copy).count,
    (signature copy).directed first second =
      ((fullGraph copy).hiddenInternalPath? ((fullGraph copy).observedNode first)
        ((fullGraph copy).observedNode second)).isSome := by cases copy <;> decide +kernel

/-- Compute the latent projection from the actual full wiring. The shared
hidden source produces a bidirected edge in the common-cause game. -/
def projection (copy : Bool) : FiniteLatentProjection (signature copy) :=
  (fullGraph copy).computedLatentProjection (by
    intro first second
    change (signature copy).directed first second = true ↔ _
    rw [projected_arrows]
    exact (fullGraph copy).hiddenInternalPath?_iff _ _)

def fair : UrnProb Bool := ⟨2, by decide, fun cell => decide (cell.val = 1)⟩
def certain (value : Bool) : UrnProb Bool := ⟨1, by decide, fun _ => value⟩

def game (copy : Bool) : Causality.CausalUrnGame (signature copy) (projection copy) where
  Value _ := Bool
  values _ := [false, true]
  complete := by intro _ value; cases value <;> simp
  valueEq _ := inferInstance
  defaultValue _ := false
  recordedValue _ := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  contents child parents :=
    if atU : child.val = 0 then fair
    else if atX : child.val = 1 then
      certain (parents (0 : Fin 3) (by change (fullGraph copy).edge _ child = true; simp [fullGraph, atX]))
    else
      have atY : child.val = 2 := by have bound : child.val < 3 := child.isLt; omega
      if isCopy : copy = true then
        certain (parents (1 : Fin 3) (by change (fullGraph copy).edge _ child = true; simp [fullGraph, atY, isCopy]))
      else
        certain (parents (0 : Fin 3) (by
          change (fullGraph copy).edge _ child = true
          cases copy <;> simp_all [fullGraph]))

def copyGame := game true
def commonCauseGame := game false
def idle (copy : Bool) := HardIntervention.empty (signature copy)
def setX (copy : Bool) := (idle copy).set (0 : Fin 2) true
def state (x y : Bool) : (signature true).Assignment := fun node => if node.val = 0 then x else y
def yTrue : Event (signature true).Assignment := fun record => record (1 : Fin 2)
def xTrue : Event (signature true).Assignment := fun record => record (0 : Fin 2)

private theorem state_eta (record : (signature true).Assignment) :
    record = state (record (0 : Fin 2)) (record (1 : Fin 2)) := by
  funext node
  have bound : node.val < 2 := node.isLt
  by_cases zero : node.val = 0
  · have same : node = (0 : Fin 2) := Fin.ext zero
    subst node; rfl
  · have same : node = (1 : Fin 2) := Fin.ext (by change node.val = 1; omega)
    subst node; rfl

private theorem observed_cells : ∀ x y : Bool, QProb.Equiv
    ((copyGame.law (idle true)).probVal (FiniteProbRecord.singletonEvent (state x y)))
    ((commonCauseGame.law (idle false)).probVal (FiniteProbRecord.singletonEvent (state x y))) := by decide +kernel

/-- Agreement holds on EVERY recorded event, not just separate X and Y
marginals. Consequently the observational scorecard cannot select the game. -/
theorem observational_laws_agree (event : Event (signature true).Assignment) :
    QProb.Equiv ((copyGame.law (idle true)).probVal event)
      ((commonCauseGame.law (idle false)).probVal event) := by
  apply FiniteProbRecord.probVal_extensional_of_singletons _ _ (signature true).assignmentEnumeration
    (signature true).assignmentEnumeration_nodup (signature true).assignmentEnumeration_complete
  intro record
  rw [state_eta record]
  exact observed_cells _ _

theorem copy_setting_effect : QProb.Equiv ((copyGame.law (setX true)).probVal yTrue) QProb.one := by decide +kernel

theorem common_cause_setting_effect :
    QProb.Equiv ((commonCauseGame.law (setX false)).probVal yTrue) ⟨1, 2, by decide⟩ := by decide +kernel

/-- These are graph facts from the explicitly unrecorded U, not probability
decorations attached after observing the joint table. -/
theorem projected_common_cause :
    (projection false).observedGraph.bidirected (0 : Fin 2) (1 : Fin 2) = true ∧
    (projection true).observedGraph.bidirected (0 : Fin 2) (1 : Fin 2) = false := by decide +kernel

/-- All recipes are supplied, including the three-cell recipe behind the
observationally impossible X=true parent tuple. U's unused declared input
is harmless and does not add a faithfulness assumption to the game. -/
def variableContents (child : Fin 3) (parents : (game true).Parents child) : UrnProb Bool :=
  if atY : child.val = 2 then
    let x : Bool := parents (1 : Fin 3) (by change (fullGraph true).edge _ child = true; simp [fullGraph, atY])
    if x then ⟨3, by decide, fun cell => decide (0 < cell.val)⟩
    else ⟨2, by decide, fun _ => false⟩
  else certain false

def variableGame : Causality.CausalUrnGame (signature true) (projection true) :=
  { (game true) with contents := variableContents }

theorem unequal_recipe_sizes : ∀ (parents : variableGame.Parents (2 : Fin 3)),
    (variableGame.contents (2 : Fin 3) parents).n =
      if (parents (1 : Fin 3) (by decide +kernel)) = true then 3 else 2 := by
  intro parents
  by_cases x : parents (1 : Fin 3) (by decide +kernel) = true <;>
    simp [variableGame, variableContents, x]

theorem observational_action_impossible : ((variableGame.law (idle true)).probVal xTrue).num = 0 := by decide +kernel

theorem intervention_reaches_new_recipe :
    QProb.Equiv ((variableGame.law (setX true)).probVal xTrue) QProb.one ∧
    QProb.Equiv ((variableGame.law (setX true)).probVal yTrue) ⟨2, 3, by decide⟩ := by decide +kernel

theorem null_condition_is_undefined : variableGame.conditional (idle true) yTrue xTrue = none := by decide +kernel

/-- The denominator is one here and the outcome is zero. The conditional is
supported, and the general zero theorem preserves that distinction. -/
def supported_zero_conditional : ProbabilityResult.Equivalent
    (variableGame.conditional (idle true) yTrue topEvent) (some QProb.zero) :=
  variableGame.conditional_zero (idle true) yTrue topEvent (by decide +kernel) (by decide +kernel)

private def support (result : ProbabilityResult.Result) (defined : result.isSome = true) :
    ProbabilityResult.Supported result := by
  cases result with
  | none => cases defined
  | some value => exact ⟨value, .value (QProb.equiv_refl _)⟩

/-- Instantiate a genuinely causal action/observation exchange for the copy
game. Graph separation and support are checked from the game, while the
qualitative equality holds for EVERY Clayton scale. No SCM is supplied. -/
theorem copy_rule2 (scale : QualitativeUrnScale) :
    QualitativeDoCalculus.KernelPlausEqv scale
      (copyGame.kernelPlaus scale
        (rule2Left NodeSet.empty (NodeSet.singleton (1 : Fin 2)) (NodeSet.singleton (0 : Fin 2)) NodeSet.empty) (state true true))
      (copyGame.kernelPlaus scale
        (rule2Right NodeSet.empty (NodeSet.singleton (1 : Fin 2)) (NodeSet.singleton (0 : Fin 2)) NodeSet.empty) (state true true)) := by
  apply copyGame.qualitative_rule2 scale NodeSet.empty
    (NodeSet.singleton (1 : Fin 2)) (NodeSet.singleton (0 : Fin 2)) NodeSet.empty (state true true)
  · exact FourWayDisjoint.emptyAction _ _ NodeSet.empty
      (NodeSet.disjoint_singletons_of_ne (S := signature true)
        (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by
          intro equal
          have impossible : (1 : Nat) = 0 := congrArg Fin.val equal
          cases impossible))
      (NodeSet.disjoint_empty_right _) (NodeSet.disjoint_empty_right _)
  · decide +kernel
  · exact support _ (by decide +kernel)
  · exact support _ (by decide +kernel)

end Thesis.Examples.CausalUrnGame
