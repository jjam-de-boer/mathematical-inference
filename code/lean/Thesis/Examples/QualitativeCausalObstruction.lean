import Thesis.Causality.QualitativeCausalScale
import Thesis.Causality.ProbabilityResult

namespace Thesis.Examples.QualitativeCausalObstruction

open Probability Causality
open Probability.ClaytonWaddington Probability.ClaytonWaddington.UrnRatio
open Causality.QualitativeCausalScale Causality.QualitativeDoCalculus

/-!
# Separate experimental urns need not describe one causal game

The old qualitative comparison structure records an urn for each setting.
Its requirements preserve individual free-node marginals, but do not prevent
an intervention from changing the *joint* behavior of two children.

Here the declared graph is the fork A → B, A → C. Observation draws three
independent fair bits. Only the experiment setting A=false, and nothing else,
changes the children to a common fair bit. All other experiments draw every
unset variable independently. Every slice is an ordinary positive-size urn;
the defect is the incompatibility between those experiments.

These urns are deliberately NOT an instance of `CausalUrnGame`: its stable
local recipes and fresh private randomness would prohibit this switch. The
example refutes a proposed converse for the weaker structure, never Pearl's
rules for genuine causal models.
-/

/-- Three recorded Boolean coordinates, ordered A,B,C, with just the fork. -/
def signature : ObservedSignature where
  count := 3
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed parent child := decide (parent.val = 0 ∧ 0 < child.val)
  directed_earlier := by
    intro parent child edge
    have bounds := of_decide_eq_true edge
    omega

def nodeA : Fin signature.count := ⟨0, by decide⟩
def nodeB : Fin signature.count := ⟨1, by decide⟩
def nodeC : Fin signature.count := ⟨2, by decide⟩

def assignment (a b c : Bool) : signature.Assignment :=
  fun node => if node.val = 0 then a else if node.val = 1 then b else c

def intervention (a b c : Option Bool) : HardIntervention signature where
  value node := if node.val = 0 then a else if node.val = 1 then b else c

private theorem assignment_eta (a : signature.Assignment) :
    assignment (a nodeA) (a nodeB) (a nodeC) = a := by
  funext node
  match node with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨n + 3, bound⟩ => change n + 3 < 3 at bound; omega

private theorem intervention_eta (I : HardIntervention signature) :
    intervention (I.value nodeA) (I.value nodeB) (I.value nodeC) = I := by
  apply HardIntervention.extensional
  intro node
  match node with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨n + 3, bound⟩ => change n + 3 < 3 at bound; omega

/- The finite decisions below are explicit truth-table elimination. They do
not add excluded middle for arbitrary propositions or a function-choice axiom.
In particular, all subsequent `decide +kernel` proofs are kernel reductions,
not an unchecked native evaluator or a supplied soundness certificate. -/
private instance optionBoolForall (P : Option Bool → Prop) [DecidablePred P] :
    Decidable (∀ value, P value) :=
  decidable_of_iff (P none ∧ P (some false) ∧ P (some true)) (by
    constructor
    · intro h value
      cases value with
      | none => exact h.1
      | some value => cases value <;> simp_all
    · intro h
      exact ⟨h none, h (some false), h (some true)⟩)

private instance interventionForall (P : HardIntervention signature → Prop) [DecidablePred P] :
    Decidable (∀ I, P I) :=
  decidable_of_iff (∀ a b c : Option Bool, P (intervention a b c)) (by
    constructor
    · intro h I
      simpa only [intervention_eta] using h (I.value nodeA) (I.value nodeB) (I.value nodeC)
    · intro h a b c
      exact h (intervention a b c))

private instance assignmentForall (P : signature.Assignment → Prop) [DecidablePred P] :
    Decidable (∀ a, P a) :=
  decidable_of_iff (∀ a b c : Bool, P (assignment a b c)) (by
    constructor
    · intro h a
      simpa only [assignment_eta] using h (a nodeA) (a nodeB) (a nodeC)
    · intro h a b c
      exact h (assignment a b c))

private instance boolFunctionForall (P : (Bool → Bool) → Prop) [DecidablePred P] :
    Decidable (∀ f, P f) :=
  decidable_of_iff (∀ a b : Bool, P (fun value => if value then b else a)) (by
    constructor
    · intro h f
      have same : (fun value => if value then f true else f false) = f := by
        funext value
        cases value <;> rfl
      simpa only [same] using h (f false) (f true)
    · intro h a b
      exact h (fun value => if value then b else a))

def idle : HardIntervention signature := HardIntervention.empty signature

/-- The three cell bits are genuinely independent under the uniform eight
cells. Overriding a set coordinate does not condition on its original bit. -/
def bit (cell : Fin 8) (node : Fin signature.count) : Bool :=
  decide (cell.val / 2 ^ node.val % 2 = 1)

def exceptional (I : HardIntervention signature) : Bool :=
  decide (I.value nodeA = some false ∧ I.value nodeB = none ∧ I.value nodeC = none)

def read (I : HardIntervention signature) (cell : Fin 8) : signature.Assignment :=
  fun node => match I.value node with
    | some value => value
    | none => if exceptional I && decide (node.val = 2) then bit cell nodeB else bit cell node

def slice (I : HardIntervention signature) : UrnProb signature.Assignment :=
  ⟨8, by decide, read I⟩

def nodeEvent (node : Fin signature.count) (event : Event Bool) : Event signature.Assignment :=
  fun a => event (a node)

private theorem read_effective (I : HardIntervention signature) (node) (value)
    (forced : I.value node = some value) (cell) : read I cell node = value := by
  simp only [read, forced]

/-- Every unset individual coordinate stays fair, even in the exceptional
experiment. This fact is intentionally weaker than joint independence. -/
private theorem unset_node_count : ∀ (I : HardIntervention signature) (node)
    (event : Event Bool), I.value node = none →
    (slice I).probNum (nodeEvent node event) =
      (slice idle).probNum (nodeEvent node event) := by
  decide +kernel

/-- The exceptional action can change descendants jointly; it still leaves
every non-descendant reading unchanged on each cell. -/
private theorem nonDescendant_read : ∀ (I : HardIntervention signature) (cell : Fin 8) (node),
    nonDescendantsOf signature I.targets node = true → read I cell node = read idle cell node := by
  decide +kernel

/-- Compare labels on the same eight cells. This lemma leaves the test
arbitrary: subsequent claims are about ALL events, not selected PMFs. -/
private theorem slice_count_congr (I J : HardIntervention signature)
    (E F : Event signature.Assignment)
    (same : ∀ cell : Fin 8, E (read I cell) = F (read J cell)) :
    (slice I).probNum E = (slice J).probNum F := by
  rw [UrnProb.probNum_eq_cellCount, UrnProb.probNum_eq_cellCount]
  exact count_congr same

private def canonical (node : Fin signature.count) (value : Bool) : signature.Assignment :=
  fun other => if other = node then value else false

private theorem singleton_factor (node : Fin signature.count)
    (E : Event signature.Assignment)
    (depends : dependsOnlyOn (NodeSet.singleton node) E) :
    E = nodeEvent node (fun value => E (canonical node value)) := by
  funext a
  apply depends a (canonical node (a node))
  intro other selected
  have same : other = node := (NodeSet.singleton_eq_true_iff node other).mp selected
  subst other
  simp only [canonical, ↓reduceIte]

/-- An actual inhabitant of the OLD weak requirements. The parent-modularity
proof only needs unchanged single-node marginals. It therefore cannot detect
the intervention-dependent correlation between the two children. -/
def weakScale : QualitativeCausalScale signature where
  urn := rationalScale
  slice := slice
  effectiveness := by
    intro I node value forced
    have same := slice_count_congr I I (fun a => decide (a node = value)) topEvent (by
      intro cell
      simp only [read_effective I node value forced cell, decide_true, topEvent])
    exact congrArg (fun count => count * 8) same
  nonDescendantInvariance := by
    intro I E depends
    have same := slice_count_congr I idle E E (by
      intro cell
      apply depends
      intro node selected
      exact nonDescendant_read I cell node selected)
    exact congrArg (fun count => count * 8) same
  parentModularity := by
    intro child I J E _agree _parentsSet unforcedI unforcedJ depends
    have factored := singleton_factor child E depends
    change (slice I).probNum E * 8 = (slice J).probNum E * 8
    rw [factored, unset_node_count I child _ unforcedI, unset_node_count J child _ unforcedJ]

private def screenLeft (child : Fin signature.count) : Kernel signature :=
  let parents := parentsOf signature child
  let extra := NodeSet.diff (nonDescendantsOf signature (NodeSet.singleton child)) parents
  ⟨NodeSet.singleton child, NodeSet.empty, NodeSet.union extra parents⟩

private def screenRight (child : Fin signature.count) : Kernel signature :=
  ⟨NodeSet.singleton child, NodeSet.empty, parentsOf signature child⟩

/-- This computable predicate compares only conditionals which both exist.
It never equates `none` with a zero rational value. -/
private def agreeWhenSupported (left right : Option QProb) : Prop :=
  match left, right with
  | some first, some second => QProb.Equiv first second
  | _, _ => True

private instance agreeWhenSupported_decidable (left right : Option QProb) :
    Decidable (agreeWhenSupported left right) := by
  cases left <;> cases right <;> simp only [agreeWhenSupported] <;> infer_instance

private def scaleAgreement (Q : QualitativeUrnScale) (left right : Option Q.Plaus) : Prop :=
  match left, right with
  | some first, some second => Q.eqv first second
  | _, _ => True

private theorem scale_agree (Q : QualitativeUrnScale) {left right : Option Q.Plaus}
    (equal : KernelPlausEqv Q left right) : scaleAgreement Q left right := by
  cases equal with
  | unsupported => trivial
  | defined same => exact same

private theorem idle_conditionals : ∀ (child : Fin signature.count) (reference : signature.Assignment),
    agreeWhenSupported
      (weakScale.kernelPlausOf (screenLeft child) reference)
      (weakScale.kernelPlausOf (screenRight child) reference) := by
  decide +kernel

/-- The observational law is fully independent, hence also satisfies the
old extra observational screening-off hypothesis. This still says nothing
about the newly correlated experiment after setting A=false. -/
theorem weakScale_idleScreeningOff : IdleScreeningOff weakScale := by
  intro child reference
  dsimp only
  intro first second left right
  have agreed := idle_conditionals child reference
  change weakScale.kernelPlausOf (screenLeft child) reference = some first at left
  change weakScale.kernelPlausOf (screenRight child) reference = some second at right
  rw [left, right] at agreed
  exact agreed

def setAFalse : HardIntervention signature := intervention (some false) none none

def witness : signature.Assignment := assignment false true true

private def leftValue : QProb := ⟨4, 4, by decide⟩
private def rightValue : QProb := ⟨4, 8, by decide⟩

theorem after_setting_left_supported :
    weakScale.kernelPlausOf
      (rule1Left (NodeSet.singleton nodeA) (NodeSet.singleton nodeB)
        (NodeSet.singleton nodeC) NodeSet.empty) witness = some leftValue := by
  rfl

theorem after_setting_right_supported :
    weakScale.kernelPlausOf
      (rule1Right (NodeSet.singleton nodeA) (NodeSet.singleton nodeB)
        (NodeSet.singleton nodeC) NodeSet.empty) witness = some rightValue := by
  rfl

/-- Both evidence events have positive mass. The disagreement is between
defined values one and one-half, not a comparison involving null evidence. -/
theorem after_setting_values_disagree : ¬ QProb.Equiv leftValue rightValue := by
  decide +kernel

/-- There is no undeclared common cause in the claimed fork. Adding one
would change the graphical premise and would not repair this example on
the stated graph. -/
def graph : ObservedGraph signature where
  bidirected _ _ := false
  bidirected_symmetric := by intro _ _ impossible; cases impossible
  bidirected_irreflexive := by intro _; rfl

theorem rule1_disjoint : FourWayDisjoint
    (NodeSet.singleton nodeA) (NodeSet.singleton nodeB)
    (NodeSet.singleton nodeC) NodeSet.empty := by
  constructor <;> unfold NodeSet.Disjoint <;> decide +kernel

/-- Conditioning on A blocks the sole fork path between B and C. A is a
root, so deleting its incoming arrows does not change that calculation. -/
theorem rule1_separated : graph.dSeparated (.bar (NodeSet.singleton nodeA))
    (NodeSet.singleton nodeB) (NodeSet.singleton nodeC)
    (NodeSet.union (NodeSet.singleton nodeA) NodeSet.empty) = true := by
  decide +kernel

theorem rule1_qualitative_failure : ¬ KernelPlausEqv rationalScale
    (weakScale.kernelPlausOf
      (rule1Left (NodeSet.singleton nodeA) (NodeSet.singleton nodeB)
        (NodeSet.singleton nodeC) NodeSet.empty) witness)
    (weakScale.kernelPlausOf
      (rule1Right (NodeSet.singleton nodeA) (NodeSet.singleton nodeB)
        (NodeSet.singleton nodeC) NodeSet.empty) witness) := by
  rw [after_setting_left_supported, after_setting_right_supported]
  intro equal
  exact after_setting_values_disagree (scale_agree rationalScale equal)

/-- The old proposed transfer from observational screening-off to every
intervention slice is false, even on three Boolean coordinates. -/
theorem not_mutilated_after_setting :
    ¬ MutilatedIdleScreeningOff weakScale setAFalse := by
  intro claimed
  have impossible := claimed nodeB witness leftValue rightValue (by rfl) (by rfl)
  exact after_setting_values_disagree impossible

theorem not_mutilatedMarkovFromAxioms : ¬ MutilatedMarkovFromAxioms := by
  intro claimed
  exact not_mutilated_after_setting
    (claimed weakScale weakScale_idleScreeningOff setAFalse)

end Thesis.Examples.QualitativeCausalObstruction
