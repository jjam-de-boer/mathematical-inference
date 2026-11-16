import Thesis.Examples.QualitativeCausalObstruction

namespace Thesis.Examples.QualitativeExperimentalDrift

open Probability Causality
open Probability.ClaytonWaddington Probability.ClaytonWaddington.UrnRatio
open Causality.QualitativeCausalScale Causality.QualitativeDoCalculus

/-!
# Local screening inside each experiment does not imply stability

The declared graph is A → B. Observation draws independent fair bits, but
setting A=a changes the unforced child to the constant a. Setting B leaves
A fair. Thus every experiment is locally compatible with its intervened DAG,
and all old weak requirements hold. Nevertheless observing A=false gives
P(B=true)=1/2, whereas setting A=false gives the supported value zero.

The defect is experimental drift: B's instructions change when its parent
was *set*, rather than merely having the same parent value. The new abstract
characterization must exclude that distinction through cross-experiment
stability. This is not a valid instance of the stable operational urn game.
-/

def signature : ObservedSignature where
  count := 2
  Value _ := Bool
  valueEnumeration _ := [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue _ := false
  valueDecidableEq _ := inferInstance
  directed parent child := decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by
    intro parent child edge
    have bounds := of_decide_eq_true edge
    omega

def nodeA : Fin signature.count := ⟨0, by decide⟩
def nodeB : Fin signature.count := ⟨1, by decide⟩

def assignment (a b : Bool) : signature.Assignment :=
  fun node => if node.val = 0 then a else b

def intervention (a b : Option Bool) : HardIntervention signature where
  value node := if node.val = 0 then a else b

private theorem assignment_eta (a : signature.Assignment) :
    assignment (a nodeA) (a nodeB) = a := by
  funext node
  match node with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨n + 2, bound⟩ => change n + 2 < 2 at bound; omega

private theorem intervention_eta (I : HardIntervention signature) :
    intervention (I.value nodeA) (I.value nodeB) = I := by
  apply HardIntervention.extensional
  intro node
  match node with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨n + 2, bound⟩ => change n + 2 < 2 at bound; omega

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
  decidable_of_iff (∀ a b : Option Bool, P (intervention a b)) (by
    constructor
    · intro h I
      simpa only [intervention_eta] using h (I.value nodeA) (I.value nodeB)
    · intro h a b
      exact h (intervention a b))

private instance assignmentForall (P : signature.Assignment → Prop) [DecidablePred P] :
    Decidable (∀ a, P a) :=
  decidable_of_iff (∀ a b : Bool, P (assignment a b)) (by
    constructor
    · intro h a
      simpa only [assignment_eta] using h (a nodeA) (a nodeB)
    · intro h a b
      exact h (assignment a b))

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

def bit (cell : Fin 4) (node : Fin signature.count) : Bool :=
  decide (cell.val / 2 ^ node.val % 2 = 1)

def read (I : HardIntervention signature) (cell : Fin 4) : signature.Assignment :=
  fun node => match I.value node with
    | some value => value
    | none => if node.val = 1 then (I.value nodeA).getD (bit cell node) else bit cell node

def slice (I : HardIntervention signature) : UrnProb signature.Assignment :=
  ⟨4, by decide, read I⟩

def nodeEvent (node : Fin signature.count) (event : Event Bool) : Event signature.Assignment :=
  fun a => event (a node)

private theorem read_effective (I : HardIntervention signature) (node) (value)
    (forced : I.value node = some value) (cell) : read I cell node = value := by
  simp only [read, forced]

private theorem nonDescendant_read : ∀ (I : HardIntervention signature) (cell : Fin 4) (node),
    nonDescendantsOf signature I.targets node = true → read I cell node = read idle cell node := by
  decide +kernel

/-- Once the parent is explicitly set in both experiments, all old
single-child modularity tests agree. They never compare that row to ordinary
observation of the same parent value, which is the missing requirement. -/
private theorem parent_node_count : ∀ (I J : HardIntervention signature) (child)
    (event : Event Bool),
    (∀ parent, signature.directed parent child = true → I.value parent = J.value parent) →
    (∀ parent, signature.directed parent child = true → (I.value parent).isSome = true) →
    I.value child = none → J.value child = none →
    (slice I).probNum (nodeEvent child event) = (slice J).probNum (nodeEvent child event) := by
  decide +kernel

private theorem slice_count_congr (I J : HardIntervention signature)
    (E F : Event signature.Assignment)
    (same : ∀ cell : Fin 4, E (read I cell) = F (read J cell)) :
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

def weakScale : QualitativeCausalScale signature where
  urn := rationalScale
  slice := slice
  effectiveness := by
    intro I node value forced
    have same := slice_count_congr I I (fun a => decide (a node = value)) topEvent (by
      intro cell
      simp only [read_effective I node value forced cell, decide_true, topEvent])
    exact congrArg (fun count => count * 4) same
  nonDescendantInvariance := by
    intro I E depends
    have same := slice_count_congr I idle E E (by
      intro cell
      apply depends
      intro node selected
      exact nonDescendant_read I cell node selected)
    exact congrArg (fun count => count * 4) same
  parentModularity := by
    intro child I J E agree parentsSet unforcedI unforcedJ depends
    have factored := singleton_factor child E depends
    change (slice I).probNum E * 4 = (slice J).probNum E * 4
    rw [factored, parent_node_count I J child _ agree parentsSet unforcedI unforcedJ]

private def markovLeft (I : HardIntervention signature) (child : Fin signature.count) : Kernel signature :=
  let parents := fun parent => mutilatedDirected signature I.targets parent child
  let extra := NodeSet.diff (nonDescendantsOf signature (NodeSet.singleton child)) parents
  ⟨NodeSet.singleton child, I.targets, NodeSet.union extra parents⟩

private def markovRight (I : HardIntervention signature) (child : Fin signature.count) : Kernel signature :=
  ⟨NodeSet.singleton child, I.targets, fun parent => mutilatedDirected signature I.targets parent child⟩

private def agreeWhenSupported (left right : Option QProb) : Prop :=
  match left, right with
  | some first, some second => QProb.Equiv first second
  | _, _ => True

private instance agreeWhenSupported_decidable (left right : Option QProb) :
    Decidable (agreeWhenSupported left right) := by
  cases left <;> cases right <;> simp only [agreeWhenSupported] <;> infer_instance

private theorem all_conditionals : ∀ (I : HardIntervention signature) (child : Fin signature.count)
    (reference : signature.Assignment),
    agreeWhenSupported (weakScale.kernelPlausOf (markovLeft I child) reference)
      (weakScale.kernelPlausOf (markovRight I child) reference) := by
  decide +kernel

/-- Even the old interventional screening-off conclusion holds separately
in EVERY slice here. It cannot supply the missing link between experiments. -/
theorem every_slice_screens (I : HardIntervention signature) : MutilatedIdleScreeningOff weakScale I := by
  intro child reference
  dsimp only
  intro first second left right
  have agreed := all_conditionals I child reference
  change weakScale.kernelPlausOf (markovLeft I child) reference = some first at left
  change weakScale.kernelPlausOf (markovRight I child) reference = some second at right
  rw [left, right] at agreed
  exact agreed

theorem weakScale_idleScreeningOff : IdleScreeningOff weakScale := by
  intro child reference
  dsimp only
  intro first second left right
  have agreed := all_conditionals idle child reference
  change weakScale.kernelPlausOf (markovLeft idle child) reference = some first at left
  change weakScale.kernelPlausOf (markovRight idle child) reference = some second at right
  rw [left, right] at agreed
  exact agreed

def witness : signature.Assignment := assignment false true

private def actionValue : QProb := ⟨0, 4, by decide⟩
private def observationValue : QProb := ⟨1, 2, by decide⟩

theorem setting_supported_zero :
    weakScale.kernelPlausOf
      (rule2Left NodeSet.empty (NodeSet.singleton nodeB) (NodeSet.singleton nodeA) NodeSet.empty)
      witness = some actionValue := by rfl

theorem observing_supported_half :
    weakScale.kernelPlausOf
      (rule2Right NodeSet.empty (NodeSet.singleton nodeB) (NodeSet.singleton nodeA) NodeSet.empty)
      witness = some observationValue := by rfl

theorem action_observation_disagree : ¬ QProb.Equiv actionValue observationValue := by decide +kernel

def graph : ObservedGraph signature where
  bidirected _ _ := false
  bidirected_symmetric := by intro _ _ impossible; cases impossible
  bidirected_irreflexive := by intro _; rfl

theorem rule2_disjoint : FourWayDisjoint NodeSet.empty (NodeSet.singleton nodeB)
    (NodeSet.singleton nodeA) NodeSet.empty := by
  constructor <;> unfold NodeSet.Disjoint <;> decide +kernel

/-- Removing A's outgoing arrow separates the two observed vertices, so
the usual Rule 2 graphical condition is satisfied on the declared graph. -/
theorem rule2_separated : graph.dSeparated (.barUnderline NodeSet.empty (NodeSet.singleton nodeA))
    (NodeSet.singleton nodeB) (NodeSet.singleton nodeA)
    (NodeSet.union NodeSet.empty NodeSet.empty) = true := by decide +kernel

private def scaleAgreement (Q : QualitativeUrnScale) (left right : Option Q.Plaus) : Prop :=
  match left, right with
  | some first, some second => Q.eqv first second
  | _, _ => True

private theorem scale_agree (Q : QualitativeUrnScale) {left right : Option Q.Plaus}
    (equal : KernelPlausEqv Q left right) : scaleAgreement Q left right := by
  cases equal with
  | unsupported => trivial
  | defined same => exact same

theorem rule2_qualitative_failure : ¬ KernelPlausEqv rationalScale
    (weakScale.kernelPlausOf
      (rule2Left NodeSet.empty (NodeSet.singleton nodeB) (NodeSet.singleton nodeA) NodeSet.empty)
      witness)
    (weakScale.kernelPlausOf
      (rule2Right NodeSet.empty (NodeSet.singleton nodeB) (NodeSet.singleton nodeA) NodeSet.empty)
      witness) := by
  rw [setting_supported_zero, observing_supported_half]
  intro equal
  exact action_observation_disagree (scale_agree rationalScale equal)

end Thesis.Examples.QualitativeExperimentalDrift
