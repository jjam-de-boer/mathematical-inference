import Thesis.Causality.Structural.Core

namespace Thesis
namespace Causality

open Probability

/-!
Atomic compilation and semantic realization of finite hard interventions.

The compiler replaces each selected mechanism by a constant and removes its
incoming directed and latent inputs one at a time. It deliberately keeps this
long path distinct from the compact hard-intervention evaluator: the main
result proves that the generated target record has the compact evaluator's
unit-level semantics, rather than defining one presentation in terms of the
other.
-/

/-! ## Atomic compilation of finite hard interventions -/

namespace AtomicIntervention

abbrev Action (S : ObservedSignature) :=
  (node : Fin S.count) -> Option (S.Value node)

/-- A structural equation is extensionally constant at one node. -/
def FixedAt (M : ExactModel S) (child : Fin S.count)
    (value : S.Value child) : Prop :=
  forall parents latents, M.mechanism child parents latents = value

/-- Every selected equation is already the constant requested by the action. -/
def RealizesAction (mode : CausalMode S) (action : Action S) : Prop :=
  forall child value, action child = some value ->
    FixedAt mode.record.model child value

/-- No compact intervention remains active in an epistemic causal mode. -/
def NoActiveIntervention (mode : CausalMode S) : Prop :=
  forall child, mode.record.intervention.value child = none

@[simp] theorem initial_noActiveIntervention (model : ExactModel S) :
    NoActiveIntervention
      ⟨"initial", CausalEpistemicRecord.initial model⟩ := by
  intro child
  rfl

/-- Appending an endogenous variable preserves an empty intervention. -/
theorem endogenousLearning_noActiveIntervention
    (mode : CausalMode S) (spec : EndogenousVariableSpec mode.record)
    (targetName : String) (empty : NoActiveIntervention mode) :
    NoActiveIntervention (spec.learnTransition mode targetName).target := by
  intro child
  refine TerminalVariableSpec.terminalCases (motive := fun child =>
      (spec.learnTransition mode targetName).target.record.intervention.value
        child = none) ?_ (fun old => ?_) child
  · simp [EndogenousVariableSpec.learnTransition,
      EndogenousVariableSpec.learnRecord,
      TerminalVariableSpec.liftIntervention]
  · simp [EndogenousVariableSpec.learnTransition,
      EndogenousVariableSpec.learnRecord,
      TerminalVariableSpec.liftIntervention, empty old]

/-- Appending an exogenous root preserves an empty intervention. -/
theorem exogenousLearning_noActiveIntervention
    (mode : CausalMode S) (spec : ExogenousVariableSpec)
    (targetName : String) (empty : NoActiveIntervention mode) :
    NoActiveIntervention (spec.learnTransition mode targetName).target := by
  intro child
  exact empty child

/-- Adding one directed causal link preserves an empty intervention. -/
theorem directedRelating_noActiveIntervention
    (mode : CausalMode S) (parent child : Fin S.count)
    (earlier : parent.val < child.val)
    (operation : DirectedLink.RelateOperation S parent child earlier)
    (targetName : String) (empty : NoActiveIntervention mode) :
    NoActiveIntervention (operation.transition mode targetName).target := by
  intro child
  exact empty child

/-- Adding one latent-input link preserves an empty intervention. -/
theorem latentRelating_noActiveIntervention
    (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count) (child : Fin S.count)
    (operation : LatentLink.RelateOperation mode.record source child)
    (targetName : String) (empty : NoActiveIntervention mode) :
    NoActiveIntervention (operation.transition mode targetName).target := by
  intro node
  exact empty node

/-- Whole-family mechanism replacement preserves an empty intervention. -/
theorem mechanismReplacement_noActiveIntervention
    (mode : CausalMode S)
    (operation : StructuralMechanismReplacement.Operation mode.record)
    (targetName : String) (empty : NoActiveIntervention mode) :
    NoActiveIntervention (operation.transition mode targetName).target := by
  intro child
  exact empty child

/-- A certified belief reindexing preserves absence of active interventions. -/
theorem beliefReindexing_noActiveIntervention
    (mode : CausalMode S)
    (operation : BeliefReindexing.CertifiedOperation mode.record)
    (targetName : String) (empty : NoActiveIntervention mode) :
    NoActiveIntervention (operation.transition mode targetName).target := by
  intro child
  cases operation with
  | mk OriginSignature origin assignment reference interventionPolicy =>
      cases interventionPolicy with
      | preserve _ => exact empty child
      | clear _ _ => rfl

def directedConstantOperation (S : ObservedSignature)
    (parent child : Fin S.count) (value : S.Value child) :
    DirectedLink.UnrelateOperation S parent child where
  replacement := fun _ _ _ => value

/-- Remove one directed input while retaining a constant target equation. -/
def cutDirected (mode : CausalMode S) (parent child : Fin S.count)
    (value : S.Value child) (targetName : String) :
    CausalEditTransition S (DirectedLink.removeSignature S parent child) :=
  DirectedLink.UnrelateOperation.transition
    (directedConstantOperation S parent child value) mode targetName

def latentConstantOperation (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count) (child : Fin S.count)
    (value : S.Value child) :
    LatentLink.UnrelateOperation mode.record source child where
  replacement := fun _ _ => value

/-- Remove one latent input while retaining a constant target equation. -/
def cutLatent (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count) (child : Fin S.count)
    (value : S.Value child) (targetName : String) :
    CausalEditTransition S S :=
  LatentLink.UnrelateOperation.transition (source := source) mode
    (latentConstantOperation mode source child value) targetName

theorem fixed_after_setting (mode : CausalMode S) (child : Fin S.count)
    (value : S.Value child) :
    FixedAt (StructuralSetting.applyConstant mode.record child value).model
      child value := by
  intro parents latents
  exact StructuralSetting.mechanism_at_target mode.record child value
    parents latents

theorem fixed_after_directed_cut (mode : CausalMode S)
    (parent child : Fin S.count) (value : S.Value child) :
    FixedAt
      ((directedConstantOperation S parent child value).apply
        mode.record).model
      child value := by
  intro parents latents
  simp [directedConstantOperation,
    DirectedLink.UnrelateOperation.apply]

theorem fixed_after_latent_cut (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count) (child : Fin S.count)
    (value : S.Value child) :
    FixedAt
      (latentConstantOperation mode source child value).apply.model
      child value := by
  intro parents latents
  simp [latentConstantOperation,
    LatentLink.UnrelateOperation.apply]

theorem directed_cut_mechanism_other (mode : CausalMode S)
    (parent child node : Fin S.count) (value : S.Value child)
    (different : node ≠ child)
    (parents : (DirectedLink.removeSignature S parent child).ParentValues node)
    (latents : (DirectedLink.removeLatent mode.record.model parent child).Inputs node) :
    (((directedConstantOperation S parent child value).apply
      mode.record).model.mechanism node parents latents) =
      mode.record.model.mechanism node
        (fun candidate oldEdge => parents candidate
          (DirectedLink.remainingEdge S parent child different oldEdge))
        latents := by
  unfold DirectedLink.UnrelateOperation.apply
  dsimp [directedConstantOperation]
  split
  · rename_i equal
    exact (different equal).elim
  · rfl

/-- Cutting one input of an already constant equation preserves all values. -/
theorem directed_cut_evalNode_eq (mode : CausalMode S)
    (parent child : Fin S.count) (value : S.Value child)
    (fixed : FixedAt mode.record.model child value)
    (u : mode.record.model.latent.Assignment) (node : Fin S.count) :
    (((directedConstantOperation S parent child value).apply
      mode.record).model.eval u node) = mode.record.model.eval u node := by
  change (((directedConstantOperation S parent child value).apply
      mode.record).model.evalNodeUnder
        (FiniteLatentSCM.noIntervention
          (DirectedLink.removeSignature S parent child)) u node) =
    mode.record.model.evalNodeUnder
      (FiniteLatentSCM.noIntervention S) u node
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  simp only [FiniteLatentSCM.noIntervention]
  by_cases selected : node = child
  · subst node
    rw [fixed_after_directed_cut mode parent child value]
    rw [fixed]
  · rw [directed_cut_mechanism_other mode parent child node value selected]
    congr 1
    funext candidate edge
    exact directed_cut_evalNode_eq mode parent child value fixed u candidate
termination_by node.val
decreasing_by
  exact S.directed_earlier edge

theorem directed_cut_eval_eq (mode : CausalMode S)
    (parent child : Fin S.count) (value : S.Value child)
    (fixed : FixedAt mode.record.model child value)
    (u : mode.record.model.latent.Assignment) :
    (((directedConstantOperation S parent child value).apply
      mode.record).model.eval u) = mode.record.model.eval u := by
  funext node
  exact directed_cut_evalNode_eq mode parent child value fixed u node

theorem latent_cut_mechanism_other (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count)
    (child node : Fin S.count) (value : S.Value child)
    (different : node ≠ child) (parents : S.ParentValues node)
    (latents : (LatentLink.removeExtension mode.record.model source child).Inputs node) :
    ((latentConstantOperation mode source child value).apply.model.mechanism
      node parents latents) =
      mode.record.model.mechanism node parents
        (fun candidate oldIncident => latents candidate
          (LatentLink.remainingIncident mode.record.model source child
            different oldIncident)) := by
  unfold LatentLink.UnrelateOperation.apply
  dsimp [latentConstantOperation]
  split
  · rename_i equal
    exact (different equal).elim
  · rfl

theorem latent_cut_evalNode_eq (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count)
    (child : Fin S.count) (value : S.Value child)
    (fixed : FixedAt mode.record.model child value)
    (u : mode.record.model.latent.Assignment) (node : Fin S.count) :
    ((latentConstantOperation mode source child value).apply.model.eval u node) =
      mode.record.model.eval u node := by
  change (latentConstantOperation mode source child value).apply.model.evalNodeUnder
      (FiniteLatentSCM.noIntervention S) u node =
    mode.record.model.evalNodeUnder
      (FiniteLatentSCM.noIntervention S) u node
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  simp only [FiniteLatentSCM.noIntervention]
  by_cases selected : node = child
  · subst node
    rw [fixed_after_latent_cut mode source child value]
    rw [fixed]
  · rw [latent_cut_mechanism_other mode source child node value selected]
    congr 1
    funext candidate edge
    exact latent_cut_evalNode_eq mode source child value fixed u candidate
termination_by node.val
decreasing_by
  exact S.directed_earlier edge

theorem latent_cut_eval_eq (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count)
    (child : Fin S.count) (value : S.Value child)
    (fixed : FixedAt mode.record.model child value)
    (u : mode.record.model.latent.Assignment) :
    ((latentConstantOperation mode source child value).apply.model.eval u) =
      mode.record.model.eval u := by
  funext node
  exact latent_cut_evalNode_eq mode source child value fixed u node

theorem fixed_after_setting_other (mode : CausalMode S)
    (setNode fixedNode : Fin S.count) (setValue : S.Value setNode)
    (fixedValue : S.Value fixedNode) (different : fixedNode ≠ setNode)
    (fixed : FixedAt mode.record.model fixedNode fixedValue) :
    FixedAt
      (StructuralSetting.applyConstant mode.record setNode setValue).model
      fixedNode fixedValue := by
  intro parents latents
  unfold StructuralSetting.applyConstant StructuralSetting.constantOperation
    StructuralSetting.Operation.apply
  dsimp
  split
  · rename_i equal
    exact (different equal).elim
  · exact fixed parents latents

theorem fixed_after_directed_cut_other (mode : CausalMode S)
    (parent cutNode fixedNode : Fin S.count) (cutValue : S.Value cutNode)
    (fixedValue : S.Value fixedNode) (different : fixedNode ≠ cutNode)
    (fixed : FixedAt mode.record.model fixedNode fixedValue) :
    FixedAt
      ((directedConstantOperation S parent cutNode cutValue).apply
        mode.record).model fixedNode fixedValue := by
  intro parents latents
  rw [directed_cut_mechanism_other mode parent cutNode fixedNode cutValue
    different]
  exact fixed _ _

theorem fixed_after_latent_cut_other (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count)
    (cutNode fixedNode : Fin S.count) (cutValue : S.Value cutNode)
    (fixedValue : S.Value fixedNode) (different : fixedNode ≠ cutNode)
    (fixed : FixedAt mode.record.model fixedNode fixedValue) :
    FixedAt
      (latentConstantOperation mode source cutNode cutValue).apply.model
      fixedNode fixedValue := by
  intro parents latents
  rw [latent_cut_mechanism_other mode source cutNode fixedNode cutValue
    different]
  exact fixed _ _

/-!
### Coordinate-preserving compiled prefixes

Every structural edit may change the dependent signature. This section records
the coordinate maps explicitly, so later endpoint comparisons are stated after
transport rather than relying on ill-typed definitional equality.
-/

/-- The target has the same node coordinates and value types as the source. -/
structure NodeEquiv (S T : ObservedSignature) where
  toFun : Fin S.count -> Fin T.count
  invFun : Fin T.count -> Fin S.count
  left_inv : forall node, invFun (toFun node) = node
  right_inv : forall node, toFun (invFun node) = node

namespace NodeEquiv

def refl (S : ObservedSignature) : NodeEquiv S S where
  toFun := fun node => node
  invFun := fun node => node
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def trans (first : NodeEquiv S T) (second : NodeEquiv T U) :
    NodeEquiv S U where
  toFun := fun node => second.toFun (first.toFun node)
  invFun := fun node => first.invFun (second.invFun node)
  left_inv := by
    intro node
    rw [second.left_inv, first.left_inv]
  right_inv := by
    intro node
    rw [first.right_inv, second.right_inv]

end NodeEquiv

structure SameCoordinates (S T : ObservedSignature) where
  nodeEquiv : NodeEquiv S T
  value_eq : forall node : Fin S.count,
    S.Value node = T.Value (nodeEquiv.toFun node)

namespace SameCoordinates

def refl (S : ObservedSignature) : SameCoordinates S S where
  nodeEquiv := NodeEquiv.refl S
  value_eq := fun _ => rfl

def trans (first : SameCoordinates S T) (second : SameCoordinates T U) :
    SameCoordinates S U where
  nodeEquiv := first.nodeEquiv.trans second.nodeEquiv
  value_eq := fun node => Eq.trans (first.value_eq node)
    (second.value_eq (first.nodeEquiv.toFun node))

def transportAction (coordinates : SameCoordinates S T)
    (action : Action S) : Action T :=
  fun node =>
    match action (coordinates.nodeEquiv.invFun node) with
    | none => none
    | some value => some (cast
        (Eq.trans
          (coordinates.value_eq (coordinates.nodeEquiv.invFun node))
          (congrArg T.Value (coordinates.nodeEquiv.right_inv node)))
        value)

/-- Reindex a dependent observed assignment along the recorded coordinates. -/
def transportObserved (coordinates : SameCoordinates S T)
    (assignment : S.Assignment) : T.Assignment :=
  fun node =>
    cast
      (Eq.trans
        (coordinates.value_eq (coordinates.nodeEquiv.invFun node))
        (congrArg T.Value (coordinates.nodeEquiv.right_inv node)))
      (assignment (coordinates.nodeEquiv.invFun node))

/-- Reindex a target assignment back to the source coordinates. -/
def untransportObserved (coordinates : SameCoordinates S T)
    (assignment : T.Assignment) : S.Assignment :=
  fun node => cast (coordinates.value_eq node).symm
    (assignment (coordinates.nodeEquiv.toFun node))

@[simp] theorem untransportObserved_transportObserved
    (coordinates : SameCoordinates S T) (assignment : S.Assignment) :
    coordinates.untransportObserved
        (coordinates.transportObserved assignment) = assignment := by
  funext node
  unfold untransportObserved transportObserved
  apply eq_of_heq
  exact HEq.trans (cast_heq _ _)
    (HEq.trans (cast_heq _ _)
      (by rw [coordinates.nodeEquiv.left_inv]))

@[simp] theorem transportAction_refl (action : Action S) (node : Fin S.count) :
    (refl S).transportAction action node = action node := by
  unfold transportAction refl
  dsimp [NodeEquiv.refl]
  cases action node with
  | none => rfl
  | some value =>
      apply congrArg some
      rfl

theorem transportAction_trans (first : SameCoordinates S T)
    (second : SameCoordinates T U) (action : Action S) :
    second.transportAction (first.transportAction action) =
      (first.trans second).transportAction action := by
  funext node
  unfold transportAction
  dsimp [trans, NodeEquiv.trans]
  let sourceNode := first.nodeEquiv.invFun (second.nodeEquiv.invFun node)
  cases selected : action sourceNode with
  | none => simp
  | some value =>
      apply congrArg some
      apply eq_of_heq
      exact HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _)
        (cast_heq _ _).symm)

/-- Transporting an action preserves whether an original coordinate is selected. -/
theorem transportAction_isSome_toFun (coordinates : SameCoordinates S T)
    (action : Action S) (child : Fin S.count) :
    (coordinates.transportAction action
        (coordinates.nodeEquiv.toFun child)).isSome =
      (action child).isSome := by
  have isSomeEq :
      (action (coordinates.nodeEquiv.invFun
        (coordinates.nodeEquiv.toFun child))).isSome =
        (action child).isSome :=
    congrArg (fun node => (action node).isSome)
      (coordinates.nodeEquiv.left_inv child)
  unfold transportAction
  cases sourceSelected : action (coordinates.nodeEquiv.invFun
      (coordinates.nodeEquiv.toFun child)) <;>
    simp only [sourceSelected, Option.isSome_none, Option.isSome_some] at isSomeEq ⊢
  · exact isSomeEq
  · exact isSomeEq

@[simp] theorem transportObserved_refl (assignment : S.Assignment) :
    (refl S).transportObserved assignment = assignment := by
  rfl

theorem transportObserved_trans (first : SameCoordinates S T)
    (second : SameCoordinates T U) (assignment : S.Assignment) :
    second.transportObserved (first.transportObserved assignment) =
      (first.trans second).transportObserved assignment := by
  funext node
  simp [transportObserved, trans, NodeEquiv.trans]

end SameCoordinates

/-- A constructive equivalence between two finite index sets. -/
structure FinIndexEquiv (left right : Nat) where
  toFun : Fin left -> Fin right
  invFun : Fin right -> Fin left
  left_inv : forall index, invFun (toFun index) = index
  right_inv : forall index, toFun (invFun index) = index

namespace FinIndexEquiv

def refl (count : Nat) : FinIndexEquiv count count where
  toFun := fun index => index
  invFun := fun index => index
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def trans (first : FinIndexEquiv left middle)
    (second : FinIndexEquiv middle right) : FinIndexEquiv left right where
  toFun := fun index => second.toFun (first.toFun index)
  invFun := fun index => first.invFun (second.invFun index)
  left_inv := by
    intro index
    rw [second.left_inv, first.left_inv]
  right_inv := by
    intro index
    rw [first.right_inv, second.right_inv]

end FinIndexEquiv

/-- The latent roots and their value types are unchanged by a compiled `do`. -/
structure SameRoots {S T : ObservedSignature}
    (source : CausalMode S) (target : CausalMode T) where
  rootEquiv : FinIndexEquiv source.record.model.latent.count
    target.record.model.latent.count
  value_eq : forall root : Fin source.record.model.latent.count,
    source.record.model.latent.Value root =
      target.record.model.latent.Value (rootEquiv.toFun root)

namespace SameRoots

def refl (mode : CausalMode S) : SameRoots mode mode where
  rootEquiv := FinIndexEquiv.refl mode.record.model.latent.count
  value_eq := fun _ => rfl

def trans (first : SameRoots source middle)
    (second : SameRoots middle target) : SameRoots source target where
  rootEquiv :=
    first.rootEquiv.trans second.rootEquiv
  value_eq := fun root => Eq.trans (first.value_eq root)
    (second.value_eq (first.rootEquiv.toFun root))

def transportAssignment (roots : SameRoots source target)
    (assignment : source.record.model.latent.Assignment) :
    target.record.model.latent.Assignment :=
  fun root =>
    cast
      (Eq.trans
        (roots.value_eq (roots.rootEquiv.invFun root))
        (congrArg target.record.model.latent.Value
          (roots.rootEquiv.right_inv root)))
      (assignment (roots.rootEquiv.invFun root))

end SameRoots

/-- A compiled path whose target coordinates are explicitly related to its source. -/
structure Execution (source : CausalMode S) where
  signature : ObservedSignature
  target : CausalMode signature
  path : CausalEditPath source target
  coordinates : SameCoordinates S signature
  roots : SameRoots source target

namespace Execution

def identity (mode : CausalMode S) : Execution mode where
  signature := S
  target := mode
  path := .nil mode
  coordinates := SameCoordinates.refl S
  roots := SameRoots.refl mode

def prepend (transition : CausalEditTransition S T)
    (coordinates : SameCoordinates S T)
    (roots : SameRoots transition.source transition.target)
    (tail : Execution transition.target) : Execution transition.source where
  signature := tail.signature
  target := tail.target
  path := .cons transition tail.path
  coordinates := coordinates.trans tail.coordinates
  roots := roots.trans tail.roots

def append (first : Execution source)
    (second : Execution first.target) : Execution source where
  signature := second.signature
  target := second.target
  path := first.path.append second.path
  coordinates := first.coordinates.trans second.coordinates
  roots := first.roots.trans second.roots

def transportedAction {S : ObservedSignature} {source : CausalMode S}
    (execution : Execution source)
    (action : Action S) : Action execution.signature :=
  execution.coordinates.transportAction action

def transportedAssignment (execution : Execution source)
    (assignment : source.record.model.latent.Assignment) :
    execution.target.record.model.latent.Assignment :=
  execution.roots.transportAssignment assignment

def transportedObserved {S : ObservedSignature} {source : CausalMode S}
    (execution : Execution source)
    (assignment : S.Assignment) : execution.signature.Assignment :=
  execution.coordinates.transportObserved assignment

/-- Unit-level semantic preservation for a dependent-signature executable edit path. -/
structure Semantics (execution : Execution source) : Prop where
  evaluate : forall assignment : source.record.model.latent.Assignment,
    Exists fun targetAssignment :
        execution.target.record.model.latent.Assignment =>
      execution.target.record.model.eval targetAssignment =
        execution.transportedObserved (source.record.model.eval assignment)

/-- An edit path realizes an explicitly supplied source-level evaluator. -/
structure RealizesEvaluation {S : ObservedSignature} {source : CausalMode S}
    (execution : Execution source)
    (reference : source.record.model.latent.Assignment -> S.Assignment) : Prop where
  evaluate : forall assignment : source.record.model.latent.Assignment,
    Exists fun targetAssignment :
        execution.target.record.model.latent.Assignment =>
      execution.target.record.model.eval targetAssignment =
        execution.transportedObserved (reference assignment)

/--
A constructive execution certificate.  Unlike `RealizesEvaluation`, it retains
the target latent assignment as explicit data rather than hiding it under
`Exists`.  This is the form needed to push a finite belief through an edit
program and compare event probabilities.
-/
structure DeterministicRealizesEvaluation
    {S : ObservedSignature} {source : CausalMode S}
    (execution : Execution source)
    (reference : source.record.model.latent.Assignment -> S.Assignment) where
  assignment : source.record.model.latent.Assignment ->
    execution.target.record.model.latent.Assignment
  evaluate : forall sourceAssignment,
    execution.target.record.model.eval (assignment sourceAssignment) =
      execution.transportedObserved (reference sourceAssignment)

def DeterministicRealizesEvaluation.toExistential
    (realizes : DeterministicRealizesEvaluation execution reference) :
    RealizesEvaluation execution reference where
  evaluate := fun assignment => ⟨realizes.assignment assignment,
    realizes.evaluate assignment⟩

namespace Semantics

def identity (mode : CausalMode S) : Semantics (Execution.identity mode) where
  evaluate := fun assignment => ⟨assignment, rfl⟩

def prepend (transition : CausalEditTransition S T)
    (coordinates : SameCoordinates S T)
    (roots : SameRoots transition.source transition.target)
    (tail : Execution transition.target)
    (stepSemantic : forall assignment :
        transition.source.record.model.latent.Assignment,
      Exists fun targetAssignment :
          transition.target.record.model.latent.Assignment =>
        transition.target.record.model.eval targetAssignment =
          coordinates.transportObserved
            (transition.source.record.model.eval assignment))
    (tailSemantic : Semantics tail) :
    Semantics (Execution.prepend transition coordinates roots tail) where
  evaluate := by
    intro assignment
    rcases stepSemantic assignment with ⟨middleAssignment, first⟩
    rcases tailSemantic.evaluate middleAssignment with
      ⟨targetAssignment, second⟩
    refine ⟨targetAssignment, ?_⟩
    change tail.target.record.model.eval targetAssignment =
      (coordinates.trans tail.coordinates).transportObserved
        (transition.source.record.model.eval assignment)
    rw [second, first]
    exact SameCoordinates.transportObserved_trans coordinates tail.coordinates
      (transition.source.record.model.eval assignment)

def append (first : Execution source) (second : Execution first.target)
    (firstSemantic : Semantics first) (secondSemantic : Semantics second) :
    Semantics (Execution.append first second) where
  evaluate := by
    intro assignment
    rcases firstSemantic.evaluate assignment with ⟨middleAssignment, firstEq⟩
    rcases secondSemantic.evaluate middleAssignment with
      ⟨targetAssignment, secondEq⟩
    refine ⟨targetAssignment, ?_⟩
    change second.target.record.model.eval targetAssignment =
      (first.coordinates.trans second.coordinates).transportObserved
        (source.record.model.eval assignment)
    rw [secondEq, firstEq]
    exact SameCoordinates.transportObserved_trans first.coordinates second.coordinates
      (source.record.model.eval assignment)

end Semantics

namespace RealizesEvaluation

def appendSemantics {S : ObservedSignature} {source : CausalMode S}
    (first : Execution source)
    (second : Execution first.target)
    (reference : source.record.model.latent.Assignment -> S.Assignment)
    (firstRealizes : RealizesEvaluation first reference)
    (secondSemantic : Semantics second) :
    RealizesEvaluation (Execution.append first second) reference where
  evaluate := by
    intro assignment
    rcases firstRealizes.evaluate assignment with
      ⟨middleAssignment, firstEq⟩
    rcases secondSemantic.evaluate middleAssignment with
      ⟨targetAssignment, secondEq⟩
    refine ⟨targetAssignment, ?_⟩
    change second.target.record.model.eval targetAssignment =
      (first.coordinates.trans second.coordinates).transportObserved
        (reference assignment)
    rw [secondEq, firstEq]
    exact SameCoordinates.transportObserved_trans first.coordinates
      second.coordinates (reference assignment)

end RealizesEvaluation

namespace DeterministicRealizesEvaluation

def identity (mode : CausalMode S) :
    DeterministicRealizesEvaluation (Execution.identity mode)
      mode.record.model.eval where
  assignment := fun assignment => assignment
  evaluate := fun _ => rfl

def prepend (transition : CausalEditTransition S T)
    (coordinates : SameCoordinates S T)
    (roots : SameRoots transition.source transition.target)
    (tail : Execution transition.target)
    (stepAssignment :
      transition.source.record.model.latent.Assignment ->
        transition.target.record.model.latent.Assignment)
    (stepSemantic : forall assignment,
      transition.target.record.model.eval (stepAssignment assignment) =
        coordinates.transportObserved
          (transition.source.record.model.eval assignment))
    (tailSemantic : DeterministicRealizesEvaluation tail
      transition.target.record.model.eval) :
    DeterministicRealizesEvaluation
      (Execution.prepend transition coordinates roots tail)
      transition.source.record.model.eval where
  assignment := fun assignment =>
    tailSemantic.assignment (stepAssignment assignment)
  evaluate := by
    intro assignment
    change tail.target.record.model.eval
        (tailSemantic.assignment (stepAssignment assignment)) =
      (coordinates.trans tail.coordinates).transportObserved
        (transition.source.record.model.eval assignment)
    rw [tailSemantic.evaluate, stepSemantic]
    exact SameCoordinates.transportObserved_trans coordinates tail.coordinates
      (transition.source.record.model.eval assignment)

def appendSemantics {S : ObservedSignature} {source : CausalMode S}
    (first : Execution source)
    (second : Execution first.target)
    (reference : source.record.model.latent.Assignment -> S.Assignment)
    (firstRealizes : DeterministicRealizesEvaluation first reference)
    (secondAssignment :
      first.target.record.model.latent.Assignment ->
        second.target.record.model.latent.Assignment)
    (secondSemantic : forall assignment,
      second.target.record.model.eval (secondAssignment assignment) =
        second.transportedObserved
          (first.target.record.model.eval assignment)) :
    DeterministicRealizesEvaluation (Execution.append first second) reference where
  assignment := fun assignment =>
    secondAssignment (firstRealizes.assignment assignment)
  evaluate := by
    intro assignment
    change second.target.record.model.eval
        (secondAssignment (firstRealizes.assignment assignment)) =
      (first.coordinates.trans second.coordinates).transportObserved
        (reference assignment)
    rw [secondSemantic, firstRealizes.evaluate]
    exact SameCoordinates.transportObserved_trans first.coordinates
      second.coordinates (reference assignment)

/--
Evidence that the endpoint's active intervention has already been compiled
into its structural equations on every latent assignment selected by a
deterministic realization.
-/
structure EndpointInterventionAbsorbed
    {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source}
    {reference : source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference) : Prop where
  evaluate : forall sourceAssignment,
    execution.target.record.model.evalUnder
        execution.target.record.intervention.value
        (realizes.assignment sourceAssignment) =
      execution.target.record.model.eval
        (realizes.assignment sourceAssignment)

namespace EndpointInterventionAbsorbed

/-- An endpoint with no active intervention is, in particular, absorbed. -/
def ofEmpty
    {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source}
    {reference : source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (empty : forall node,
      execution.target.record.intervention.value node = none) :
    EndpointInterventionAbsorbed realizes where
  evaluate := by
    intro sourceAssignment
    have interventionEq :
        execution.target.record.intervention.value =
          FiniteLatentSCM.noIntervention execution.signature := by
      funext node
      simpa [FiniteLatentSCM.noIntervention] using empty node
    rw [interventionEq]
    exact execution.target.record.model.evalUnder_noIntervention
      (realizes.assignment sourceAssignment)

end EndpointInterventionAbsorbed

/--
Transport the current epistemic belief through a constructive edit execution.
The resulting record uses the actual endpoint SCM and no residual compact
intervention override.
-/
def endpointRecord {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source} {reference :
      source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference) :
    CausalEpistemicRecord execution.signature where
  model := execution.target.record.model
  belief := source.record.belief.map realizes.assignment
  intervention := HardIntervention.empty execution.signature

/-- Intrinsic belief reindexing data for the canonical probability endpoint. -/
def endpointReindexing {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source} {reference :
      source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (absorbed : EndpointInterventionAbsorbed realizes) :
    BeliefReindexing.CertifiedOperation execution.target.record where
  OriginSignature := S
  origin := .current source.record
  assignment := realizes.assignment
  reference := fun assignment =>
    execution.transportedObserved (reference assignment)
  interventionPolicy := .clear
    (absorbed := absorbed.evaluate)
    (structuralRealization := realizes.evaluate)

/--
The canonical atomic endpoint is reindexed from the current source belief,
through exactly the constructive latent assignment retained by `realizes`.
-/
@[simp] theorem endpointReindexing_belief
    {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source} {reference :
      source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (absorbed : EndpointInterventionAbsorbed realizes) :
    (realizes.endpointReindexing absorbed).apply.belief =
      source.record.belief.map realizes.assignment :=
  rfl

/--
The final proof-carrying reindexing step that turns the semantic endpoint
record into the literal target of an executable causal-edit path.
-/
def endpointTransition {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source} {reference :
      source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (absorbed : EndpointInterventionAbsorbed realizes) :
    CausalEditTransition execution.signature execution.signature where
  source := execution.target
  target := ⟨"canonical-probability-endpoint", realizes.endpointRecord⟩
  operation := .reindexingBelief (realizes.endpointReindexing absorbed)
  realized := rfl

def endpointRoots {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source} {reference :
      source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (absorbed : EndpointInterventionAbsorbed realizes) :
    SameRoots execution.target (realizes.endpointTransition absorbed).target where
  rootEquiv :=
    FinIndexEquiv.refl execution.target.record.model.latent.count
  value_eq := fun _ => rfl

/-- The one-step execution that installs the canonical probability endpoint. -/
def endpointExecution {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source} {reference :
      source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (absorbed : EndpointInterventionAbsorbed realizes) :
    Execution execution.target where
  signature := execution.signature
  target := (realizes.endpointTransition absorbed).target
  path := CausalEditPath.single (realizes.endpointTransition absorbed)
  coordinates := SameCoordinates.refl execution.signature
  roots := realizes.endpointRoots absorbed

/-- Append canonical probability reindexing to an already executed edit path. -/
def canonicalExecution {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source} {reference :
      source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (absorbed : EndpointInterventionAbsorbed realizes) :
    Execution source :=
  execution.append (realizes.endpointExecution absorbed)

/--
The closed execution retains the same evaluator while making its
probability-bearing record the literal target.
-/
noncomputable def canonicalRealizes
    {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source} {reference :
      source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (absorbed : EndpointInterventionAbsorbed realizes) :
    DeterministicRealizesEvaluation
      (realizes.canonicalExecution absorbed) reference :=
  DeterministicRealizesEvaluation.appendSemantics
    execution (realizes.endpointExecution absorbed) reference realizes
    (fun assignment => assignment) (fun _ => rfl)

@[simp] theorem canonicalExecution_target_record
    {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source} {reference :
      source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (absorbed : EndpointInterventionAbsorbed realizes) :
    (realizes.canonicalExecution absorbed).target.record =
      realizes.endpointRecord :=
  rfl

@[simp] theorem canonicalRealizes_endpointRecord
    {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source} {reference :
      source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (absorbed : EndpointInterventionAbsorbed realizes) :
    (realizes.canonicalRealizes absorbed).endpointRecord =
      (realizes.canonicalExecution absorbed).target.record :=
  rfl

def endpointEvent {S : ObservedSignature} {source : CausalMode S}
    (execution : Execution source) (event : S.Assignment -> Bool) :
    execution.signature.Assignment -> Bool :=
  fun assignment =>
    event (execution.coordinates.untransportObserved assignment)

/--
Endpoint probabilities are exactly the source-belief probabilities of the
reference evaluator.  This is the probability-level bridge missing from an
existential unit-by-unit semantics.
-/
theorem endpointRecord_observedValue
    {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source}
    {reference : source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (event : S.Assignment -> Bool) :
    QProb.Equiv
      (realizes.endpointRecord.observedValue
        (endpointEvent execution event))
      (source.record.belief.probVal
        (fun assignment => event (reference assignment))) := by
  exact QProb.equiv_trans
    (realizes.endpointRecord.observedDist_probVal
      (endpointEvent execution event))
    (QProb.equiv_trans
      (FiniteProbRecord.map_probVal source.record.belief realizes.assignment
        (fun targetAssignment =>
          endpointEvent execution event
            (execution.target.record.model.eval targetAssignment)))
      (FiniteProbRecord.probVal_congr source.record.belief _ _
        (fun assignment => by
          unfold endpointEvent
          rw [realizes.evaluate]
          unfold transportedObserved
          rw [SameCoordinates.untransportObserved_transportObserved])))

/--
The two probability-bearing fields needed to identify the canonical endpoint
record with the literal record reached by an edit execution.
-/
structure TargetRecordAgreement
    {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source}
    {reference : source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference) : Prop where
  belief : forall event :
      execution.target.record.model.latent.Assignment -> Bool,
    QProb.Equiv
      ((source.record.belief.map realizes.assignment).probVal event)
      (execution.target.record.belief.probVal event)
  interventionEmpty : forall node,
    execution.target.record.intervention.value node = none

/--
Under the explicit belief-transport and no-residual-intervention invariants,
every endpoint event has the same probability in `endpointRecord` and in the
literal target record. Record equality is neither required nor asserted.
-/
theorem endpointRecord_target_observedValue
    {S : ObservedSignature} {source : CausalMode S}
    {execution : Execution source}
    {reference : source.record.model.latent.Assignment -> S.Assignment}
    (realizes : DeterministicRealizesEvaluation execution reference)
    (agreement : TargetRecordAgreement realizes)
    (event : execution.signature.Assignment -> Bool) :
    QProb.Equiv
      (realizes.endpointRecord.observedValue event)
      (execution.target.record.observedValue event) := by
  let endpointLatentEvent :
      execution.target.record.model.latent.Assignment -> Bool :=
    fun assignment =>
      event (execution.target.record.model.evalUnder
        (HardIntervention.empty execution.signature).value assignment)
  let targetLatentEvent :
      execution.target.record.model.latent.Assignment -> Bool :=
    fun assignment =>
      event (execution.target.record.model.evalUnder
        execution.target.record.intervention.value assignment)
  have eventAgreement : forall assignment,
      endpointLatentEvent assignment = targetLatentEvent assignment := by
    intro assignment
    unfold endpointLatentEvent targetLatentEvent
    congr 2
    funext node
    simpa [HardIntervention.empty, FiniteLatentSCM.noIntervention] using
      (agreement.interventionEmpty node).symm
  exact QProb.equiv_trans
    (realizes.endpointRecord.observedDist_probVal event)
    (QProb.equiv_trans
      (agreement.belief endpointLatentEvent)
      (QProb.equiv_trans
        (FiniteProbRecord.probVal_congr execution.target.record.belief
          endpointLatentEvent targetLatentEvent eventAgreement)
        (QProb.equiv_symm
          (execution.target.record.observedDist_probVal event))))

end DeterministicRealizesEvaluation

end Execution

/-- A source directed input is absent at an execution endpoint. -/
def DirectedInputAbsent {S : ObservedSignature} {mode : CausalMode S}
    (execution : Execution mode) (parent child : Fin S.count) : Prop :=
  execution.signature.directed
    (execution.coordinates.nodeEquiv.toFun parent)
    (execution.coordinates.nodeEquiv.toFun child) = false

/-- A source latent input is absent at an execution endpoint. -/
def LatentInputAbsent {S : ObservedSignature} {mode : CausalMode S}
    (execution : Execution mode)
    (source : Fin mode.record.model.latent.count)
    (child : Fin S.count) : Prop :=
  execution.target.record.model.latent.incident
    (execution.roots.rootEquiv.toFun source)
    (execution.coordinates.nodeEquiv.toFun child) = false

def settingRoots (mode : CausalMode S) (child : Fin S.count)
    (value : S.Value child) (targetName : String) :
    SameRoots mode
      (StructuralSetting.transition mode child value targetName).target where
  rootEquiv :=
    { toFun := fun root => root
      invFun := fun root => root
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  value_eq := fun _ => rfl

def directedCutRoots (mode : CausalMode S) (parent child : Fin S.count)
    (value : S.Value child) (targetName : String) :
    SameRoots mode (cutDirected mode parent child value targetName).target where
  rootEquiv :=
    { toFun := fun root => root
      invFun := fun root => root
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  value_eq := fun _ => rfl

def latentCutRoots (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count) (child : Fin S.count)
    (value : S.Value child) (targetName : String) :
    SameRoots mode (cutLatent mode source child value targetName).target where
  rootEquiv :=
    { toFun := fun root => root
      invFun := fun root => root
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  value_eq := fun _ => rfl

def directedCoordinates (S : ObservedSignature)
    (parent child : Fin S.count) :
    SameCoordinates S (DirectedLink.removeSignature S parent child) where
  nodeEquiv :=
    { toFun := fun node => node
      invFun := fun node => node
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  value_eq := fun _ => rfl

@[simp] theorem directedCoordinates_transportAction
    (S : ObservedSignature) (parent child : Fin S.count)
    (action : Action S) (node : Fin S.count) :
    (directedCoordinates S parent child).transportAction action node =
      action node := by
  unfold SameCoordinates.transportAction
  dsimp [directedCoordinates]
  cases action node with
  | none => rfl
  | some value => exact congrArg some (cast_eq _ value)

@[simp] theorem directedCoordinates_transportObserved
    (S : ObservedSignature) (parent child : Fin S.count)
    (assignment : S.Assignment) :
    (directedCoordinates S parent child).transportObserved assignment =
      assignment := by
  rfl

/-!
### Structural constant-setting phase

For each selected node, first replace its mechanism by the requested constant.
The phase preserves all other mechanisms and keeps the compact intervention
field empty; incoming edges are removed only in the following two phases.
-/

def setMode (mode : CausalMode S) (action : Action S) :
    List (Fin S.count) -> CausalMode S
  | [] => mode
  | child :: rest =>
      match action child with
      | none => setMode mode action rest
      | some value =>
          setMode
            (StructuralSetting.transition mode child value
              "atomic-do-set").target action rest

def setPath (mode : CausalMode S) (action : Action S) :
    (nodes : List (Fin S.count)) ->
      CausalEditPath mode (setMode mode action nodes)
  | [] => by simpa [setMode] using CausalEditPath.nil mode
  | child :: rest => by
      cases selected : action child with
      | none =>
          simpa [setMode, selected] using setPath mode action rest
      | some value =>
          let step := StructuralSetting.transition mode child value
            "atomic-do-set"
          simpa [setMode, selected, step] using
            CausalEditPath.cons step (setPath step.target action rest)

def setRoots (mode : CausalMode S) (action : Action S) :
    (nodes : List (Fin S.count)) -> SameRoots mode (setMode mode action nodes)
  | [] => by simpa [setMode] using SameRoots.refl mode
  | child :: rest => by
      cases selected : action child with
      | none =>
          simpa [setMode, selected] using setRoots mode action rest
      | some value =>
          let step := StructuralSetting.transition mode child value
            "atomic-do-set"
          simpa [setMode, selected, step] using
            (settingRoots mode child value "atomic-do-set").trans
              (setRoots step.target action rest)

def setExecution (mode : CausalMode S) (action : Action S)
    (nodes : List (Fin S.count)) : Execution mode where
  signature := S
  target := setMode mode action nodes
  path := setPath mode action nodes
  coordinates := SameCoordinates.refl S
  roots := setRoots mode action nodes

/-- Constant-setting edits preserve absence of a compact intervention. -/
theorem setMode_noActiveIntervention
    (mode : CausalMode S) (action : Action S)
    (empty : NoActiveIntervention mode) :
    (nodes : List (Fin S.count)) ->
      NoActiveIntervention (setMode mode action nodes)
  | [] => by
      simpa [setMode] using empty
  | child :: rest => by
      cases selected : action child with
      | none =>
          simpa [setMode, selected] using
            setMode_noActiveIntervention mode action empty rest
      | some value =>
          let step := StructuralSetting.transition mode child value
            "atomic-do-set"
          have stepEmpty : NoActiveIntervention step.target := by
            intro node
            exact empty node
          simpa [setMode, selected, step] using
            setMode_noActiveIntervention step.target action stepEmpty rest

theorem setMode_preserves_fixed (mode : CausalMode S) (action : Action S)
    (nodes : List (Fin S.count)) (child : Fin S.count) (value : S.Value child)
    (selected : action child = some value)
    (fixed : FixedAt mode.record.model child value) :
    FixedAt (setMode mode action nodes).record.model child value := by
  induction nodes generalizing mode with
  | nil => simpa [setMode] using fixed
  | cons setNode rest ih =>
      cases setSelected : action setNode with
      | none =>
          simpa [setMode, setSelected] using ih mode fixed
      | some setValue =>
          let step := StructuralSetting.transition mode setNode setValue
            "atomic-do-set"
          have stepFixed : FixedAt step.target.record.model child value := by
            by_cases same : child = setNode
            · subst child
              have valuesEqual : setValue = value :=
                Option.some.inj (setSelected.symm.trans selected)
              subst setValue
              exact fixed_after_setting mode setNode value
            · exact fixed_after_setting_other mode setNode child setValue
                value same fixed
          simpa [setMode, setSelected, step] using ih step.target stepFixed

theorem setMode_fixes_member (mode : CausalMode S) (action : Action S)
    (nodes : List (Fin S.count)) (child : Fin S.count) (value : S.Value child)
    (member : child ∈ nodes) (selected : action child = some value) :
    FixedAt (setMode mode action nodes).record.model child value := by
  induction nodes generalizing mode with
  | nil => simp at member
  | cons setNode rest ih =>
      have memberCases : child = setNode ∨ child ∈ rest := by
        simpa using member
      rcases memberCases with head | tail
      · subst child
        let step := StructuralSetting.transition mode setNode value
          "atomic-do-set"
        have stepFixed : FixedAt step.target.record.model setNode value :=
          fixed_after_setting mode setNode value
        simpa [setMode, selected, step] using
          setMode_preserves_fixed step.target action rest setNode value selected
            stepFixed
      · cases setSelected : action setNode with
        | none =>
            simpa [setMode, setSelected] using ih mode tail
        | some setValue =>
            let step := StructuralSetting.transition mode setNode setValue
              "atomic-do-set"
            simpa [setMode, setSelected, step] using ih step.target tail

def insertAction (base : Action S) (target : Fin S.count)
    (value : S.Value target) : Action S :=
  (HardIntervention.set ⟨base⟩ target value).value

/-- Replacing one equation by a constant realizes one atomic hard setting. -/
theorem setting_evalNodeUnder_eq (mode : CausalMode S)
    (target : Fin S.count) (value : S.Value target) (base : Action S)
    (baseNone : base target = none)
    (u : mode.record.model.latent.Assignment) (node : Fin S.count) :
    (StructuralSetting.applyConstant mode.record target value).model.evalNodeUnder
        base u node =
      mode.record.model.evalNodeUnder (insertAction base target value) u node := by
  rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  by_cases same : node = target
  · subst node
    simp [insertAction, HardIntervention.set, baseNone,
      StructuralSetting.mechanism_at_target]
  · cases selected : base node with
    | some current =>
        simp [insertAction, HardIntervention.set, same, selected]
    | none =>
        rw [StructuralSetting.mechanism_at_other mode.record target node value
          same]
        simp [insertAction, HardIntervention.set, same, selected]
        congr 1
        funext parent edge
        exact setting_evalNodeUnder_eq mode target value base baseNone u parent
termination_by node.val
decreasing_by
  exact S.directed_earlier edge

theorem setting_evalUnder_eq (mode : CausalMode S)
    (target : Fin S.count) (value : S.Value target) (base : Action S)
    (baseNone : base target = none)
    (u : mode.record.model.latent.Assignment) :
    (StructuralSetting.applyConstant mode.record target value).model.evalUnder
        base u =
      mode.record.model.evalUnder (insertAction base target value) u := by
  funext node
  exact setting_evalNodeUnder_eq mode target value base baseNone u node

def actionOn (action : Action S) (nodes : List (Fin S.count)) : Action S :=
  fun node => if node ∈ nodes then action node else none

theorem actionOn_all (action : Action S) :
    actionOn action (List.finRange S.count) = action := by
  funext node
  simp [actionOn, List.mem_finRange]

theorem finRange_nodup : forall count, (List.finRange count).Nodup := by
  intro count
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.finRange_succ]
      exact List.nodup_cons.mpr ⟨by
        intro member
        rcases List.mem_map.mp member with ⟨value, _, equal⟩
        have impossible := congrArg Fin.val equal
        simp at impossible,
        List.Pairwise.map Fin.succ (fun left right different equal =>
          different (Fin.ext (Nat.succ.inj (congrArg Fin.val equal)))) ih⟩

/--
Constructive setting-phase semantics.  The dependent pair retains the target
latent assignment that realizes the requested partial action.
-/
noncomputable def setMode_eval_data (mode : CausalMode S) (action : Action S)
    (nodes : List (Fin S.count)) (nodup : nodes.Nodup)
    (u : mode.record.model.latent.Assignment) :
    { targetU : (setMode mode action nodes).record.model.latent.Assignment //
      (setMode mode action nodes).record.model.eval targetU =
        mode.record.model.evalUnder (actionOn action nodes) u } := by
  induction nodes generalizing mode with
  | nil => exact ⟨u, rfl⟩
  | cons child rest ih =>
      have childNotMem : child ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      cases selected : action child with
      | none =>
          have actionsEqual : actionOn action (child :: rest) =
              actionOn action rest := by
            funext node
            by_cases same : node = child
            · subst node
              simp [actionOn, selected, childNotMem]
            · simp [actionOn, same]
          rcases ih mode restNodup u with ⟨targetU, evaluated⟩
          have witness :
              { targetU :
                  (setMode mode action rest).record.model.latent.Assignment //
            (setMode mode action rest).record.model.eval targetU =
              mode.record.model.evalUnder (actionOn action rest) u } :=
            ⟨targetU, evaluated⟩
          rw [setMode, selected, actionsEqual]
          exact witness
      | some value =>
          let step := StructuralSetting.transition mode child value
            "atomic-do-set"
          rcases ih step.target restNodup u with ⟨targetU, tail⟩
          have baseNone : actionOn action rest child = none := by
            simp [actionOn, childNotMem]
          have inserted : insertAction (actionOn action rest) child value =
              actionOn action (child :: rest) := by
            funext node
            by_cases same : node = child
            · subst node
              simp [insertAction, HardIntervention.set, actionOn, selected]
            · simp [insertAction, HardIntervention.set, actionOn, same]
          have head := setting_evalUnder_eq mode child value
            (actionOn action rest) baseNone u
          have evaluated := Eq.trans tail head
          have witness :
              { targetU :
                  (setMode step.target action rest).record.model.latent.Assignment //
            (setMode step.target action rest).record.model.eval targetU =
              mode.record.model.evalUnder
                (insertAction (actionOn action rest) child value) u } :=
            ⟨targetU, evaluated⟩
          rw [setMode, selected, ← inserted]
          simpa only using witness

/-!
### Directed-cut phase

After constant setting, delete every incoming observed-parent edge of each
selected node. The replacement equation remains constant, so the recursive
evaluation proof shows that deleting each now-unused input preserves values.
-/

theorem directedCut_preserves_realizesAction (mode : CausalMode S)
    (action : Action S) (parent child : Fin S.count)
    (value : S.Value child) (selected : action child = some value)
    (fixed : RealizesAction mode action) :
    RealizesAction (cutDirected mode parent child value
      "atomic-do-cut-directed").target
      ((directedCoordinates S parent child).transportAction action) := by
  intro node fixedValue targetSelected
  have sourceSelected : action node = some fixedValue := by
    rw [directedCoordinates_transportAction] at targetSelected
    exact targetSelected
  by_cases same : node = child
  · subst node
    have valuesEqual : fixedValue = value :=
      Option.some.inj (sourceSelected.symm.trans selected)
    subst fixedValue
    exact fixed_after_directed_cut mode parent child value
  · exact fixed_after_directed_cut_other mode parent child node value
      fixedValue same (fixed node fixedValue sourceSelected)

/-- Removing one directed input preserves absence of a compact intervention. -/
theorem directedCut_noActiveIntervention
    (mode : CausalMode S) (parent child : Fin S.count)
    (value : S.Value child) (empty : NoActiveIntervention mode) :
    NoActiveIntervention
      (cutDirected mode parent child value
        "atomic-do-cut-directed").target := by
  intro node
  exact empty node

def directedExecution (mode : CausalMode S) (action : Action S) :
    List (Fin S.count × Fin S.count) -> Execution mode
  | [] => Execution.identity mode
  | (parent, child) :: rest =>
      match action child with
      | none => directedExecution mode action rest
      | some value =>
          let step := cutDirected mode parent child value
            "atomic-do-cut-directed"
          let coordinates := directedCoordinates S parent child
          Execution.prepend step coordinates
            (directedCutRoots mode parent child value
              "atomic-do-cut-directed")
            (directedExecution step.target
              (coordinates.transportAction action) rest)
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-- Every directed-cut worklist preserves absence of a compact intervention. -/
theorem directedExecution_noActiveIntervention
    (mode : CausalMode S) (action : Action S)
    (empty : NoActiveIntervention mode) :
    (pairs : List (Fin S.count × Fin S.count)) ->
      NoActiveIntervention (directedExecution mode action pairs).target
  | [] => by
      rw [directedExecution.eq_1]
      exact empty
  | (parent, child) :: rest => by
      cases selected : action child with
      | none =>
          rw [directedExecution.eq_2, selected]
          exact directedExecution_noActiveIntervention mode action empty rest
      | some value =>
          let step := cutDirected mode parent child value
            "atomic-do-cut-directed"
          let coordinates := directedCoordinates S parent child
          have stepEmpty : NoActiveIntervention step.target :=
            directedCut_noActiveIntervention mode parent child value empty
          rw [directedExecution.eq_2, selected]
          exact directedExecution_noActiveIntervention step.target
            (coordinates.transportAction action) stepEmpty rest
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/--
Constructive directed-cut semantics.  Every cut retains the same latent unit,
and the recursive certificate records that unit at the final endpoint.
-/
noncomputable def directedExecutionDeterministicSemantics
    (mode : CausalMode S) (action : Action S)
    (fixed : RealizesAction mode action) :
    (pairs : List (Fin S.count × Fin S.count)) ->
      Execution.DeterministicRealizesEvaluation
        (directedExecution mode action pairs) mode.record.model.eval
  | [] => by
      simpa only [directedExecution.eq_1] using
        Execution.DeterministicRealizesEvaluation.identity mode
  | (parent, child) :: rest => by
      cases selected : action child with
      | none =>
          simpa only [directedExecution.eq_2, selected] using
            directedExecutionDeterministicSemantics mode action fixed rest
      | some value =>
          let step := cutDirected mode parent child value
            "atomic-do-cut-directed"
          let coordinates := directedCoordinates S parent child
          have sourceFixed : FixedAt mode.record.model child value :=
            fixed child value selected
          have stepFixed := directedCut_preserves_realizesAction mode action
            parent child value selected fixed
          let tailExecution := directedExecution step.target
            (coordinates.transportAction action) rest
          have tailSemantic :=
            directedExecutionDeterministicSemantics step.target
              (coordinates.transportAction action) stepFixed rest
          have stepSemantic : forall assignment :
              mode.record.model.latent.Assignment,
              step.target.record.model.eval assignment =
                coordinates.transportObserved
                  (mode.record.model.eval assignment) := by
            intro assignment
            rw [directedCoordinates_transportObserved]
            exact directed_cut_eval_eq mode parent child value sourceFixed
              assignment
          have composed :=
            Execution.DeterministicRealizesEvaluation.prepend step coordinates
              (directedCutRoots mode parent child value
                "atomic-do-cut-directed")
              tailExecution (fun assignment => assignment) stepSemantic
              tailSemantic
          simpa only [directedExecution.eq_2, selected, step, coordinates] using composed
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-- Existential directed-cut semantics, derived from the constructive certificate. -/
def directedExecutionSemantics (mode : CausalMode S) (action : Action S)
    (fixed : RealizesAction mode action)
    (pairs : List (Fin S.count × Fin S.count)) :
    Execution.Semantics (directedExecution mode action pairs) where
  evaluate :=
    (directedExecutionDeterministicSemantics mode action fixed pairs).toExistential.evaluate

def directedExecutionFixed (mode : CausalMode S) (action : Action S)
    (fixed : RealizesAction mode action) :
    (pairs : List (Fin S.count × Fin S.count)) ->
      RealizesAction (directedExecution mode action pairs).target
        ((directedExecution mode action pairs).transportedAction action)
  | [] => by
      rw [directedExecution.eq_1]
      change RealizesAction mode ((SameCoordinates.refl S).transportAction action)
      intro child value selected
      apply fixed child value
      rw [SameCoordinates.transportAction_refl] at selected
      exact selected
  | (parent, child) :: rest => by
      cases selected : action child with
      | none =>
          rw [directedExecution.eq_2, selected]
          exact directedExecutionFixed mode action fixed rest
      | some value =>
          let step := cutDirected mode parent child value
            "atomic-do-cut-directed"
          let coordinates := directedCoordinates S parent child
          let tailExecution := directedExecution step.target
            (coordinates.transportAction action) rest
          have stepFixed := directedCut_preserves_realizesAction mode action
            parent child value selected fixed
          have tailFixed := directedExecutionFixed step.target
            (coordinates.transportAction action) stepFixed rest
          have actionEq :
              (Execution.prepend step coordinates
                (directedCutRoots mode parent child value
                  "atomic-do-cut-directed") tailExecution).transportedAction
                  action =
                tailExecution.transportedAction
                  (coordinates.transportAction action) := by
            exact (SameCoordinates.transportAction_trans coordinates
              tailExecution.coordinates action).symm
          rw [directedExecution.eq_2, selected]
          dsimp only
          change RealizesAction tailExecution.target
            ((Execution.prepend step coordinates
              (directedCutRoots mode parent child value
                "atomic-do-cut-directed") tailExecution).transportedAction
                action)
          rw [actionEq]
          exact tailFixed
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-- Later directed cuts preserve any directed input already known to be absent. -/
theorem directedExecution_preserves_absent
    (mode : CausalMode S) (action : Action S)
    (parent child : Fin S.count)
    (absent : S.directed parent child = false) :
    (pairs : List (Fin S.count × Fin S.count)) ->
      DirectedInputAbsent (directedExecution mode action pairs) parent child
  | [] => by
      rw [directedExecution.eq_1]
      exact absent
  | (cutParent, cutChild) :: rest => by
      cases selected : action cutChild with
      | none =>
          rw [directedExecution.eq_2, selected]
          exact directedExecution_preserves_absent mode action parent child
            absent rest
      | some value =>
          let step := cutDirected mode cutParent cutChild value
            "atomic-do-cut-directed"
          let coordinates := directedCoordinates S cutParent cutChild
          have stepAbsent :
              (DirectedLink.removeSignature S cutParent cutChild).directed
                (coordinates.nodeEquiv.toFun parent)
                (coordinates.nodeEquiv.toFun child) = false := by
            change (DirectedLink.removeSignature S cutParent cutChild).directed
              parent child = false
            simp [DirectedLink.removeSignature, absent]
          have tailAbsent := directedExecution_preserves_absent step.target
            (coordinates.transportAction action)
            (coordinates.nodeEquiv.toFun parent)
            (coordinates.nodeEquiv.toFun child) stepAbsent rest
          rw [directedExecution.eq_2, selected]
          simpa [DirectedInputAbsent, Execution.prepend,
            SameCoordinates.trans, NodeEquiv.trans, step, coordinates] using
            tailAbsent
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-- Processing a selected pair removes that directed input at the endpoint. -/
theorem directedExecution_removes_member
    (mode : CausalMode S) (action : Action S)
    (parent child : Fin S.count) (value : S.Value child)
    (selected : action child = some value) :
    (pairs : List (Fin S.count × Fin S.count)) ->
      (parent, child) ∈ pairs ->
        DirectedInputAbsent (directedExecution mode action pairs) parent child
  | [], member => by simp at member
  | (cutParent, cutChild) :: rest, member => by
      have memberCases : (parent, child) = (cutParent, cutChild) ∨
          (parent, child) ∈ rest := by
        simpa only [List.mem_cons] using member
      cases cutSelected : action cutChild with
      | none =>
          rcases memberCases with same | tail
          · have childEq : child = cutChild := congrArg Prod.snd same
            subst cutChild
            rw [cutSelected] at selected
            contradiction
          · rw [directedExecution.eq_2, cutSelected]
            exact directedExecution_removes_member mode action parent child
              value selected rest tail
      | some cutValue =>
          let step := cutDirected mode cutParent cutChild cutValue
            "atomic-do-cut-directed"
          let coordinates := directedCoordinates S cutParent cutChild
          let tailExecution := directedExecution step.target
            (coordinates.transportAction action) rest
          have result : DirectedInputAbsent tailExecution
              (coordinates.nodeEquiv.toFun parent)
              (coordinates.nodeEquiv.toFun child) := by
            rcases memberCases with same | tail
            · have parentEq : parent = cutParent := congrArg Prod.fst same
              have childEq : child = cutChild := congrArg Prod.snd same
              subst parent
              subst child
              have stepAbsent :
                  (DirectedLink.removeSignature S cutParent cutChild).directed
                    (coordinates.nodeEquiv.toFun cutParent)
                    (coordinates.nodeEquiv.toFun cutChild) = false := by
                change (DirectedLink.removeSignature S cutParent cutChild).directed
                  cutParent cutChild = false
                exact DirectedLink.removedEdge S cutParent cutChild
              exact directedExecution_preserves_absent step.target
                (coordinates.transportAction action)
                (coordinates.nodeEquiv.toFun cutParent)
                (coordinates.nodeEquiv.toFun cutChild) stepAbsent rest
            · have transportedSelected :
                  (coordinates.transportAction action)
                      (coordinates.nodeEquiv.toFun child) =
                    some (cast (coordinates.value_eq child) value) := by
                change (coordinates.transportAction action) child = some value
                rw [show coordinates = directedCoordinates S cutParent cutChild
                  from rfl, directedCoordinates_transportAction]
                exact selected
              exact directedExecution_removes_member step.target
                (coordinates.transportAction action)
                (coordinates.nodeEquiv.toFun parent)
                (coordinates.nodeEquiv.toFun child)
                (cast (coordinates.value_eq child) value)
                transportedSelected rest tail
          rw [directedExecution.eq_2, cutSelected]
          simpa [DirectedInputAbsent, Execution.prepend,
            SameCoordinates.trans, NodeEquiv.trans, step, coordinates,
            tailExecution] using result
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-!
### Latent-input-cut phase

Finally remove every incoming latent-root incidence into selected nodes. This
is the latent analogue of the directed-cut phase and completes graph surgery:
selected nodes have constant equations with no incoming directed or latent
inputs.
-/

def latentExecution (mode : CausalMode S) (action : Action S)
    : List (Fin mode.record.model.latent.count × Fin S.count) -> Execution mode
  | [] => Execution.identity mode
  | (source, child) :: rest =>
      match action child with
      | none => latentExecution mode action rest
      | some value =>
          let step := cutLatent mode source child value
            "atomic-do-cut-latent"
          Execution.prepend step (SameCoordinates.refl S)
            (latentCutRoots mode source child value
              "atomic-do-cut-latent")
            (latentExecution step.target action rest)
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-- Removing one latent input preserves absence of a compact intervention. -/
theorem latentCut_noActiveIntervention
    (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count)
    (child : Fin S.count) (value : S.Value child)
    (empty : NoActiveIntervention mode) :
    NoActiveIntervention
      (cutLatent mode source child value "atomic-do-cut-latent").target := by
  intro node
  exact empty node

/-- Every latent-cut worklist preserves absence of a compact intervention. -/
theorem latentExecution_noActiveIntervention
    (mode : CausalMode S) (action : Action S)
    (empty : NoActiveIntervention mode) :
    (pairs : List (Fin mode.record.model.latent.count × Fin S.count)) ->
      NoActiveIntervention (latentExecution mode action pairs).target
  | [] => by
      rw [latentExecution.eq_1]
      exact empty
  | (source, child) :: rest => by
      cases selected : action child with
      | none =>
          rw [latentExecution.eq_2, selected]
          exact latentExecution_noActiveIntervention mode action empty rest
      | some value =>
          let step := cutLatent mode source child value
            "atomic-do-cut-latent"
          have stepEmpty : NoActiveIntervention step.target :=
            latentCut_noActiveIntervention mode source child value empty
          rw [latentExecution.eq_2, selected]
          exact latentExecution_noActiveIntervention step.target action stepEmpty rest
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

theorem latentCut_preserves_realizesAction (mode : CausalMode S)
    (action : Action S) (source : Fin mode.record.model.latent.count)
    (child : Fin S.count) (value : S.Value child)
    (selected : action child = some value)
    (fixed : RealizesAction mode action) :
    RealizesAction (cutLatent mode source child value
      "atomic-do-cut-latent").target action := by
  intro node fixedValue targetSelected
  by_cases same : node = child
  · subst node
    have valuesEqual : fixedValue = value :=
      Option.some.inj (targetSelected.symm.trans selected)
    subst fixedValue
    exact fixed_after_latent_cut mode source child value
  · exact fixed_after_latent_cut_other mode source child node value
      fixedValue same (fixed node fixedValue targetSelected)

/--
Constructive latent-cut semantics.  Cutting an incidence retains the same
latent assignment and records it through the remaining edit path.
-/
noncomputable def latentExecutionDeterministicSemantics
    (mode : CausalMode S) (action : Action S)
    (fixed : RealizesAction mode action) :
    (pairs : List (Fin mode.record.model.latent.count × Fin S.count)) ->
      Execution.DeterministicRealizesEvaluation
        (latentExecution mode action pairs) mode.record.model.eval
  | [] => by
      simpa only [latentExecution.eq_1] using
        Execution.DeterministicRealizesEvaluation.identity mode
  | (source, child) :: rest => by
      cases selected : action child with
      | none =>
          simpa only [latentExecution.eq_2, selected] using
            latentExecutionDeterministicSemantics mode action fixed rest
      | some value =>
          let step := cutLatent mode source child value
            "atomic-do-cut-latent"
          let tailExecution := latentExecution step.target action rest
          have sourceFixed : FixedAt mode.record.model child value :=
            fixed child value selected
          have stepFixed := latentCut_preserves_realizesAction mode action
            source child value selected fixed
          have tailSemantic :=
            latentExecutionDeterministicSemantics step.target action stepFixed rest
          have stepSemantic : forall assignment :
              mode.record.model.latent.Assignment,
              step.target.record.model.eval assignment =
                (SameCoordinates.refl S).transportObserved
                  (mode.record.model.eval assignment) := by
            intro assignment
            rw [SameCoordinates.transportObserved_refl]
            exact latent_cut_eval_eq mode source child value sourceFixed assignment
          have composed :=
            Execution.DeterministicRealizesEvaluation.prepend step
              (SameCoordinates.refl S)
              (latentCutRoots mode source child value "atomic-do-cut-latent")
              tailExecution (fun assignment => assignment) stepSemantic
              tailSemantic
          simpa only [latentExecution.eq_2, selected, step, tailExecution] using composed
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-- Existential latent-cut semantics, derived from the constructive certificate. -/
def latentExecutionSemantics (mode : CausalMode S) (action : Action S)
    (fixed : RealizesAction mode action)
    (pairs : List (Fin mode.record.model.latent.count × Fin S.count)) :
    Execution.Semantics (latentExecution mode action pairs) where
  evaluate :=
    (latentExecutionDeterministicSemantics mode action fixed pairs).toExistential.evaluate

/-- Every latent cut preserves the constant equations already installed. -/
def latentExecutionFixed (mode : CausalMode S) (action : Action S)
    (fixed : RealizesAction mode action) :
    (pairs : List (Fin mode.record.model.latent.count × Fin S.count)) ->
      RealizesAction (latentExecution mode action pairs).target
        ((latentExecution mode action pairs).transportedAction action)
  | [] => by
      rw [latentExecution.eq_1]
      change RealizesAction mode ((SameCoordinates.refl S).transportAction action)
      intro child value selected
      apply fixed child value
      rw [SameCoordinates.transportAction_refl] at selected
      exact selected
  | (source, child) :: rest => by
      cases selected : action child with
      | none =>
          rw [latentExecution.eq_2, selected]
          exact latentExecutionFixed mode action fixed rest
      | some value =>
          let step := cutLatent mode source child value
            "atomic-do-cut-latent"
          let coordinates := SameCoordinates.refl S
          let tailExecution := latentExecution step.target action rest
          have stepFixed := latentCut_preserves_realizesAction mode action
            source child value selected fixed
          have tailFixed := latentExecutionFixed step.target action stepFixed rest
          have actionEq :
              (Execution.prepend step coordinates
                (latentCutRoots mode source child value
                  "atomic-do-cut-latent") tailExecution).transportedAction action =
                tailExecution.transportedAction
                  (coordinates.transportAction action) := by
            exact (SameCoordinates.transportAction_trans coordinates
              tailExecution.coordinates action).symm
          have reflAction : coordinates.transportAction action = action := by
            funext node
            exact SameCoordinates.transportAction_refl action node
          rw [latentExecution.eq_2, selected]
          dsimp only
          change RealizesAction tailExecution.target
            ((Execution.prepend step coordinates
              (latentCutRoots mode source child value
                "atomic-do-cut-latent") tailExecution).transportedAction action)
          rw [actionEq, reflAction]
          exact tailFixed
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-- Latent-input cuts leave every absent directed input absent. -/
theorem latentExecution_preserves_directed_absent
    (mode : CausalMode S) (action : Action S)
    (parent child : Fin S.count)
    (absent : S.directed parent child = false) :
    (pairs : List (Fin mode.record.model.latent.count × Fin S.count)) ->
      DirectedInputAbsent (latentExecution mode action pairs) parent child
  | [] => by
      rw [latentExecution.eq_1]
      exact absent
  | (source, cutChild) :: rest => by
      cases selected : action cutChild with
      | none =>
          rw [latentExecution.eq_2, selected]
          exact latentExecution_preserves_directed_absent mode action
            parent child absent rest
      | some value =>
          let step := cutLatent mode source cutChild value
            "atomic-do-cut-latent"
          let coordinates := SameCoordinates.refl S
          have tailAbsent := latentExecution_preserves_directed_absent
            step.target action parent child absent rest
          rw [latentExecution.eq_2, selected]
          simpa [DirectedInputAbsent, Execution.prepend,
            SameCoordinates.trans, NodeEquiv.trans, step, coordinates] using
            tailAbsent
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-- Later latent cuts preserve any latent input already known to be absent. -/
theorem latentExecution_preserves_absent
    (mode : CausalMode S) (action : Action S)
    (source : Fin mode.record.model.latent.count) (child : Fin S.count)
    (absent : mode.record.model.latent.incident source child = false) :
    (pairs : List (Fin mode.record.model.latent.count × Fin S.count)) ->
      LatentInputAbsent (latentExecution mode action pairs) source child
  | [] => by
      rw [latentExecution.eq_1]
      exact absent
  | (cutSource, cutChild) :: rest => by
      cases selected : action cutChild with
      | none =>
          rw [latentExecution.eq_2, selected]
          exact latentExecution_preserves_absent mode action source child
            absent rest
      | some value =>
          let step := cutLatent mode cutSource cutChild value
            "atomic-do-cut-latent"
          let coordinates := SameCoordinates.refl S
          let roots := latentCutRoots mode cutSource cutChild value
            "atomic-do-cut-latent"
          have stepAbsent :
              step.target.record.model.latent.incident
                (roots.rootEquiv.toFun source)
                (coordinates.nodeEquiv.toFun child) = false := by
            change (LatentLink.removeExtension mode.record.model cutSource
              cutChild).incident source child = false
            simp [LatentLink.removeExtension, absent]
          have tailAbsent := latentExecution_preserves_absent step.target action
            (roots.rootEquiv.toFun source)
            (coordinates.nodeEquiv.toFun child) stepAbsent rest
          rw [latentExecution.eq_2, selected]
          simpa [LatentInputAbsent, Execution.prepend, SameRoots.trans,
            FinIndexEquiv.trans, SameCoordinates.trans, NodeEquiv.trans,
            step, roots, coordinates] using tailAbsent
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-- Processing a selected pair removes that latent input at the endpoint. -/
theorem latentExecution_removes_member
    (mode : CausalMode S) (action : Action S)
    (source : Fin mode.record.model.latent.count) (child : Fin S.count)
    (selected : (action child).isSome = true) :
    (pairs : List (Fin mode.record.model.latent.count × Fin S.count)) ->
      (source, child) ∈ pairs ->
        LatentInputAbsent (latentExecution mode action pairs) source child
  | [], member => by simp at member
  | (cutSource, cutChild) :: rest, member => by
      have memberCases : (source, child) = (cutSource, cutChild) ∨
          (source, child) ∈ rest := by
        simpa only [List.mem_cons] using member
      cases cutSelected : action cutChild with
      | none =>
          rcases memberCases with same | tail
          · have childEq : child = cutChild := congrArg Prod.snd same
            subst cutChild
            simp [cutSelected] at selected
          · rw [latentExecution.eq_2, cutSelected]
            exact latentExecution_removes_member mode action source child
              selected rest tail
      | some cutValue =>
          let step := cutLatent mode cutSource cutChild cutValue
            "atomic-do-cut-latent"
          let coordinates := SameCoordinates.refl S
          let roots := latentCutRoots mode cutSource cutChild cutValue
            "atomic-do-cut-latent"
          let tailExecution := latentExecution step.target action rest
          have result : LatentInputAbsent tailExecution
              (roots.rootEquiv.toFun source)
              (coordinates.nodeEquiv.toFun child) := by
            rcases memberCases with same | tail
            · have sourceEq : source = cutSource := congrArg Prod.fst same
              have childEq : child = cutChild := congrArg Prod.snd same
              subst source
              subst child
              have stepAbsent :
                  step.target.record.model.latent.incident
                    (roots.rootEquiv.toFun cutSource)
                    (coordinates.nodeEquiv.toFun cutChild) = false := by
                change (LatentLink.removeExtension mode.record.model cutSource
                  cutChild).incident cutSource cutChild = false
                exact LatentLink.removedIncident mode.record.model cutSource
                  cutChild
              exact latentExecution_preserves_absent step.target action
                (roots.rootEquiv.toFun cutSource)
                (coordinates.nodeEquiv.toFun cutChild) stepAbsent rest
            · exact latentExecution_removes_member step.target action
                (roots.rootEquiv.toFun source)
                (coordinates.nodeEquiv.toFun child) selected rest tail
          rw [latentExecution.eq_2, cutSelected]
          simpa [LatentInputAbsent, Execution.prepend, SameRoots.trans,
            FinIndexEquiv.trans, SameCoordinates.trans, NodeEquiv.trans,
            step, roots, coordinates, tailExecution] using result
termination_by pairs => pairs.length
decreasing_by
  all_goals
    change rest.length < rest.length + 1
    omega

/-- Every observed node, used by the constant-setting phase. -/
def nodeWorklist (S : ObservedSignature) : List (Fin S.count) :=
  List.finRange S.count

/-- Every ordered observed-node pair, used by the directed-cut phase. -/
def directedWorklist (S : ObservedSignature) :
    List (Fin S.count × Fin S.count) :=
  (List.finRange S.count).flatMap fun child =>
    (List.finRange S.count).map fun parent => (parent, child)

/-- Every latent-root/observed-node pair, used by the latent-cut phase. -/
def latentWorklist (mode : CausalMode S) :
    List (Fin mode.record.model.latent.count × Fin S.count) :=
  (List.finRange S.count).flatMap fun child =>
    (List.finRange mode.record.model.latent.count).map fun source =>
      (source, child)

theorem mem_directedWorklist (S : ObservedSignature)
    (parent child : Fin S.count) :
    (parent, child) ∈ directedWorklist S := by
  simp [directedWorklist]

theorem mem_latentWorklist (mode : CausalMode S)
    (source : Fin mode.record.model.latent.count) (child : Fin S.count) :
    (source, child) ∈ latentWorklist mode := by
  simp [latentWorklist]

def setPhase (mode : CausalMode S) (action : Action S) : Execution mode :=
  setExecution mode action (nodeWorklist S)

theorem setPhase_noActiveIntervention
    (mode : CausalMode S) (action : Action S)
    (empty : NoActiveIntervention mode) :
    NoActiveIntervention (setPhase mode action).target :=
  setMode_noActiveIntervention mode action empty (nodeWorklist S)

/--
Constructive setting-phase semantics, retaining the target latent assignment
used by the endpoint probability distribution.
-/
noncomputable def setPhaseDeterministicRealizes
    (mode : CausalMode S) (action : Action S) :
    Execution.DeterministicRealizesEvaluation (setPhase mode action)
      (fun assignment => mode.record.model.evalUnder action assignment) where
  assignment := fun assignment =>
    (setMode_eval_data mode action (nodeWorklist S)
      (finRange_nodup S.count) assignment).1
  evaluate := by
    intro assignment
    change (setMode mode action (nodeWorklist S)).record.model.eval
        _ =
      (SameCoordinates.refl S).transportObserved
        (mode.record.model.evalUnder action assignment)
    simpa [nodeWorklist, actionOn_all] using
      (setMode_eval_data mode action (nodeWorklist S)
        (finRange_nodup S.count) assignment).2

/-- Existential setting semantics, derived from the constructive certificate. -/
def setPhaseRealizes (mode : CausalMode S) (action : Action S) :
    Execution.RealizesEvaluation (setPhase mode action)
      (fun assignment => mode.record.model.evalUnder action assignment) :=
  (setPhaseDeterministicRealizes mode action).toExistential

def setPhaseFixed (mode : CausalMode S) (action : Action S) :
    RealizesAction (setPhase mode action).target
      ((setPhase mode action).transportedAction action) := by
  change RealizesAction
    (setMode mode action (nodeWorklist S))
    ((SameCoordinates.refl S).transportAction action)
  intro child value selected
  rw [SameCoordinates.transportAction_refl] at selected
  exact setMode_fixes_member mode action (nodeWorklist S) child value
    (List.mem_finRange child) selected

def directedPhase (mode : CausalMode S) (action : Action S) :
    Execution (setPhase mode action).target :=
  directedExecution (setPhase mode action).target
    ((setPhase mode action).transportedAction action)
    (directedWorklist S)

theorem directedPhase_noActiveIntervention
    (mode : CausalMode S) (action : Action S)
    (empty : NoActiveIntervention (setPhase mode action).target) :
    NoActiveIntervention (directedPhase mode action).target :=
  directedExecution_noActiveIntervention
    (setPhase mode action).target
    ((setPhase mode action).transportedAction action)
    empty (directedWorklist S)

def directedPhaseSemantics (mode : CausalMode S) (action : Action S) :
    Execution.Semantics (directedPhase mode action) :=
  directedExecutionSemantics (setPhase mode action).target
    ((setPhase mode action).transportedAction action)
    (setPhaseFixed mode action) (directedWorklist S)

noncomputable def directedPhaseDeterministicSemantics
    (mode : CausalMode S) (action : Action S) :
    Execution.DeterministicRealizesEvaluation (directedPhase mode action)
      (setPhase mode action).target.record.model.eval :=
  directedExecutionDeterministicSemantics (setPhase mode action).target
    ((setPhase mode action).transportedAction action)
    (setPhaseFixed mode action) (directedWorklist S)

def directedPhaseFixed (mode : CausalMode S) (action : Action S) :
    RealizesAction (directedPhase mode action).target
      ((directedPhase mode action).transportedAction
        ((setPhase mode action).transportedAction action)) :=
  directedExecutionFixed (setPhase mode action).target
    ((setPhase mode action).transportedAction action)
    (setPhaseFixed mode action) (directedWorklist S)

def setAndDirected (mode : CausalMode S) (action : Action S) : Execution mode :=
  (setPhase mode action).append (directedPhase mode action)

theorem setAndDirected_noActiveIntervention
    (mode : CausalMode S) (action : Action S)
    (empty : NoActiveIntervention mode) :
    NoActiveIntervention (setAndDirected mode action).target :=
  directedPhase_noActiveIntervention mode action
    (setPhase_noActiveIntervention mode action empty)

noncomputable def setAndDirectedDeterministicRealizes
    (mode : CausalMode S) (action : Action S) :
    Execution.DeterministicRealizesEvaluation (setAndDirected mode action)
      (fun assignment => mode.record.model.evalUnder action assignment) :=
  Execution.DeterministicRealizesEvaluation.appendSemantics
    (setPhase mode action) (directedPhase mode action)
    (fun assignment => mode.record.model.evalUnder action assignment)
    (setPhaseDeterministicRealizes mode action)
    (directedPhaseDeterministicSemantics mode action).assignment
    (directedPhaseDeterministicSemantics mode action).evaluate

/-- Existential set-and-cut semantics, derived from the constructive certificate. -/
def setAndDirectedRealizes (mode : CausalMode S) (action : Action S) :
    Execution.RealizesEvaluation (setAndDirected mode action)
      (fun assignment => mode.record.model.evalUnder action assignment) :=
  (setAndDirectedDeterministicRealizes mode action).toExistential

def setAndDirectedFixed (mode : CausalMode S) (action : Action S) :
    RealizesAction (setAndDirected mode action).target
      ((setAndDirected mode action).transportedAction action) := by
  have actionEq : (setAndDirected mode action).transportedAction action =
      (directedPhase mode action).transportedAction
        ((setPhase mode action).transportedAction action) := by
    exact (SameCoordinates.transportAction_trans
      (setPhase mode action).coordinates
      (directedPhase mode action).coordinates action).symm
  rw [actionEq]
  exact directedPhaseFixed mode action

/-- The directed phase removes every incoming observed input of a selected node. -/
theorem setAndDirected_directedRemoved (mode : CausalMode S)
    (action : Action S) (parent child : Fin S.count)
    (value : S.Value child) (selected : action child = some value) :
    DirectedInputAbsent (setAndDirected mode action) parent child := by
  let set := setPhase mode action
  have childSelected : set.transportedAction action child = some value := by
    rw [show set.transportedAction action child = action child from
      SameCoordinates.transportAction_refl action child]
    exact selected
  have phaseAbsent := directedExecution_removes_member set.target
    (set.transportedAction action) parent child value childSelected
    (directedWorklist S) (mem_directedWorklist S parent child)
  simpa [DirectedInputAbsent, setAndDirected, directedPhase, set,
    Execution.append, SameCoordinates.trans, NodeEquiv.trans,
    setPhase, setExecution] using phaseAbsent

def latentPhase (mode : CausalMode S) (action : Action S) :
    Execution (setAndDirected mode action).target :=
  let built := setAndDirected mode action
  latentExecution built.target (built.transportedAction action)
    (latentWorklist built.target)

theorem latentPhase_noActiveIntervention
    (mode : CausalMode S) (action : Action S)
    (empty : NoActiveIntervention (setAndDirected mode action).target) :
    NoActiveIntervention (latentPhase mode action).target :=
  latentExecution_noActiveIntervention
    (setAndDirected mode action).target
    ((setAndDirected mode action).transportedAction action)
    empty (latentWorklist (setAndDirected mode action).target)

def latentPhaseSemantics (mode : CausalMode S) (action : Action S) :
    Execution.Semantics (latentPhase mode action) :=
  latentExecutionSemantics (setAndDirected mode action).target
    ((setAndDirected mode action).transportedAction action)
    (setAndDirectedFixed mode action)
    (latentWorklist (setAndDirected mode action).target)

noncomputable def latentPhaseDeterministicSemantics
    (mode : CausalMode S) (action : Action S) :
    Execution.DeterministicRealizesEvaluation (latentPhase mode action)
      (setAndDirected mode action).target.record.model.eval :=
  latentExecutionDeterministicSemantics (setAndDirected mode action).target
    ((setAndDirected mode action).transportedAction action)
    (setAndDirectedFixed mode action)
    (latentWorklist (setAndDirected mode action).target)

/-- The latent phase preserves every selected constant equation. -/
def latentPhaseFixed (mode : CausalMode S) (action : Action S) :
    RealizesAction (latentPhase mode action).target
      ((latentPhase mode action).transportedAction
        ((setAndDirected mode action).transportedAction action)) :=
  latentExecutionFixed (setAndDirected mode action).target
    ((setAndDirected mode action).transportedAction action)
    (setAndDirectedFixed mode action)
    (latentWorklist (setAndDirected mode action).target)

/--
The finite `do` program: structurally set every selected equation, then remove
every directed and latent input into those selected nodes one at a time.
-/
def compile (mode : CausalMode S) (action : Action S) : Execution mode :=
  (setAndDirected mode action).append (latentPhase mode action)

/-- Atomic compilation preserves an initially empty compact intervention. -/
theorem compile_noActiveIntervention
    (mode : CausalMode S) (action : Action S)
    (empty : NoActiveIntervention mode) :
    NoActiveIntervention (compile mode action).target :=
  latentPhase_noActiveIntervention mode action
    (setAndDirected_noActiveIntervention mode action empty)

/--
The fully compiled atomic intervention, with a constructive endpoint assignment
for every source latent unit.
-/
noncomputable def compileDeterministicRealizes
    (mode : CausalMode S) (action : Action S) :
    Execution.DeterministicRealizesEvaluation (compile mode action)
      (fun assignment => mode.record.model.evalUnder action assignment) :=
  Execution.DeterministicRealizesEvaluation.appendSemantics
    (setAndDirected mode action) (latentPhase mode action)
    (fun assignment => mode.record.model.evalUnder action assignment)
    (setAndDirectedDeterministicRealizes mode action)
    (latentPhaseDeterministicSemantics mode action).assignment
    (latentPhaseDeterministicSemantics mode action).evaluate

/--
The atomically compiled path has the compact hard-intervention semantics. This
existential view is projected from `compileDeterministicRealizes`.
-/
def compileRealizes (mode : CausalMode S) (action : Action S) :
    Execution.RealizesEvaluation (compile mode action)
      (fun assignment => mode.record.model.evalUnder action assignment) :=
  (compileDeterministicRealizes mode action).toExistential

/-- Every selected equation remains constant through the complete compilation. -/
def compileFixed (mode : CausalMode S) (action : Action S) :
    RealizesAction (compile mode action).target
      ((compile mode action).transportedAction action) := by
  have actionEq : (compile mode action).transportedAction action =
      (latentPhase mode action).transportedAction
        ((setAndDirected mode action).transportedAction action) := by
    exact (SameCoordinates.transportAction_trans
      (setAndDirected mode action).coordinates
      (latentPhase mode action).coordinates action).symm
  rw [actionEq]
  exact latentPhaseFixed mode action

/-- Every directed input into a selected node is absent at the compiled endpoint. -/
theorem compile_directedRemoved (mode : CausalMode S) (action : Action S)
    (parent child : Fin S.count) (value : S.Value child)
    (selected : action child = some value) :
    (compile mode action).signature.directed
        ((compile mode action).coordinates.nodeEquiv.toFun parent)
        ((compile mode action).coordinates.nodeEquiv.toFun child) = false := by
  let built := setAndDirected mode action
  have builtAbsent := setAndDirected_directedRemoved mode action parent child
    value selected
  have phaseAbsent := latentExecution_preserves_directed_absent built.target
    (built.transportedAction action)
    (built.coordinates.nodeEquiv.toFun parent)
    (built.coordinates.nodeEquiv.toFun child) builtAbsent
    (latentWorklist built.target)
  simpa [DirectedInputAbsent, compile, latentPhase, built, Execution.append,
    SameCoordinates.trans, NodeEquiv.trans] using phaseAbsent

/-- Every latent input into a selected node is absent at the compiled endpoint. -/
theorem compile_latentRemoved (mode : CausalMode S) (action : Action S)
    (source : Fin mode.record.model.latent.count) (child : Fin S.count)
    (value : S.Value child) (selected : action child = some value) :
    (compile mode action).target.record.model.latent.incident
        ((compile mode action).roots.rootEquiv.toFun source)
        ((compile mode action).coordinates.nodeEquiv.toFun child) = false := by
  let built := setAndDirected mode action
  have builtSelected :
      ((built.transportedAction action)
        (built.coordinates.nodeEquiv.toFun child)).isSome = true := by
    change (built.coordinates.transportAction action
      (built.coordinates.nodeEquiv.toFun child)).isSome = true
    rw [SameCoordinates.transportAction_isSome_toFun]
    simp [selected]
  have phaseAbsent := latentExecution_removes_member built.target
    (built.transportedAction action)
    (built.roots.rootEquiv.toFun source)
    (built.coordinates.nodeEquiv.toFun child) builtSelected
    (latentWorklist built.target)
    (mem_latentWorklist built.target
      (built.roots.rootEquiv.toFun source)
      (built.coordinates.nodeEquiv.toFun child))
  simpa [LatentInputAbsent, compile, latentPhase, built, Execution.append,
    SameRoots.trans, FinIndexEquiv.trans, SameCoordinates.trans,
    NodeEquiv.trans] using phaseAbsent

/--
The structural certificate for the atomic finite `do` compiler. At the
transported endpoint, each selected mechanism is constant at its transported
chosen value and has no incoming directed or latent inputs.
-/
structure Plan (mode : CausalMode S) (action : Action S) : Prop where
  fixed : RealizesAction (compile mode action).target
    ((compile mode action).transportedAction action)
  directedRemoved : forall parent child value,
    action child = some value ->
      (compile mode action).signature.directed
        ((compile mode action).coordinates.nodeEquiv.toFun parent)
        ((compile mode action).coordinates.nodeEquiv.toFun child) = false
  latentRemoved : forall source child value,
    action child = some value ->
      (compile mode action).target.record.model.latent.incident
        ((compile mode action).roots.rootEquiv.toFun source)
        ((compile mode action).coordinates.nodeEquiv.toFun child) = false

/-- Atomic compilation satisfies its complete structural certificate. -/
def plan (mode : CausalMode S) (action : Action S) : Plan mode action where
  fixed := compileFixed mode action
  directedRemoved := compile_directedRemoved mode action
  latentRemoved := compile_latentRemoved mode action

/--
For an initially empty compact intervention, atomic compilation supplies the
absorption evidence required by certified endpoint clearing.
-/
noncomputable def compileEndpointInterventionAbsorbed
    (mode : CausalMode S) (action : Action S)
    (empty : NoActiveIntervention mode) :
    Execution.DeterministicRealizesEvaluation.EndpointInterventionAbsorbed
      (compileDeterministicRealizes mode action) :=
  Execution.DeterministicRealizesEvaluation.EndpointInterventionAbsorbed.ofEmpty
    (compileDeterministicRealizes mode action)
    (compile_noActiveIntervention mode action empty)

def target (mode : CausalMode S) (action : Action S) :=
  (compile mode action).target

def path (mode : CausalMode S) (action : Action S) :
    CausalEditPath mode (target mode action) :=
  (compile mode action).path

end AtomicIntervention

end Causality
end Thesis
