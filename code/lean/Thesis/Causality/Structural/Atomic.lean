import Thesis.Causality.Structural.Core

namespace Thesis
namespace Causality

open Probability

/-!
Atomic compilation primitives for finite hard interventions.

Constant-setting and directed or latent cuts live here. Coordinate transport,
execution traces, and endpoint semantics are in `AtomicExecution`.
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

end AtomicIntervention

end Causality
end Thesis
