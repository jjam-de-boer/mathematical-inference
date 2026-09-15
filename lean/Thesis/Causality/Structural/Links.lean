import Thesis.Causality.ConservativeLearning

namespace Thesis
namespace Causality

open Probability

/-! Atomic mechanism replacement and directed or latent causal linkage. -/

/-! ## Atomic structural mechanism replacement -/

namespace StructuralSetting

/-- Replace one structural equation while retaining its declared inputs. -/
structure Operation (R : CausalEpistemicRecord S)
    (target : Fin S.count) where
  replacement : S.ParentValues target ->
    R.model.latent.Inputs target -> S.Value target

namespace Operation

def apply {S : ObservedSignature} {R : CausalEpistemicRecord S}
    {target : Fin S.count} (operation : Operation R target) :
    CausalEpistemicRecord S where
  model :=
    { latent := R.model.latent
      factor := R.model.factor
      prior := R.model.prior
      product_law := R.model.product_law
      mechanism := by
        intro child parents latents
        by_cases selected : child = target
        · subst child
          exact operation.replacement parents latents
        · exact R.model.mechanism child parents latents }
  belief := R.belief
  intervention := R.intervention
  stack := R.executedStack .replaceMechanism

end Operation

/-- The atomic structural counterpart of setting one variable to a value. -/
def constantOperation {S : ObservedSignature} (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) : Operation R target where
  replacement := fun _ _ => value

def applyConstant {S : ObservedSignature} (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    CausalEpistemicRecord S :=
  (constantOperation R target value).apply

@[simp] theorem mechanism_at_target {S : ObservedSignature}
    (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target)
    (parents : S.ParentValues target)
    (latents : R.model.latent.Inputs target) :
    (applyConstant R target value).model.mechanism target parents latents =
      value := by
  simp [applyConstant, constantOperation, Operation.apply]

theorem mechanism_at_other {S : ObservedSignature}
    (R : CausalEpistemicRecord S)
    (target child : Fin S.count) (value : S.Value target)
    (different : child ≠ target) (parents : S.ParentValues child)
    (latents : R.model.latent.Inputs child) :
    (applyConstant R target value).model.mechanism child parents latents =
      R.model.mechanism child parents latents := by
  unfold applyConstant constantOperation Operation.apply
  dsimp
  split
  · rename_i equal
    exact (different equal).elim
  · rfl

theorem evalNode_at_target {S : ObservedSignature}
    (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target)
    (u : R.model.latent.Assignment) :
    (applyConstant R target value).model.eval u target = value := by
  change (applyConstant R target value).model.evalNodeUnder
    (FiniteLatentSCM.noIntervention S) u target = value
  rw [FiniteLatentSCM.evalNodeUnder]
  simp [FiniteLatentSCM.equationUnder, FiniteLatentSCM.noIntervention,
    mechanism_at_target]

end StructuralSetting

/-! ## Whole-mechanism-family replacement -/

namespace StructuralMechanismReplacement

/--
Typed replacement data for the entire structural-equation family. The
exogenous model, current belief and accumulated intervention are retained.
-/
structure Operation (R : CausalEpistemicRecord S) where
  replacement : (child : Fin S.count) ->
    S.ParentValues child -> R.model.latent.Inputs child -> S.Value child

namespace Operation

def apply {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (operation : Operation R) : CausalEpistemicRecord S where
  model :=
    { latent := R.model.latent
      factor := R.model.factor
      prior := R.model.prior
      product_law := R.model.product_law
      mechanism := operation.replacement }
  belief := R.belief
  intervention := R.intervention
  stack := R.executedStack .replaceMechanism

@[simp] theorem apply_model_mechanism
    {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (operation : Operation R)
    (child : Fin S.count) (parents : S.ParentValues child)
    (latents : R.model.latent.Inputs child) :
    operation.apply.model.mechanism child parents latents =
      operation.replacement child parents latents :=
  rfl

end Operation

end StructuralMechanismReplacement

namespace DirectedLink

/-- Add one rank-respecting permitted endogenous input. -/
def addSignature (S : ObservedSignature) (parent child : Fin S.count)
    (earlier : parent.val < child.val) : ObservedSignature where
  count := S.count
  Value := S.Value
  valueEnumeration := S.valueEnumeration
  value_complete := S.value_complete
  value_nodup := S.value_nodup
  defaultValue := S.defaultValue
  valueDecidableEq := S.valueDecidableEq
  directed := fun candidateParent candidateChild =>
    S.directed candidateParent candidateChild ||
      (decide (candidateParent = parent) && decide (candidateChild = child))
  directed_earlier := by
    intro candidateParent candidateChild edge
    simp only [Bool.or_eq_true] at edge
    rcases edge with oldEdge | newEdge
    · exact S.directed_earlier oldEdge
    · have parts := Bool.and_eq_true_iff.mp newEdge
      have parentEq : candidateParent = parent := by simpa using parts.1
      have childEq : candidateChild = child := by simpa using parts.2
      simpa [parentEq, childEq] using earlier

@[simp] theorem addSignature_count (S : ObservedSignature)
    (parent child : Fin S.count) (earlier : parent.val < child.val) :
    (addSignature S parent child earlier).count = S.count :=
  rfl

@[simp] theorem addSignature_value (S : ObservedSignature)
    (parent child : Fin S.count) (earlier : parent.val < child.val)
    (node : Fin S.count) :
    (addSignature S parent child earlier).Value node = S.Value node :=
  rfl

theorem oldEdge (S : ObservedSignature) (parent child : Fin S.count)
    (earlier : parent.val < child.val) {left right : Fin S.count}
    (edge : S.directed left right = true) :
    (addSignature S parent child earlier).directed left right = true := by
  simp [addSignature, edge]

theorem addedEdge (S : ObservedSignature) (parent child : Fin S.count)
    (earlier : parent.val < child.val) :
    (addSignature S parent child earlier).directed parent child = true := by
  simp [addSignature]

/-- Reindex the unchanged latent roots over the signature with one new edge. -/
def addLatent (M : ExactModel S) (parent child : Fin S.count)
    (earlier : parent.val < child.val) :
    LatentExtension (addSignature S parent child earlier) where
  count := M.latent.count
  Value := M.latent.Value
  valueEnumeration := M.latent.valueEnumeration
  value_complete := M.latent.value_complete
  valueDecidableEq := M.latent.valueDecidableEq
  incident := M.latent.incident

/-- Data needed to make the newly permitted parent input semantically explicit. -/
structure RelateOperation (S : ObservedSignature)
    (parent child : Fin S.count) (earlier : parent.val < child.val) where
  replacement : (M : ExactModel S) ->
    (addSignature S parent child earlier).ParentValues child ->
    (addLatent M parent child earlier).Inputs child ->
    (addSignature S parent child earlier).Value child

namespace RelateOperation

def liftIntervention (intervention : HardIntervention S) :
    HardIntervention (addSignature S parent child earlier) where
  value := intervention.value

/-- Execute directed relating while preserving every unaffected mechanism. -/
def model (operation : RelateOperation S parent child earlier)
    (M : ExactModel S) : ExactModel (addSignature S parent child earlier) where
  latent := addLatent M parent child earlier
  factor := M.factor
  prior := M.prior
  product_law := M.product_law
  mechanism := by
    intro node parents latents
    by_cases selected : node = child
    · subst node
      exact operation.replacement M parents latents
    · exact M.mechanism node
        (fun candidate oldEdge =>
          parents candidate
            (DirectedLink.oldEdge S parent child earlier oldEdge))
        latents

/-- Execute the edit on an epistemic state, carrying belief and intervention. -/
def apply (operation : RelateOperation S parent child earlier)
    (R : CausalEpistemicRecord S) :
    CausalEpistemicRecord (addSignature S parent child earlier) where
  model := operation.model R.model
  belief := R.belief
  intervention := liftIntervention R.intervention
  stack := R.acrossStack .relateDirected

end RelateOperation

/-- Remove one declared endogenous input; acyclicity is inherited. -/
def removeSignature (S : ObservedSignature) (parent child : Fin S.count) :
    ObservedSignature where
  count := S.count
  Value := S.Value
  valueEnumeration := S.valueEnumeration
  value_complete := S.value_complete
  value_nodup := S.value_nodup
  defaultValue := S.defaultValue
  valueDecidableEq := S.valueDecidableEq
  directed := fun candidateParent candidateChild =>
    S.directed candidateParent candidateChild &&
      !(decide (candidateParent = parent) && decide (candidateChild = child))
  directed_earlier := by
    intro candidateParent candidateChild edge
    exact S.directed_earlier (Bool.and_eq_true_iff.mp edge).1

theorem removedEdge (S : ObservedSignature) (parent child : Fin S.count) :
    (removeSignature S parent child).directed parent child = false := by
  simp [removeSignature]

theorem remainingEdge (S : ObservedSignature) (parent child : Fin S.count)
    {candidateParent candidateChild : Fin S.count}
    (differentChild : candidateChild ≠ child)
    (edge : S.directed candidateParent candidateChild = true) :
    (removeSignature S parent child).directed
      candidateParent candidateChild = true := by
  simp [removeSignature, edge, differentChild]

/-- Reindex unchanged latent roots over a signature with one edge removed. -/
def removeLatent (M : ExactModel S) (parent child : Fin S.count) :
    LatentExtension (removeSignature S parent child) where
  count := M.latent.count
  Value := M.latent.Value
  valueEnumeration := M.latent.valueEnumeration
  value_complete := M.latent.value_complete
  valueDecidableEq := M.latent.valueDecidableEq
  incident := M.latent.incident

/-- Removing a parent requires an equation that no longer receives that input. -/
structure UnrelateOperation (S : ObservedSignature)
    (parent child : Fin S.count) where
  replacement : (M : ExactModel S) ->
    (removeSignature S parent child).ParentValues child ->
    (removeLatent M parent child).Inputs child ->
    (removeSignature S parent child).Value child

namespace UnrelateOperation

def liftIntervention (intervention : HardIntervention S) :
    HardIntervention (removeSignature S parent child) where
  value := intervention.value

def apply (operation : UnrelateOperation S parent child)
    (R : CausalEpistemicRecord S) :
    CausalEpistemicRecord (removeSignature S parent child) where
  model :=
    { latent := removeLatent R.model parent child
      factor := R.model.factor
      prior := R.model.prior
      product_law := R.model.product_law
      mechanism := by
        intro node parents latents
        by_cases selected : node = child
        · subst node
          exact operation.replacement R.model parents latents
        · exact R.model.mechanism node
            (fun candidate oldEdge =>
              parents candidate
                (DirectedLink.remainingEdge S parent child selected oldEdge))
            latents }
  belief := R.belief
  intervention := liftIntervention R.intervention
  stack := R.acrossStack .unrelateDirected

end UnrelateOperation

end DirectedLink

namespace LatentLink

/-- Add one exogenous input declaration to an existing endogenous mechanism. -/
def addExtension (M : ExactModel S) (source : Fin M.latent.count)
    (child : Fin S.count) : LatentExtension S where
  count := M.latent.count
  Value := M.latent.Value
  valueEnumeration := M.latent.valueEnumeration
  value_complete := M.latent.value_complete
  valueDecidableEq := M.latent.valueDecidableEq
  incident := fun candidateSource candidateChild =>
    M.latent.incident candidateSource candidateChild ||
      (decide (candidateSource = source) && decide (candidateChild = child))

theorem oldIncident (M : ExactModel S) (source : Fin M.latent.count)
    (child : Fin S.count) {candidateSource : Fin M.latent.count}
    {candidateChild : Fin S.count}
    (incident : M.latent.incident candidateSource candidateChild = true) :
    (addExtension M source child).incident candidateSource candidateChild = true := by
  simp [addExtension, incident]

theorem addedIncident (M : ExactModel S) (source : Fin M.latent.count)
    (child : Fin S.count) :
    (addExtension M source child).incident source child = true := by
  simp [addExtension]

structure RelateOperation (R : CausalEpistemicRecord S)
    (source : Fin R.model.latent.count) (child : Fin S.count) where
  replacement :
    S.ParentValues child ->
    (addExtension R.model source child).Inputs child -> S.Value child

namespace RelateOperation

def apply {S : ObservedSignature} {R : CausalEpistemicRecord S}
    {source : Fin R.model.latent.count} {child : Fin S.count}
    (operation : RelateOperation R source child) :
    CausalEpistemicRecord S where
  model :=
    { latent := addExtension R.model source child
      factor := R.model.factor
      prior := R.model.prior
      product_law := R.model.product_law
      mechanism := by
        intro node parents latents
        by_cases selected : node = child
        · subst node
          exact operation.replacement parents latents
        · exact R.model.mechanism node parents
            (fun candidate oldIncident =>
              latents candidate
                (LatentLink.oldIncident R.model source child oldIncident)) }
  belief := R.belief
  intervention := R.intervention
  stack := R.executedStack .relateLatent

end RelateOperation

/-- Remove one exogenous input declaration. -/
def removeExtension (M : ExactModel S) (source : Fin M.latent.count)
    (child : Fin S.count) : LatentExtension S where
  count := M.latent.count
  Value := M.latent.Value
  valueEnumeration := M.latent.valueEnumeration
  value_complete := M.latent.value_complete
  valueDecidableEq := M.latent.valueDecidableEq
  incident := fun candidateSource candidateChild =>
    M.latent.incident candidateSource candidateChild &&
      !(decide (candidateSource = source) && decide (candidateChild = child))

theorem removedIncident (M : ExactModel S) (source : Fin M.latent.count)
    (child : Fin S.count) :
    (removeExtension M source child).incident source child = false := by
  simp [removeExtension]

theorem remainingIncident (M : ExactModel S)
    (source : Fin M.latent.count) (child : Fin S.count)
    {candidateSource : Fin M.latent.count} {candidateChild : Fin S.count}
    (differentChild : candidateChild ≠ child)
    (incident : M.latent.incident candidateSource candidateChild = true) :
    (removeExtension M source child).incident
      candidateSource candidateChild = true := by
  simp [removeExtension, incident, differentChild]

structure UnrelateOperation (R : CausalEpistemicRecord S)
    (source : Fin R.model.latent.count) (child : Fin S.count) where
  replacement :
    S.ParentValues child ->
    (removeExtension R.model source child).Inputs child -> S.Value child

namespace UnrelateOperation

def apply {S : ObservedSignature} {R : CausalEpistemicRecord S}
    {source : Fin R.model.latent.count} {child : Fin S.count}
    (operation : UnrelateOperation R source child) :
    CausalEpistemicRecord S where
  model :=
    { latent := removeExtension R.model source child
      factor := R.model.factor
      prior := R.model.prior
      product_law := R.model.product_law
      mechanism := by
        intro node parents latents
        by_cases selected : node = child
        · subst node
          exact operation.replacement parents latents
        · exact R.model.mechanism node parents
            (fun candidate oldIncident =>
              latents candidate
                (LatentLink.remainingIncident R.model source child
                  selected oldIncident)) }
  belief := R.belief
  intervention := R.intervention
  stack := R.executedStack .unrelateLatent

end UnrelateOperation

end LatentLink

end Causality
end Thesis
