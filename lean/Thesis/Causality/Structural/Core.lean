import Thesis.Causality.Structural.Links
import Thesis.Causality.Structural.Learning
import Thesis.Causality.Structural.SurgeryCore
import Thesis.Causality.Forgetting.ObservedSink
import Thesis.Causality.Forgetting.ExogenousRoot

namespace Thesis
namespace Causality

open Probability

/-!
Proof-carrying structural edits for causal epistemic modes.

The executable operation changes the record.  The transition is the modal
separator that records its source, target, and realization proof.  Directed
and latent links are the two constructors of one causal `relate` family; no
second metadata graph is maintained.

This module is the public composition layer for structural edits. The
lower-level data transformations are defined in `Links`, `Learning`, and
`SurgeryCore`. Their composition here gives every public edit the same
`CausalEditOperation` and `CausalEditTransition` interface.
-/

inductive CausalLinkKind where
  | directed
  | latentInput
  deriving DecidableEq, Repr

/-- Typed coordinates for directed and latent-input causal links. -/
inductive CausalLink (R : CausalEpistemicRecord S) where
  | directed (parent child : Fin S.count)
      (earlier : parent.val < child.val)
  | latentInput (source : Fin R.model.latent.count)
      (child : Fin S.count)

/-- Context-independent markers for structural transitions. Learning and
forgetting use one label each; their typed operation constructors retain the
endogenous or exogenous data that realizes the announced edit. -/
inductive CausalEditLabel where
  | conditioning
  | compactSetting
  | compactUnsetting
  | unsetting
  | learning
  | forgetting
  | relating (kind : CausalLinkKind)
  | unrelating (kind : CausalLinkKind)
  | settingMechanism
  | replacingMechanism
  | reindexingBelief
  | surgicalIntervention
  deriving DecidableEq, Repr

namespace BeliefReindexing

inductive InterventionPolicy where
  | preserve
  | clear
  deriving DecidableEq, Repr

/--
Low-level data for pushing an arbitrary finite belief through a latent-coordinate
map while retaining the current SCM. Public causal edits use
`CertifiedOperation`, which restricts the origin and certifies endpoint
evaluation.
-/
structure Operation (R : CausalEpistemicRecord S) where
  Origin : Type
  originBelief : FiniteProbRecord Origin
  assignment : Origin -> R.model.latent.Assignment
  interventionPolicy : InterventionPolicy

namespace Operation

def apply {S : ObservedSignature} {R : CausalEpistemicRecord S}
    (operation : Operation R) : CausalEpistemicRecord S where
  model := R.model
  belief := operation.originBelief.map operation.assignment
  intervention :=
    match operation.interventionPolicy with
    | .preserve => R.intervention
    | .clear => HardIntervention.empty S
  stack := R.executedStack .reindexBelief

end Operation

/--
The two causally meaningful origins of a reindexed finite belief.  The
distribution is not supplied independently: it is either the current belief of
an explicit epistemic record or the prior of an explicit SCM.
-/
inductive Origin (O : ObservedSignature.{0}) where
  | current (record : CausalEpistemicRecord O)
  | prior (model : ExactModel O)

namespace Origin

def model : Origin O -> ExactModel O
  | .current record => record.model
  | .prior model => model

def belief (origin : Origin O) :
    FiniteProbRecord origin.model.latent.Assignment :=
  match origin with
  | .current record => record.belief
  | .prior model => model.prior

end Origin

/--
Certified intervention handling for a public causal belief-reindexing edit.
Both policies carry the intended endpoint evaluator. Preservation proves it
under the retained override. Clearing additionally proves that the retained
override has already been absorbed by the target structural equations before
it is removed.
-/
inductive CertifiedInterventionPolicy
    {S O : ObservedSignature.{0}} (R : CausalEpistemicRecord S)
    (origin : Origin O)
    (assignment :
      origin.model.latent.Assignment -> R.model.latent.Assignment)
    (reference : origin.model.latent.Assignment -> S.Assignment) : Type 1 where
  | preserve
      (realization : forall originAssignment,
        R.model.evalUnder R.intervention.value
            (assignment originAssignment) =
          reference originAssignment) :
      CertifiedInterventionPolicy R origin assignment reference
  | clear
      (absorbed : forall originAssignment,
        R.model.evalUnder R.intervention.value
            (assignment originAssignment) =
          R.model.eval (assignment originAssignment))
      (structuralRealization : forall originAssignment,
        R.model.eval (assignment originAssignment) =
          reference originAssignment) :
      CertifiedInterventionPolicy R origin assignment reference

namespace CertifiedInterventionPolicy

def toRaw :
    CertifiedInterventionPolicy R origin assignment reference ->
      InterventionPolicy
  | .preserve _ => .preserve
  | .clear _ _ => .clear

end CertifiedInterventionPolicy

/--
A provenance-carrying belief reindexing admitted by the public causal-edit
family.  Its origin distribution is derived from a causal record or SCM rather
than accepted as arbitrary finite data.
-/
structure CertifiedOperation {S : ObservedSignature.{0}}
    (R : CausalEpistemicRecord S) where
  OriginSignature : ObservedSignature.{0}
  origin : Origin OriginSignature
  assignment :
    origin.model.latent.Assignment -> R.model.latent.Assignment
  reference : origin.model.latent.Assignment -> S.Assignment
  interventionPolicy :
    CertifiedInterventionPolicy R origin assignment reference

namespace CertifiedOperation

def toOperation {S : ObservedSignature.{0}} {R : CausalEpistemicRecord S}
    (operation : CertifiedOperation R) : Operation R where
  Origin := operation.origin.model.latent.Assignment
  originBelief := operation.origin.belief
  assignment := operation.assignment
  interventionPolicy := operation.interventionPolicy.toRaw

def apply {S : ObservedSignature.{0}} {R : CausalEpistemicRecord S}
    (operation : CertifiedOperation R) : CausalEpistemicRecord S :=
  operation.toOperation.apply

@[simp] theorem apply_model {S : ObservedSignature.{0}}
    {R : CausalEpistemicRecord S} (operation : CertifiedOperation R) :
    operation.apply.model = R.model :=
  rfl

@[simp] theorem apply_belief {S : ObservedSignature.{0}}
    {R : CausalEpistemicRecord S} (operation : CertifiedOperation R) :
    operation.apply.belief =
      operation.origin.belief.map operation.assignment :=
  rfl

/-- The certified coordinate map evaluates as its declared endpoint evaluator. -/
theorem apply_realizes {S : ObservedSignature.{0}}
    {R : CausalEpistemicRecord S} (operation : CertifiedOperation R)
    (originAssignment : operation.origin.model.latent.Assignment) :
    operation.apply.model.evalUnder operation.apply.intervention.value
        (operation.assignment originAssignment) =
      operation.reference originAssignment := by
  cases operation with
  | mk OriginSignature origin assignment reference interventionPolicy =>
      cases interventionPolicy with
      | preserve realization =>
          exact realization originAssignment
      | clear _ structuralRealization =>
          exact structuralRealization originAssignment

/--
Applying a certified reindexing does not change the endpoint evaluator on any
transported origin assignment. In the clearing case this is the direct
before/after semantic equality required to show that the override was already
absorbed structurally.
-/
theorem apply_preserves_evaluation {S : ObservedSignature.{0}}
    {R : CausalEpistemicRecord S} (operation : CertifiedOperation R)
    (originAssignment : operation.origin.model.latent.Assignment) :
    R.model.evalUnder R.intervention.value
        (operation.assignment originAssignment) =
      operation.apply.model.evalUnder operation.apply.intervention.value
        (operation.assignment originAssignment) := by
  cases operation with
  | mk OriginSignature origin assignment reference interventionPolicy =>
      cases interventionPolicy with
      | preserve _ => rfl
      | clear absorbed _ =>
          exact absorbed originAssignment

/--
The declared reference evaluator is already the source record's evaluator on
the certified coordinate map, before either preserving or clearing the
intervention field.
-/
theorem source_realizes_reference {S : ObservedSignature.{0}}
    {R : CausalEpistemicRecord S} (operation : CertifiedOperation R)
    (originAssignment : operation.origin.model.latent.Assignment) :
    R.model.evalUnder R.intervention.value
        (operation.assignment originAssignment) =
      operation.reference originAssignment :=
  Eq.trans
    (operation.apply_preserves_evaluation originAssignment)
    (operation.apply_realizes originAssignment)

end CertifiedOperation

end BeliefReindexing

/--
One closed family of intrinsically specified causal edits. Every constructor
carries the operation-specific input data, and `result` computes the target
record from that data and the indexed source. No constructor accepts an
arbitrary target record.
-/
inductive CausalEditOperation :
    {S : ObservedSignature} -> CausalEpistemicRecord S ->
      (T : ObservedSignature) -> Type 1
  | conditioning {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (evidence : source.model.latent.Assignment -> Bool)
      (hEvidence : source.belief.EventPositive evidence) :
      CausalEditOperation source S
  | compactSetting {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (target : Fin S.count) (value : S.Value target) :
      CausalEditOperation source S
  | compactIntervening {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (nodes : NodeSet S) (reference : S.Assignment) :
      CausalEditOperation source S
  | compactUnsetting {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (target : Fin S.count) : CausalEditOperation source S
  | unsetting {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (target : Fin S.count)
      (h : source.UnsetReady target) : CausalEditOperation source S
  | observing {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (nodes : NodeSet S) (reference : S.Assignment)
      (hEvidence : source.belief.EventPositive
        (source.nodeObservationEvidence nodes reference)) :
      CausalEditOperation source S
  | learningTerminal {S : ObservedSignature}
      {source : CausalEpistemicRecord S} (spec : TerminalVariableSpec S) :
      CausalEditOperation source spec.extendSignature
  | forgettingTerminal {S : ObservedSignature}
      (original : CausalEpistemicRecord S) (spec : TerminalVariableSpec S) :
      CausalEditOperation (spec.learnRecord original) S
  | learningEndogenous {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (spec : EndogenousVariableSpec source) :
      CausalEditOperation source spec.extendSignature
  | forgettingEndogenous {S : ObservedSignature}
      (original : CausalEpistemicRecord S)
      (spec : EndogenousVariableSpec original) :
      CausalEditOperation spec.learnRecord S
  | forgettingUnusedEndogenous {S : ObservedSignature}
      {source : CausalEpistemicRecord S} (spec : ObservedDeletionSpec S) :
      CausalEditOperation source spec.signature
  | learningExogenous {S : ObservedSignature}
      {source : CausalEpistemicRecord S} (spec : ExogenousVariableSpec) :
      CausalEditOperation source S
  | forgettingExogenous {S : ObservedSignature}
      (original : CausalEpistemicRecord S) (spec : ExogenousVariableSpec) :
      CausalEditOperation (spec.learnRecord original) S
  | forgettingUnusedExogenous {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (spec : ExogenousDeletionSpec source.model) :
      CausalEditOperation source S
  | relatingDirected {S : ObservedSignature}
      {source : CausalEpistemicRecord S} {parent child : Fin S.count}
      {earlier : parent.val < child.val}
      (operation : DirectedLink.RelateOperation S parent child earlier) :
      CausalEditOperation source
        (DirectedLink.addSignature S parent child earlier)
  | unrelatingDirected {S : ObservedSignature}
      {source : CausalEpistemicRecord S} {parent child : Fin S.count}
      (operation : DirectedLink.UnrelateOperation S parent child) :
      CausalEditOperation source (DirectedLink.removeSignature S parent child)
  | relatingLatent {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      {latentSource : Fin source.model.latent.count} {child : Fin S.count}
      (operation : LatentLink.RelateOperation source latentSource child) :
      CausalEditOperation source S
  | unrelatingLatent {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      {latentSource : Fin source.model.latent.count} {child : Fin S.count}
      (operation : LatentLink.UnrelateOperation source latentSource child) :
      CausalEditOperation source S
  | settingMechanism {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (target : Fin S.count) (value : S.Value target) :
      CausalEditOperation source S
  | replacingMechanismAt {S : ObservedSignature}
      {source : CausalEpistemicRecord S} {target : Fin S.count}
      (operation : StructuralSetting.Operation source target) :
      CausalEditOperation source S
  | replacingMechanisms {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (operation : StructuralMechanismReplacement.Operation source) :
      CausalEditOperation source S
  | reindexingBelief {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (operation : BeliefReindexing.CertifiedOperation source) :
      CausalEditOperation source S
  | surgicalIntervention {S : ObservedSignature}
      {source : CausalEpistemicRecord S}
      (action : (node : Fin S.count) -> Option (S.Value node)) :
      CausalEditOperation source
        (SurgicalIntervention.signature source.model action)

namespace CausalEditOperation

def result : CausalEditOperation source T -> CausalEpistemicRecord T
  | .conditioning evidence hEvidence =>
      source.conditionLatent evidence hEvidence
  | .compactSetting target value => source.setVariable target value
  | .compactIntervening nodes reference =>
      source.interveneNodes nodes reference
  | .compactUnsetting target => source.clearVariable target
  | .unsetting target h => source.unsetVariable target h
  | .observing nodes reference hEvidence =>
      source.observeNodes nodes reference hEvidence
  | .learningTerminal spec => spec.learnRecord source
  | .forgettingTerminal original _ => original
  | .learningEndogenous spec => spec.learnRecord
  | .forgettingEndogenous original _ => original
  | .forgettingUnusedEndogenous spec => spec.deleteRecord source
  | .learningExogenous spec => spec.learnRecord source
  | .forgettingExogenous original _ => original
  | .forgettingUnusedExogenous spec => spec.deleteRecord
  | .relatingDirected operation => operation.apply source
  | .unrelatingDirected operation => operation.apply source
  | .relatingLatent operation => operation.apply
  | .unrelatingLatent operation => operation.apply
  | .settingMechanism target value =>
      StructuralSetting.applyConstant source target value
  | .replacingMechanismAt operation => operation.apply
  | .replacingMechanisms operation => operation.apply
  | .reindexingBelief operation => operation.apply
  | .surgicalIntervention action =>
      SurgicalIntervention.apply source action

def label : CausalEditOperation source T -> CausalEditLabel
  | .conditioning _ _ => .conditioning
  | .compactSetting _ _ => .compactSetting
  | .compactIntervening _ _ => .compactSetting
  | .compactUnsetting _ => .compactUnsetting
  | .unsetting _ _ => .unsetting
  | .observing _ _ _ => .conditioning
  | .learningTerminal _
  | .learningEndogenous _
  | .learningExogenous _ => .learning
  | .forgettingTerminal _ _
  | .forgettingEndogenous _ _
  | .forgettingExogenous _ _
  | .forgettingUnusedEndogenous _
  | .forgettingUnusedExogenous _ => .forgetting
  | .relatingDirected _ => .relating .directed
  | .unrelatingDirected _ => .unrelating .directed
  | .relatingLatent _ => .relating .latentInput
  | .unrelatingLatent _ => .unrelating .latentInput
  | .settingMechanism _ _ => .settingMechanism
  | .replacingMechanismAt _
  | .replacingMechanisms _ => .replacingMechanism
  | .reindexingBelief _ => .reindexingBelief
  | .surgicalIntervention _ => .surgicalIntervention

/-- Intrinsic edit corresponding to one fixed-signature record step. -/
def ofRecordStep
    {S : ObservedSignature} {source target : CausalEpistemicRecord S}
    {fixedLabel : CausalTransitionLabel}
    (step : CausalRecordStep fixedLabel source target) :
    CausalEditOperation source S :=
  match step with
  | .conditioning _ evidence hEvidence => .conditioning evidence hEvidence
  | .observing _ nodes reference hEvidence =>
      .observing nodes reference hEvidence
  | .setting _ selected value => .compactSetting selected value
  | .intervening _ nodes reference => .compactIntervening nodes reference
  | .unsetting _ selected h => .unsetting selected h

@[simp] theorem ofRecordStep_result
    {S : ObservedSignature} {source target : CausalEpistemicRecord S}
    {fixedLabel : CausalTransitionLabel}
    (step : CausalRecordStep fixedLabel source target) :
    (ofRecordStep step).result = target := by
  cases step <;> rfl

end CausalEditOperation

/-- A modality-indexed, proof-carrying causal record edit. -/
structure CausalEditTransition (S T : ObservedSignature) where
  source : CausalMode S
  target : CausalMode T
  operation : CausalEditOperation source.record T
  realized : target.record = operation.result

namespace CausalEditTransition

/-- The operation constructor is the unique source of a transition's label. -/
def label (transition : CausalEditTransition S T) : CausalEditLabel :=
  transition.operation.label

/-- View a fixed-signature epistemic transition as a structural edit step. -/
def ofCausalTransition (transition : CausalTransition S) :
    CausalEditTransition S S where
  source := transition.source
  target := transition.target
  operation := CausalEditOperation.ofRecordStep transition.valid
  realized := (CausalEditOperation.ofRecordStep_result transition.valid).symm

/-- Conservative terminal learning in the unified edit family. -/
def learnTerminal (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (targetName : String) :
    CausalEditTransition S spec.extendSignature where
  source := mode
  target := mode.learnTerminal spec targetName
  operation := .learningTerminal spec
  realized := rfl

/--
Forget exactly the terminal extension recorded by `learnTerminal`.  The source
mode and specification provide the provenance required for genuine deletion.
-/
def forgetTerminal (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (learnedName targetName : String) :
    CausalEditTransition spec.extendSignature S where
  source := mode.learnTerminal spec learnedName
  target := { name := targetName, record := mode.record }
  operation := .forgettingTerminal mode.record spec
  realized := rfl

@[simp] theorem learnTerminal_target_record
    (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (targetName : String) :
    (learnTerminal mode spec targetName).target.record =
      spec.learnRecord mode.record :=
  rfl

@[simp] theorem forgetTerminal_target_record
    (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (learnedName targetName : String) :
    (forgetTerminal mode spec learnedName targetName).target.record =
      mode.record :=
  rfl

/-- Learning followed by its provenance-guided forgetting restores the record. -/
theorem learn_forget_record_roundTrip
    (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (learnedName targetName : String) :
    (forgetTerminal mode spec learnedName targetName).target.record =
      mode.record :=
  rfl

/-- Old current-belief events are invariant across terminal learning. -/
theorem learnTerminal_observedValue_old
    (mode : CausalMode S) (spec : TerminalVariableSpec S)
    (targetName : String) (event : S.Assignment -> Bool) :
    QProb.Equiv
      ((learnTerminal mode spec targetName).target.record.observedValue
        (spec.liftEvent event))
      (mode.record.observedValue event) :=
  spec.learnRecord_observedValue_old mode.record event

end CausalEditTransition

namespace StructuralSetting

namespace Operation

def transition {S : ObservedSignature} (mode : CausalMode S)
    (target : Fin S.count)
    (operation : Operation mode.record target) (targetName : String) :
    CausalEditTransition S S where
  source := mode
  target := ⟨targetName, operation.apply⟩
  operation := .replacingMechanismAt operation
  realized := rfl

end Operation

def transition {S : ObservedSignature} (mode : CausalMode S)
    (target : Fin S.count)
    (value : S.Value target) (targetName : String) :
    CausalEditTransition S S where
  source := mode
  target := ⟨targetName, applyConstant mode.record target value⟩
  operation := .settingMechanism target value
  realized := rfl

end StructuralSetting

namespace StructuralMechanismReplacement
namespace Operation

def transition {S : ObservedSignature} (mode : CausalMode S)
    (operation : Operation mode.record) (targetName : String) :
    CausalEditTransition S S where
  source := mode
  target := ⟨targetName, operation.apply⟩
  operation := .replacingMechanisms operation
  realized := rfl

end Operation
end StructuralMechanismReplacement

namespace BeliefReindexing
namespace CertifiedOperation

def transition {S : ObservedSignature} (mode : CausalMode S)
    (operation : CertifiedOperation mode.record) (targetName : String) :
    CausalEditTransition S S where
  source := mode
  target := ⟨targetName, operation.apply⟩
  operation := .reindexingBelief operation
  realized := rfl

end CertifiedOperation
end BeliefReindexing

namespace DirectedLink

namespace RelateOperation

def transition (operation : RelateOperation S parent child earlier)
    (mode : CausalMode S) (targetName : String) :
    CausalEditTransition S (addSignature S parent child earlier) where
  source := mode
  target := ⟨targetName, operation.apply mode.record⟩
  operation := .relatingDirected operation
  realized := rfl

end RelateOperation

namespace UnrelateOperation

def transition (operation : UnrelateOperation S parent child)
    (mode : CausalMode S) (targetName : String) :
    CausalEditTransition S (removeSignature S parent child) where
  source := mode
  target := ⟨targetName, operation.apply mode.record⟩
  operation := .unrelatingDirected operation
  realized := rfl

end UnrelateOperation

end DirectedLink

namespace LatentLink

namespace RelateOperation

def transition {S : ObservedSignature} (mode : CausalMode S)
    {source : Fin mode.record.model.latent.count} {child : Fin S.count}
    (operation : RelateOperation mode.record source child)
    (targetName : String) :
    CausalEditTransition S S where
  source := mode
  target := ⟨targetName, operation.apply⟩
  operation := .relatingLatent operation
  realized := rfl

end RelateOperation

namespace UnrelateOperation

def transition {S : ObservedSignature} (mode : CausalMode S)
    {source : Fin mode.record.model.latent.count} {child : Fin S.count}
    (operation : UnrelateOperation mode.record source child)
    (targetName : String) :
    CausalEditTransition S S where
  source := mode
  target := ⟨targetName, operation.apply⟩
  operation := .unrelatingLatent operation
  realized := rfl

end UnrelateOperation

end LatentLink

namespace EndogenousVariableSpec

def learnTransition {S : ObservedSignature} (mode : CausalMode S)
    (spec : EndogenousVariableSpec mode.record) (targetName : String) :
    CausalEditTransition S spec.extendSignature where
  source := mode
  target := ⟨targetName, spec.learnRecord⟩
  operation := .learningEndogenous spec
  realized := rfl

/-- Forget exactly the terminal node produced by the corresponding learning edit. -/
def forgetTransition {S : ObservedSignature} (mode : CausalMode S)
    (spec : EndogenousVariableSpec mode.record)
    (learnedName targetName : String) :
    CausalEditTransition spec.extendSignature S where
  source := (learnTransition mode spec learnedName).target
  target := ⟨targetName, mode.record⟩
  operation := .forgettingEndogenous mode.record spec
  realized := rfl

/-- Forget any directed sink, not only a node carrying learning provenance. -/
def forgetUnusedTransition {S : ObservedSignature} (mode : CausalMode S)
    (spec : ObservedDeletionSpec S) (targetName : String) :
    CausalEditTransition S spec.signature where
  source := mode
  target := ⟨targetName, spec.deleteRecord mode.record⟩
  operation := .forgettingUnusedEndogenous spec
  realized := rfl

@[simp] theorem learn_forget_record_roundTrip
    {S : ObservedSignature} (mode : CausalMode S)
    (spec : EndogenousVariableSpec mode.record)
    (learnedName targetName : String) :
    (forgetTransition mode spec learnedName targetName).target.record =
      mode.record :=
  rfl

end EndogenousVariableSpec

namespace ExogenousVariableSpec

def learnTransition (spec : ExogenousVariableSpec) (mode : CausalMode S)
    (targetName : String) : CausalEditTransition S S where
  source := mode
  target := ⟨targetName, spec.learnRecord mode.record⟩
  operation := .learningExogenous spec
  realized := rfl

/-- Forget exactly the fresh root produced by this learning operation. -/
def forgetTransition (spec : ExogenousVariableSpec) (mode : CausalMode S)
    (learnedName targetName : String) : CausalEditTransition S S where
  source := (spec.learnTransition mode learnedName).target
  target := ⟨targetName, mode.record⟩
  operation := .forgettingExogenous mode.record spec
  realized := rfl

/-- Forget any latent root unused by every observed mechanism. -/
def forgetUnusedTransition (mode : CausalMode S)
    (spec : ExogenousDeletionSpec mode.record.model) (targetName : String) :
    CausalEditTransition S S where
  source := mode
  target := ⟨targetName, spec.deleteRecord⟩
  operation := .forgettingUnusedExogenous spec
  realized := rfl

@[simp] theorem learn_forget_record_roundTrip
    (spec : ExogenousVariableSpec) (mode : CausalMode S)
    (learnedName targetName : String) :
    (spec.forgetTransition mode learnedName targetName).target.record =
      mode.record :=
  rfl

end ExogenousVariableSpec

namespace SurgicalIntervention

def transition (mode : CausalMode S)
    (action : (node : Fin S.count) -> Option (S.Value node))
    (targetName : String) :
    CausalEditTransition S (signature mode.record.model action) where
  source := mode
  target := ⟨targetName, apply mode.record action⟩
  operation := .surgicalIntervention action
  realized := rfl

end SurgicalIntervention

/--
A composable sequence of executable causal edits.  Signatures may change at
every step, so the endpoints are indexed by their actual dependent modes.
-/
inductive CausalEditPath :
    {S : ObservedSignature} -> CausalMode S ->
      {T : ObservedSignature} -> CausalMode T -> Type 1
  | nil (mode : CausalMode S) : CausalEditPath mode mode
  | cons (transition : CausalEditTransition S T)
      (rest : CausalEditPath transition.target target) :
      CausalEditPath transition.source target

namespace CausalEditPath

def single (transition : CausalEditTransition S T) :
    CausalEditPath transition.source transition.target :=
  .cons transition (.nil transition.target)

def append (first : CausalEditPath source middle)
    (second : CausalEditPath middle target) :
    CausalEditPath source target :=
  match first with
  | .nil _ => second
  | .cons transition rest => .cons transition (append rest second)

@[simp] theorem nil_append (path : CausalEditPath source target) :
    append (.nil source) path = path :=
  rfl

@[simp] theorem append_nil (path : CausalEditPath source target) :
    append path (.nil target) = path := by
  induction path with
  | nil => rfl
  | cons transition rest ih => simp [append, ih]

theorem append_assoc (first : CausalEditPath source middle)
    (second : CausalEditPath middle later)
    (third : CausalEditPath later target) :
    append (append first second) third =
      append first (append second third) := by
  induction first with
  | nil => rfl
  | cons transition rest ih => simp [append, ih]

def labels : CausalEditPath source target -> List CausalEditLabel
  | .nil _ => []
  | .cons transition rest => transition.label :: labels rest

end CausalEditPath

end Causality
end Thesis
