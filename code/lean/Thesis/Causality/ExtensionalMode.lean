import Thesis.Causality.Structural

namespace Thesis
namespace Causality

open Probability
open AtomicIntervention

/-!
Public finished modes are an SCM together with a current latent belief.
`CausalEpistemicRecord` remains the workspace: compact `do` and the modal
stack live there, and inverse *operations of a record* (`UnsetReady`,
`uncondition` as a method of the target) are not methods of this object.

`act` is a wrap `project ∘ op ∘ embed`, not a second copy of the edit
payloads. Public 1-cells are existing `CausalEditOperation` constructors
that preserve an empty compact intervention. Compact `set` / `intervene` /
`unset` are workspace-only. Inverse 1-cells are Hom data: a workspace path
starting at the Hom's target record, or the stored source after surgery.
-/

/--
A finished epistemic mode: generative SCM plus current latent law.
The compact intervention and modal stack of the workspace record are not
part of this object.
-/
structure ExtensionalMode (S : ObservedSignature) where
  model : ExactModel S
  belief : FiniteProbRecord model.latent.Assignment

namespace ExtensionalMode

def extensionalName : String :=
  "extensional"

/-- Workspace representative: empty compact `do`, nil stack. -/
def embed (m : ExtensionalMode S) : CausalMode S where
  name := extensionalName
  record :=
    { model := m.model
      belief := m.belief
      intervention := HardIntervention.empty S
      stack := .nil }

/-- Record-level counterpart of `AtomicIntervention.NoActiveIntervention`. -/
def noActive (R : CausalEpistemicRecord S) : Prop :=
  forall child, R.intervention.value child = none

theorem noActive_iff (mode : CausalMode S) :
    noActive mode.record ↔ NoActiveIntervention mode :=
  Iff.rfl

/-- Forget the stack. Defined only when compact `do` is empty. -/
def project (R : CausalEpistemicRecord S) (_h : noActive R) :
    ExtensionalMode S where
  model := R.model
  belief := R.belief

@[simp] theorem embed_noActive (m : ExtensionalMode S) :
    noActive (embed m).record := by
  intro child
  rfl

@[simp] theorem embed_NoActiveIntervention (m : ExtensionalMode S) :
    NoActiveIntervention (embed m) :=
  embed_noActive m

@[simp] theorem project_embed (m : ExtensionalMode S) :
    project (embed m).record (embed_noActive m) = m :=
  rfl

/-- `embed` of an uninformed mode is the usual initial record. -/
@[simp] theorem embed_initial (model : ExactModel S) :
    (embed ⟨model, model.prior⟩).record =
      CausalEpistemicRecord.initial model :=
  rfl

theorem noActive_intervention_eq (R : CausalEpistemicRecord S)
    (h : noActive R) :
    R.intervention.value = FiniteLatentSCM.noIntervention S := by
  funext child
  exact h child

/-- Probability of an observed event; no sticky compact `do`. -/
def observedValue (m : ExtensionalMode S)
    (event : S.Assignment -> Bool) : QProb :=
  (m.belief.map m.model.eval).probVal event

theorem observedValue_eq_record (R : CausalEpistemicRecord S)
    (h : noActive R) (event : S.Assignment -> Bool) :
    QProb.Equiv (observedValue (project R h) event) (R.observedValue event) := by
  have interventionEq := noActive_intervention_eq R h
  change QProb.Equiv
    ((R.belief.map R.model.eval).probVal event)
    ((R.belief.map (R.model.evalUnder R.intervention.value)).probVal event)
  rw [interventionEq]
  exact QProb.equiv_refl _

/--
Run an existing workspace edit on `embed m` and read the finished mode.
This is not a new modality table: `op` is a `CausalEditOperation`.
-/
def act (m : ExtensionalMode S)
    (op : CausalEditOperation (embed m).record T)
    (h : noActive op.result) : ExtensionalMode T :=
  project op.result h

/-! ## Empty-`do` preservation for public constructors -/

theorem conditioning_noActive (m : ExtensionalMode S)
    (evidence : m.model.latent.Assignment -> Bool)
    (hEvidence : m.belief.EventPositive evidence) :
    noActive
      (CausalEditOperation.conditioning (source := (embed m).record)
        evidence hEvidence).result :=
  embed_noActive m

theorem observing_noActive (m : ExtensionalMode S) (nodes : NodeSet S)
    (reference : S.Assignment)
    (hEvidence : m.belief.EventPositive
      ((embed m).record.nodeObservationEvidence nodes reference)) :
    noActive
      (CausalEditOperation.observing (source := (embed m).record)
        nodes reference hEvidence).result :=
  embed_noActive m

theorem surgicalIntervention_noActive (m : ExtensionalMode S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    noActive
      (CausalEditOperation.surgicalIntervention
        (source := (embed m).record) action).result := by
  intro child
  rfl

theorem settingMechanism_noActive (m : ExtensionalMode S)
    (target : Fin S.count) (value : S.Value target) :
    noActive
      (CausalEditOperation.settingMechanism (source := (embed m).record)
        target value).result :=
  embed_noActive m

theorem replacingMechanismAt_noActive (m : ExtensionalMode S)
    {target : Fin S.count}
    (operation : StructuralSetting.Operation (embed m).record target) :
    noActive
      (CausalEditOperation.replacingMechanismAt (source := (embed m).record)
        operation).result :=
  embed_noActive m

theorem replacingMechanisms_noActive (m : ExtensionalMode S)
    (operation : StructuralMechanismReplacement.Operation (embed m).record) :
    noActive
      (CausalEditOperation.replacingMechanisms (source := (embed m).record)
        operation).result :=
  mechanismReplacement_noActiveIntervention (embed m) operation
    extensionalName (embed_NoActiveIntervention m)

theorem reindexingBelief_noActive (m : ExtensionalMode.{0} S)
    (operation : BeliefReindexing.CertifiedOperation (embed m).record) :
    noActive
      (CausalEditOperation.reindexingBelief (source := (embed m).record)
        operation).result :=
  beliefReindexing_noActiveIntervention (embed m) operation
    extensionalName (embed_NoActiveIntervention m)

theorem learningTerminal_noActive (m : ExtensionalMode S)
    (spec : TerminalVariableSpec S) :
    noActive
      (CausalEditOperation.learningTerminal (source := (embed m).record)
        spec).result := by
  intro child
  refine TerminalVariableSpec.terminalCases
    (motive := fun child =>
      (spec.learnRecord (embed m).record).intervention.value child = none)
    ?_ (fun old => ?_) child
  · simp [TerminalVariableSpec.learnRecord, TerminalVariableSpec.liftIntervention]
  · simp [TerminalVariableSpec.learnRecord, TerminalVariableSpec.liftIntervention,
      embed_noActive m old]

theorem learningEndogenous_noActive (m : ExtensionalMode S)
    (spec : EndogenousVariableSpec (embed m).record) :
    noActive
      (CausalEditOperation.learningEndogenous spec).result :=
  endogenousLearning_noActiveIntervention (embed m) spec extensionalName
    (embed_NoActiveIntervention m)

theorem learningExogenous_noActive (m : ExtensionalMode S)
    (spec : ExogenousVariableSpec) :
    noActive
      (CausalEditOperation.learningExogenous (source := (embed m).record)
        spec).result :=
  exogenousLearning_noActiveIntervention (embed m) spec extensionalName
    (embed_NoActiveIntervention m)

theorem forgettingUnusedEndogenous_noActive (m : ExtensionalMode S)
    (spec : ObservedDeletionSpec S) :
    noActive
      (CausalEditOperation.forgettingUnusedEndogenous
        (source := (embed m).record) spec).result := by
  intro child
  exact embed_noActive m
    (CausalEpistemicRecord.selectedEmbed spec.retained child)

theorem forgettingUnusedExogenous_noActive (m : ExtensionalMode S)
    (spec : ExogenousDeletionSpec (embed m).record.model) :
    noActive
      (CausalEditOperation.forgettingUnusedExogenous
        (source := (embed m).record) spec).result :=
  embed_noActive m

theorem relatingDirected_noActive (m : ExtensionalMode S)
    {parent child : Fin S.count} {earlier : parent.val < child.val}
    (operation : DirectedLink.RelateOperation S parent child earlier) :
    noActive
      (CausalEditOperation.relatingDirected (source := (embed m).record)
        operation).result :=
  directedRelating_noActiveIntervention (embed m) parent child earlier
    operation extensionalName (embed_NoActiveIntervention m)

theorem unrelatingDirected_noActive (m : ExtensionalMode S)
    {parent child : Fin S.count}
    (operation : DirectedLink.UnrelateOperation S parent child) :
    noActive
      (CausalEditOperation.unrelatingDirected (source := (embed m).record)
        operation).result :=
  embed_noActive m

theorem relatingLatent_noActive (m : ExtensionalMode S)
    {source : Fin (embed m).record.model.latent.count} {child : Fin S.count}
    (operation : LatentLink.RelateOperation (embed m).record source child) :
    noActive
      (CausalEditOperation.relatingLatent operation).result :=
  latentRelating_noActiveIntervention (embed m) (source := source)
    (child := child) operation extensionalName
    (embed_NoActiveIntervention m)

theorem unrelatingLatent_noActive (m : ExtensionalMode S)
    {source : Fin (embed m).record.model.latent.count} {child : Fin S.count}
    (operation : LatentLink.UnrelateOperation (embed m).record source child) :
    noActive
      (CausalEditOperation.unrelatingLatent operation).result :=
  embed_noActive m

/-! ## Public 1-cells as `act` abbreviations -/

def conditioning (m : ExtensionalMode S)
    (evidence : m.model.latent.Assignment -> Bool)
    (hEvidence : m.belief.EventPositive evidence) : ExtensionalMode S :=
  act m (.conditioning evidence hEvidence)
    (conditioning_noActive m evidence hEvidence)

def observing (m : ExtensionalMode S) (nodes : NodeSet S)
    (reference : S.Assignment)
    (hEvidence : m.belief.EventPositive
      ((embed m).record.nodeObservationEvidence nodes reference)) :
    ExtensionalMode S :=
  act m (.observing nodes reference hEvidence)
    (observing_noActive m nodes reference hEvidence)

def surgicalIntervention (m : ExtensionalMode S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    ExtensionalMode (SurgicalIntervention.signature m.model action) :=
  act m (.surgicalIntervention action)
    (surgicalIntervention_noActive m action)

def settingMechanism (m : ExtensionalMode S) (target : Fin S.count)
    (value : S.Value target) : ExtensionalMode S :=
  act m (.settingMechanism target value)
    (settingMechanism_noActive m target value)

def replacingMechanismAt (m : ExtensionalMode S) {target : Fin S.count}
    (operation : StructuralSetting.Operation (embed m).record target) :
    ExtensionalMode S :=
  act m (.replacingMechanismAt operation)
    (replacingMechanismAt_noActive m operation)

def replacingMechanisms (m : ExtensionalMode S)
    (operation : StructuralMechanismReplacement.Operation (embed m).record) :
    ExtensionalMode S :=
  act m (.replacingMechanisms operation)
    (replacingMechanisms_noActive m operation)

def reindexingBelief (m : ExtensionalMode.{0} S)
    (operation : BeliefReindexing.CertifiedOperation (embed m).record) :
    ExtensionalMode S :=
  act m (.reindexingBelief operation)
    (reindexingBelief_noActive m operation)

def learningTerminal (m : ExtensionalMode S)
    (spec : TerminalVariableSpec S) :
    ExtensionalMode spec.extendSignature :=
  act m (.learningTerminal spec) (learningTerminal_noActive m spec)

def learningEndogenous (m : ExtensionalMode S)
    (spec : EndogenousVariableSpec (embed m).record) :
    ExtensionalMode spec.extendSignature :=
  act m (.learningEndogenous spec) (learningEndogenous_noActive m spec)

def learningExogenous (m : ExtensionalMode S)
    (spec : ExogenousVariableSpec) : ExtensionalMode S :=
  act m (.learningExogenous spec) (learningExogenous_noActive m spec)

def forgettingUnusedEndogenous (m : ExtensionalMode S)
    (spec : ObservedDeletionSpec S) : ExtensionalMode spec.signature :=
  act m (.forgettingUnusedEndogenous spec)
    (forgettingUnusedEndogenous_noActive m spec)

def forgettingUnusedExogenous (m : ExtensionalMode S)
    (spec : ExogenousDeletionSpec (embed m).record.model) :
    ExtensionalMode S :=
  act m (.forgettingUnusedExogenous spec)
    (forgettingUnusedExogenous_noActive m spec)

def relatingDirected (m : ExtensionalMode S)
    {parent child : Fin S.count} {earlier : parent.val < child.val}
    (operation : DirectedLink.RelateOperation S parent child earlier) :
    ExtensionalMode (DirectedLink.addSignature S parent child earlier) :=
  act m (.relatingDirected operation)
    (relatingDirected_noActive m operation)

def unrelatingDirected (m : ExtensionalMode S)
    {parent child : Fin S.count}
    (operation : DirectedLink.UnrelateOperation S parent child) :
    ExtensionalMode (DirectedLink.removeSignature S parent child) :=
  act m (.unrelatingDirected operation)
    (unrelatingDirected_noActive m operation)

def relatingLatent (m : ExtensionalMode S)
    {source : Fin (embed m).record.model.latent.count} {child : Fin S.count}
    (operation : LatentLink.RelateOperation (embed m).record source child) :
    ExtensionalMode S :=
  act m (.relatingLatent operation) (relatingLatent_noActive m operation)

def unrelatingLatent (m : ExtensionalMode S)
    {source : Fin (embed m).record.model.latent.count} {child : Fin S.count}
    (operation : LatentLink.UnrelateOperation (embed m).record source child) :
    ExtensionalMode S :=
  act m (.unrelatingLatent operation) (unrelatingLatent_noActive m operation)

/-! ## Hom: existing paths with canonical endpoints -/

/--
A public 1-cell. The workspace path may write stack frames; the target must
have empty compact `do`, and `project` of that target is `n`.
-/
structure Hom (m : ExtensionalMode S) (n : ExtensionalMode T) where
  target : CausalMode T
  empty : NoActiveIntervention target
  projected : project target.record empty = n
  path : CausalEditPath (embed m) target

/-- Wrap a single existing operation whose result is already compact-`do` free. -/
def Hom.ofOperation (m : ExtensionalMode S)
    (op : CausalEditOperation (embed m).record T)
    (h : noActive op.result) : Hom m (act m op h) where
  target := ⟨extensionalName, op.result⟩
  empty := h
  projected := rfl
  path :=
    CausalEditPath.single
      { source := embed m
        target := ⟨extensionalName, op.result⟩
        operation := op
        realized := rfl }

/--
Inverse 1-cell of a public Hom. The workspace walk starts at `μ.target`,
not at `embed n`. Surgical `do` stores the source mode. Same-signature
`uncondition` is a separate witness: it is not a `CausalEditOperation`.
-/
inductive Inverse {S T : ObservedSignature}
    {m : ExtensionalMode S} {n : ExtensionalMode T} :
    Hom m n -> Type 1
  | workspacePath {μ : Hom m n}
      (path : CausalEditPath μ.target (embed m)) : Inverse μ
  | storedSource {μ : Hom m n} : Inverse μ

/--
Inverse 1-cell for observe/condition. Restoration uses the workspace
`uncondition` of `μ.target`, not an operation of `embed n`.
-/
structure UnconditionInverse {S : ObservedSignature}
    {m n : ExtensionalMode S} (μ : Hom m n) where
  ready : μ.target.record.UnconditionReady
  roundtrip : μ.target.record.uncondition ready = (embed m).record

/-! ### Observe / condition inverses via workspace `uncondition` -/

theorem observeNodes_UnconditionReady (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment)
    (hEvidence : R.belief.EventPositive
      (R.nodeObservationEvidence nodes reference)) :
    (R.observeNodes nodes reference hEvidence).UnconditionReady := by
  simp [CausalEpistemicRecord.observeNodes,
    CausalEpistemicRecord.UnconditionReady, CausalEpistemicRecord.executedStack,
    ModalStack.unconditionReady]

theorem observeNodes_uncondition (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment)
    (hEvidence : R.belief.EventPositive
      (R.nodeObservationEvidence nodes reference)) :
    (R.observeNodes nodes reference hEvidence).uncondition
      (observeNodes_UnconditionReady R nodes reference hEvidence) = R := by
  cases R
  simp [CausalEpistemicRecord.observeNodes,
    CausalEpistemicRecord.uncondition, CausalEpistemicRecord.announce,
    CausalEpistemicRecord.commitPearl, CausalEpistemicRecord.baseOfCommit,
    CausalEpistemicRecord.executedStack, CausalEpistemicRecord.restoreTop]

theorem conditionLatent_UnconditionReady (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    (R.conditionLatent evidence hEvidence).UnconditionReady := by
  simp [CausalEpistemicRecord.conditionLatent,
    CausalEpistemicRecord.UnconditionReady, CausalEpistemicRecord.executedStack,
    ModalStack.unconditionReady]

theorem conditionLatent_uncondition (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    (R.conditionLatent evidence hEvidence).uncondition
      (conditionLatent_UnconditionReady R evidence hEvidence) = R := by
  cases R
  simp [CausalEpistemicRecord.conditionLatent,
    CausalEpistemicRecord.uncondition, CausalEpistemicRecord.announce,
    CausalEpistemicRecord.commitPearl, CausalEpistemicRecord.baseOfCommit,
    CausalEpistemicRecord.executedStack, CausalEpistemicRecord.restoreTop]

def observingHom (m : ExtensionalMode S) (nodes : NodeSet S)
    (reference : S.Assignment)
    (hEvidence : m.belief.EventPositive
      ((embed m).record.nodeObservationEvidence nodes reference)) :
    Hom m (observing m nodes reference hEvidence) :=
  Hom.ofOperation m (.observing nodes reference hEvidence)
    (observing_noActive m nodes reference hEvidence)

def observingInverse (m : ExtensionalMode S) (nodes : NodeSet S)
    (reference : S.Assignment)
    (hEvidence : m.belief.EventPositive
      ((embed m).record.nodeObservationEvidence nodes reference)) :
    UnconditionInverse (observingHom m nodes reference hEvidence) where
  ready :=
    observeNodes_UnconditionReady (embed m).record nodes reference
      hEvidence
  roundtrip :=
    observeNodes_uncondition (embed m).record nodes reference hEvidence

def conditioningHom (m : ExtensionalMode S)
    (evidence : m.model.latent.Assignment -> Bool)
    (hEvidence : m.belief.EventPositive evidence) :
    Hom m (conditioning m evidence hEvidence) :=
  Hom.ofOperation m (.conditioning evidence hEvidence)
    (conditioning_noActive m evidence hEvidence)

def conditioningInverse (m : ExtensionalMode S)
    (evidence : m.model.latent.Assignment -> Bool)
    (hEvidence : m.belief.EventPositive evidence) :
    UnconditionInverse (conditioningHom m evidence hEvidence) where
  ready :=
    conditionLatent_UnconditionReady (embed m).record evidence hEvidence
  roundtrip :=
    conditionLatent_uncondition (embed m).record evidence hEvidence

/-- Inverse 1-cells restore `embed m`; `project_embed` is then `id`. -/
theorem UnconditionInverse.restores {m n : ExtensionalMode S}
    {μ : Hom m n} (inv : UnconditionInverse μ) :
    μ.target.record.uncondition inv.ready = (embed m).record :=
  inv.roundtrip

/-! ### Learn / forget inverse 1-cells as workspace paths -/

def learningTerminalHom (m : ExtensionalMode S)
    (spec : TerminalVariableSpec S) :
    Hom m (learningTerminal m spec) :=
  Hom.ofOperation m (.learningTerminal spec)
    (learningTerminal_noActive m spec)

def learningTerminalInverse (m : ExtensionalMode S)
    (spec : TerminalVariableSpec S) :
    Inverse (learningTerminalHom m spec) :=
  .workspacePath
    (CausalEditPath.single
      (CausalEditTransition.forgetTerminal (embed m) spec extensionalName
        extensionalName))

def learningEndogenousHom (m : ExtensionalMode S)
    (spec : EndogenousVariableSpec (embed m).record) :
    Hom m (learningEndogenous m spec) :=
  Hom.ofOperation m (.learningEndogenous spec)
    (learningEndogenous_noActive m spec)

def learningEndogenousInverse (m : ExtensionalMode S)
    (spec : EndogenousVariableSpec (embed m).record) :
    Inverse (learningEndogenousHom m spec) :=
  .workspacePath
    (CausalEditPath.single
      (EndogenousVariableSpec.forgetTransition (embed m) spec
        extensionalName extensionalName))

def learningExogenousHom (m : ExtensionalMode S)
    (spec : ExogenousVariableSpec) :
    Hom m (learningExogenous m spec) :=
  Hom.ofOperation m (.learningExogenous spec)
    (learningExogenous_noActive m spec)

def learningExogenousInverse (m : ExtensionalMode S)
    (spec : ExogenousVariableSpec) :
    Inverse (learningExogenousHom m spec) :=
  .workspacePath
    (CausalEditPath.single
      (spec.forgetTransition (embed m) extensionalName extensionalName))

/-- Provenance forget restores the workspace record; `project` is then `id`. -/
@[simp] theorem learningTerminal_forget_project (m : ExtensionalMode S)
    (spec : TerminalVariableSpec S) :
    project
      (CausalEditTransition.forgetTerminal (embed m) spec
        extensionalName extensionalName).target.record
      (embed_noActive m) = m :=
  project_embed m

@[simp] theorem learningEndogenous_forget_project (m : ExtensionalMode S)
    (spec : EndogenousVariableSpec (embed m).record) :
    project
      (EndogenousVariableSpec.forgetTransition (embed m) spec
        extensionalName extensionalName).target.record
      (embed_noActive m) = m :=
  project_embed m

@[simp] theorem learningExogenous_forget_project (m : ExtensionalMode S)
    (spec : ExogenousVariableSpec) :
    project
      (spec.forgetTransition (embed m) extensionalName
        extensionalName).target.record
      (embed_noActive m) = m :=
  project_embed m

/-! ### Surgical `do`: inverse 1-cell stores the source mode -/

def surgicalInterventionHom (m : ExtensionalMode S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    Hom m (surgicalIntervention m action) :=
  Hom.ofOperation m (.surgicalIntervention action)
    (surgicalIntervention_noActive m action)

/--
The inverse 1-cell of public surgery is restoration of the stored source.
The workspace snapshot lives on `acrossStack .surgery` of `μ.target`; it is
not part of `ExtensionalMode`.
-/
def surgicalInterventionInverse (m : ExtensionalMode S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    Inverse (surgicalInterventionHom m action) :=
  .storedSource

/-- Restoring the stored source is the identity on the public mode. -/
theorem surgicalInterventionInverse_restore (m : ExtensionalMode S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    (fun _ : ExtensionalMode
        (SurgicalIntervention.signature m.model action) => m)
      (surgicalIntervention m action) = m :=
  rfl

/-! ### Optional atomic compile as one Hom -/

def atomicInterventionHom (m : ExtensionalMode S)
    (action : Action S) :
    Hom m (project (compile (embed m) action).target.record
      (compile_noActiveIntervention (embed m) action
        (embed_NoActiveIntervention m))) where
  target := (compile (embed m) action).target
  empty :=
    compile_noActiveIntervention (embed m) action
      (embed_NoActiveIntervention m)
  projected := rfl
  path := (compile (embed m) action).path

/--
Atomic compilation and compact surgery agree at unit evaluation, not as
equality of the `belief` field of `ExtensionalMode`. Atomic reindexes belief;
surgery keeps it.
-/
theorem atomicInterventionHom_eval_eq_surgery (m : ExtensionalMode S)
    (action : Action S)
    (assignment : m.model.latent.Assignment) :
    (compile (embed m) action).target.record.model.eval
        ((compileDeterministicRealizes (embed m) action).assignment
          assignment) =
      (compile (embed m) action).transportedObserved
        ((SurgicalIntervention.model m.model action).eval assignment) :=
  compileDeterministicRealizes_evaluate_surgery (embed m) action assignment

end ExtensionalMode

end Causality
end Thesis
