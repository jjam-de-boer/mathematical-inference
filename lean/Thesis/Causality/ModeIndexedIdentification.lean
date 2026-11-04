import Thesis.Causality.ExtensionalMode
import Thesis.Causality.ModeTheory
import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ConditionalIdentificationKernel
import Thesis.Causality.ObservationalEvaluation

namespace Thesis
namespace Causality

open Probability

/-!
Identification indexed by a mode's declared experimental access.

Pearl ID is graph-indexed: it answers which observational functionals equal
`P(Y | do(X))` if every `do` in the query language is available. A mode
answers which interventions this epistemic position actually has. This module
restricts the query language to an explicit allowed family, then dispatches
to `identifyJointKernel` / `identifyConditionalKernel`. It does not
reimplement identification, infer access from a belief table, or treat
compact workspace `do` as that family.

`modeUnsupported` is a permission miss. It is not a hedge (`failed`) and not
an identified value. Completeness countermodels remain about the model class.
-/

variable {S : ObservedSignature.{0}}

/-- Realize a query action from the empty intervention. Unused nodes stay
`none`; forced nodes take the reference value. -/
def realizeQueryAction (action : NodeSet S) (reference : S.Assignment) :
    HardIntervention S :=
  (HardIntervention.empty S).setNodes action reference

theorem realizeQueryAction_unused (action : NodeSet S)
    (reference : S.Assignment) (node : Fin S.count)
    (unforced : action node = false) :
    (realizeQueryAction action reference).value node = none := by
  simp [realizeQueryAction, HardIntervention.setNodes, HardIntervention.empty,
    FiniteLatentSCM.noIntervention, unforced]

theorem realizeQueryAction_forced (action : NodeSet S)
    (reference : S.Assignment) (node : Fin S.count)
    (forced : action node = true) :
    (realizeQueryAction action reference).value node = some (reference node) := by
  simp [realizeQueryAction, HardIntervention.setNodes, forced]

theorem realizeQueryAction_targets (action : NodeSet S)
    (reference : S.Assignment) :
    (realizeQueryAction action reference).targets = action := by
  funext node
  cases selected : action node with
  | false =>
      simp [realizeQueryAction, HardIntervention.setNodes, HardIntervention.targets,
        HardIntervention.empty, FiniteLatentSCM.noIntervention, selected]
  | true =>
      simp [realizeQueryAction, HardIntervention.setNodes, HardIntervention.targets,
        selected]

/-- An intervention is allowed when every forced node is intervenable. -/
def interventionAllowed (intervenable : NodeSet S) (I : HardIntervention S) :
    Bool :=
  NodeSet.subsetBool I.targets intervenable

theorem interventionAllowed_iff (intervenable : NodeSet S)
    (I : HardIntervention S) :
    interventionAllowed intervenable I = true ↔
      NodeSet.Subset I.targets intervenable :=
  NodeSet.subsetBool_eq_true_iff _ _

/-- Nodes outside the allowed family stay unforced. -/
theorem interventionAllowed_unused_none (intervenable : NodeSet S)
    (I : HardIntervention S)
    (ok : interventionAllowed intervenable I = true) (node : Fin S.count)
    (outside : intervenable node = false) :
    I.value node = none := by
  have subset : NodeSet.Subset I.targets intervenable :=
    (interventionAllowed_iff intervenable I).mp ok
  cases hValue : I.value node with
  | none => rfl
  | some _ =>
      have forced : I.targets node = true := by
        simp [HardIntervention.targets, hValue]
      have inside := subset node forced
      rw [outside] at inside
      cases inside

theorem empty_set_targets (node : Fin S.count) (value : S.Value node) :
    ((HardIntervention.empty S).set node value).targets =
      NodeSet.singleton node := by
  funext i
  unfold HardIntervention.targets HardIntervention.set NodeSet.singleton
    HardIntervention.empty FiniteLatentSCM.noIntervention
  by_cases same : i = node
  · subst i
    simp
  · simp [same]

/-- Graph-indexed identification, interpreted on a mode's observational law,
or rejected as a permission miss. `failed` is the hedge engine; bounds are
kept only when the caller supplies them. -/
inductive ModeIndexedAnswer (S : ObservedSignature) where
  | identified (formula : ProbabilityTerm S) (value : ProbabilityResult.Result)
  | failed (fail : IdentificationFail S)
  | unfinished
  | bounded (lower upper : QProb)
  | modeUnsupported

namespace ModeIndexedAnswer

def isIdentified : ModeIndexedAnswer S → Bool
  | identified _ _ => true
  | _ => false

def isFailed : ModeIndexedAnswer S → Bool
  | failed _ => true
  | _ => false

def isModeUnsupported : ModeIndexedAnswer S → Bool
  | modeUnsupported => true
  | _ => false

def identifiedValue : ModeIndexedAnswer S → Option QProb
  | identified _ (some value) => some value
  | _ => none

theorem modeUnsupported_ne_failed (fail : IdentificationFail S) :
    (modeUnsupported : ModeIndexedAnswer S) ≠ failed fail := by
  intro h
  cases h

theorem modeUnsupported_ne_identified (formula : ProbabilityTerm S)
    (value : ProbabilityResult.Result) :
    (modeUnsupported : ModeIndexedAnswer S) ≠ identified formula value := by
  intro h
  cases h

end ModeIndexedAnswer

/--
A finished public mode together with declared experimental access and the
graph used for ID. Compact `do` on `ExtensionalMode.embed` stays empty even
when `intervenable` is nonempty: allowed experiments are not the current lock.
-/
structure ModeQueryPolicy (S : ObservedSignature.{0}) where
  mode : ExtensionalMode S
  intervenable : NodeSet S

/-- Workspace current state together with an explicit allowed family. The
compact intervention field is not that family. -/
structure WorkspaceQueryPolicy (S : ObservedSignature.{0}) where
  state : ModeTheory.CurrentState S
  intervenable : NodeSet S

namespace ModeQueryPolicy

def graph (π : ModeQueryPolicy S) : ObservedGraph S :=
  π.mode.model.observedGraph

/-- Observational law induced by current belief. Compact workspace `do` is
not applied: public modes already interpret under an empty lock. -/
def observationalLaw (π : ModeQueryPolicy S) :
    FiniteProbRecord S.Assignment :=
  π.mode.belief.map π.mode.model.eval

def allowed (π : ModeQueryPolicy S) (I : HardIntervention S) : Prop :=
  NodeSet.Subset I.targets π.intervenable

def allowedB (π : ModeQueryPolicy S) (I : HardIntervention S) : Bool :=
  interventionAllowed π.intervenable I

theorem allowedB_iff (π : ModeQueryPolicy S) (I : HardIntervention S) :
    π.allowedB I = true ↔ π.allowed I :=
  interventionAllowed_iff _ _

/-- Forget compact workspace `do` when packing a query policy. Access is the
supplied `intervenable` predicate, not the current lock. -/
def ofWorkspace (σ : ModeTheory.CurrentState S) (intervenable : NodeSet S) :
    ModeQueryPolicy S where
  mode := { model := σ.model, belief := σ.belief }
  intervenable := intervenable

@[simp] theorem embed_compact_do_empty (π : ModeQueryPolicy S) :
    (ExtensionalMode.embed π.mode).record.intervention =
      HardIntervention.empty S :=
  rfl

@[simp] theorem embed_noActive (π : ModeQueryPolicy S) :
    ExtensionalMode.noActive (ExtensionalMode.embed π.mode).record :=
  ExtensionalMode.embed_noActive π.mode

/-- Empty compact `do` on the public embedding is compatible with a nonempty
allowed family. -/
theorem embed_empty_do_of_nonempty_allowed (π : ModeQueryPolicy S)
    (node : Fin S.count) (openNode : π.intervenable node = true)
    (value : S.Value node) :
    ExtensionalMode.noActive (ExtensionalMode.embed π.mode).record ∧
      π.allowedB ((HardIntervention.empty S).set node value) = true := by
  refine ⟨π.embed_noActive, ?_⟩
  unfold allowedB interventionAllowed
  rw [empty_set_targets]
  exact (NodeSet.subsetBool_eq_true_iff _ _).mpr
    (NodeSet.singleton_subset_of_mem openNode)

theorem ofWorkspace_embed_empty_do (σ : ModeTheory.CurrentState S)
    (intervenable : NodeSet S) :
    (ExtensionalMode.embed (ofWorkspace σ intervenable).mode).record.intervention =
      HardIntervention.empty S :=
  rfl

theorem ofWorkspace_drops_lock (σ : ModeTheory.CurrentState S)
    (intervenable : NodeSet S) :
    (ofWorkspace σ intervenable).mode.model = σ.model ∧
      (ofWorkspace σ intervenable).mode.belief = σ.belief ∧
      (ofWorkspace σ intervenable).intervenable = intervenable :=
  ⟨rfl, rfl, rfl⟩

theorem observationalLaw_eq_observedValue (π : ModeQueryPolicy S)
    (event : S.Assignment → Bool) :
    π.observationalLaw.probVal event = π.mode.observedValue event :=
  rfl

def jointAdmissible (π : ModeQueryPolicy S) (q : JointKernelQuery S) : Bool :=
  NodeSet.subsetBool q.action π.intervenable

def conditionalAdmissible (π : ModeQueryPolicy S)
    (q : ConditionalKernelQuery S) : Bool :=
  NodeSet.subsetBool q.action π.intervenable

theorem jointAdmissible_iff (π : ModeQueryPolicy S) (q : JointKernelQuery S) :
    π.jointAdmissible q = true ↔ NodeSet.Subset q.action π.intervenable :=
  NodeSet.subsetBool_eq_true_iff _ _

theorem conditionalAdmissible_iff (π : ModeQueryPolicy S)
    (q : ConditionalKernelQuery S) :
    π.conditionalAdmissible q = true ↔ NodeSet.Subset q.action π.intervenable :=
  NodeSet.subsetBool_eq_true_iff _ _

theorem jointAdmissible_iff_realized_allowed (π : ModeQueryPolicy S)
    (q : JointKernelQuery S) (reference : S.Assignment) :
    π.jointAdmissible q = true ↔
      π.allowedB (realizeQueryAction q.action reference) = true := by
  unfold jointAdmissible allowedB interventionAllowed
  rw [realizeQueryAction_targets]

theorem empty_action_jointAdmissible (π : ModeQueryPolicy S)
    (q : JointKernelQuery S) (emptyAction : NodeSet.isEmpty q.action = true) :
    π.jointAdmissible q = true := by
  apply (π.jointAdmissible_iff q).mpr
  intro node selected
  have noneSelected : q.action node = false :=
    (NodeSet.isEmpty_eq_true_iff q.action).mp emptyAction node
  rw [noneSelected] at selected
  cases selected

/-- Widen declared experimental access. Policy data only: the SCM, belief,
graph, and compact `do` are unchanged. Not a `CausalEditOperation`. -/
def widen (π : ModeQueryPolicy S) (extra : NodeSet S) : ModeQueryPolicy S :=
  { π with intervenable := NodeSet.union π.intervenable extra }

/-- Narrow declared experimental access. Same caveats as `widen`. -/
def narrow (π : ModeQueryPolicy S) (removed : NodeSet S) : ModeQueryPolicy S :=
  { π with intervenable := NodeSet.diff π.intervenable removed }

@[simp] theorem widen_graph (π : ModeQueryPolicy S) (extra : NodeSet S) :
    (π.widen extra).graph = π.graph :=
  rfl

@[simp] theorem narrow_graph (π : ModeQueryPolicy S) (removed : NodeSet S) :
    (π.narrow removed).graph = π.graph :=
  rfl

@[simp] theorem widen_mode (π : ModeQueryPolicy S) (extra : NodeSet S) :
    (π.widen extra).mode = π.mode :=
  rfl

@[simp] theorem narrow_mode (π : ModeQueryPolicy S) (removed : NodeSet S) :
    (π.narrow removed).mode = π.mode :=
  rfl

theorem widen_admissible (π : ModeQueryPolicy S) (extra : NodeSet S)
    (q : JointKernelQuery S)
    (covered : NodeSet.Subset q.action (NodeSet.union π.intervenable extra)) :
    (π.widen extra).jointAdmissible q = true :=
  ((π.widen extra).jointAdmissible_iff q).mpr covered

def interpretIdentified (π : ModeQueryPolicy S) (term : ProbabilityTerm S)
    (reference : S.Assignment) : ProbabilityResult.Result :=
  term.observationalDenote π.observationalLaw reference

/-- Convert a graph-indexed kernel outcome. Permission misses never arrive
here; a hedge stays `failed` unless the caller supplies bounds. -/
def ofKernelOutcome (π : ModeQueryPolicy S) (outcome : IdentificationOutcome S)
    (reference : S.Assignment) (bounds : Option (QProb × QProb)) :
    ModeIndexedAnswer S :=
  match outcome with
  | .identified term =>
      .identified term (π.interpretIdentified term reference)
  | .failed fail =>
      match bounds with
      | some ⟨lo, hi⟩ => .bounded lo hi
      | none => .failed fail
  | .unfinished => .unfinished

theorem ofKernelOutcome_ne_modeUnsupported (π : ModeQueryPolicy S)
    (outcome : IdentificationOutcome S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb)) :
    π.ofKernelOutcome outcome reference bounds ≠ .modeUnsupported := by
  cases outcome with
  | identified term => intro h; cases h
  | failed fail =>
      cases bounds with
      | none => intro h; cases h
      | some bounds =>
          cases bounds
          intro h
          cases h
  | unfinished => intro h; cases h

def kernelOutcome (π : ModeQueryPolicy S) (q : JointKernelQuery S)
    (override : Option (ProbabilityTerm S)) : IdentificationOutcome S :=
  match override with
  | some term => .identified term
  | none => identifyJointKernel π.graph q

/-- Dispatch: if the query action is allowed, run the existing kernel and
interpret an identified action-free term on the observational belief law. -/
def identifyJoint (π : ModeQueryPolicy S) (q : JointKernelQuery S)
    (reference : S.Assignment) (bounds : Option (QProb × QProb))
    (override : Option (ProbabilityTerm S)) : ModeIndexedAnswer S :=
  if π.jointAdmissible q then
    π.ofKernelOutcome (π.kernelOutcome q override) reference bounds
  else
    .modeUnsupported

def identifyConditional (π : ModeQueryPolicy S)
    (q : ConditionalKernelQuery S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb)) : ModeIndexedAnswer S :=
  if π.conditionalAdmissible q then
    π.ofKernelOutcome (identifyConditionalKernel π.graph q) reference bounds
  else
    .modeUnsupported

theorem identifyJoint_modeUnsupported (π : ModeQueryPolicy S)
    (q : JointKernelQuery S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb)) (override : Option (ProbabilityTerm S))
    (denied : π.jointAdmissible q = false) :
    π.identifyJoint q reference bounds override = .modeUnsupported := by
  simp [identifyJoint, denied]

theorem identifyConditional_modeUnsupported (π : ModeQueryPolicy S)
    (q : ConditionalKernelQuery S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb))
    (denied : π.conditionalAdmissible q = false) :
    π.identifyConditional q reference bounds = .modeUnsupported := by
  simp [identifyConditional, denied]

theorem identifyJoint_of_admissible (π : ModeQueryPolicy S)
    (q : JointKernelQuery S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb)) (override : Option (ProbabilityTerm S))
    (ok : π.jointAdmissible q = true) :
    π.identifyJoint q reference bounds override =
      π.ofKernelOutcome (π.kernelOutcome q override) reference bounds := by
  simp [identifyJoint, ok]

theorem identifyConditional_of_admissible (π : ModeQueryPolicy S)
    (q : ConditionalKernelQuery S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb))
    (ok : π.conditionalAdmissible q = true) :
    π.identifyConditional q reference bounds =
      π.ofKernelOutcome (identifyConditionalKernel π.graph q) reference bounds := by
  simp [identifyConditional, ok]

theorem identifyJoint_ne_modeUnsupported_of_admissible (π : ModeQueryPolicy S)
    (q : JointKernelQuery S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb)) (override : Option (ProbabilityTerm S))
    (ok : π.jointAdmissible q = true) :
    π.identifyJoint q reference bounds override ≠ .modeUnsupported := by
  rw [π.identifyJoint_of_admissible q reference bounds override ok]
  exact π.ofKernelOutcome_ne_modeUnsupported _ _ _

theorem identifyJoint_identified_of_kernel (π : ModeQueryPolicy S)
    (q : JointKernelQuery S) (reference : S.Assignment)
    (bounds : Option (QProb × QProb)) {term : ProbabilityTerm S}
    (ok : π.jointAdmissible q = true)
    (kernel : identifyJointKernel π.graph q = .identified term) :
    π.identifyJoint q reference bounds none =
      .identified term (π.interpretIdentified term reference) := by
  rw [π.identifyJoint_of_admissible q reference bounds none ok]
  simp [kernelOutcome, ofKernelOutcome, kernel]

theorem identifyJoint_failed_of_kernel (π : ModeQueryPolicy S)
    (q : JointKernelQuery S) (reference : S.Assignment)
    {fail : IdentificationFail S}
    (ok : π.jointAdmissible q = true)
    (kernel : identifyJointKernel π.graph q = .failed fail) :
    π.identifyJoint q reference none none = .failed fail := by
  rw [π.identifyJoint_of_admissible q reference none none ok]
  simp [kernelOutcome, ofKernelOutcome, kernel]

theorem identifyJoint_bounded_of_kernel (π : ModeQueryPolicy S)
    (q : JointKernelQuery S) (reference : S.Assignment)
    (lo hi : QProb) {fail : IdentificationFail S}
    (ok : π.jointAdmissible q = true)
    (kernel : identifyJointKernel π.graph q = .failed fail) :
    π.identifyJoint q reference (some ⟨lo, hi⟩) none = .bounded lo hi := by
  rw [π.identifyJoint_of_admissible q reference (some ⟨lo, hi⟩) none ok]
  simp [kernelOutcome, ofKernelOutcome, kernel]

end ModeQueryPolicy

namespace WorkspaceQueryPolicy

def toQueryPolicy (π : WorkspaceQueryPolicy S) : ModeQueryPolicy S :=
  ModeQueryPolicy.ofWorkspace π.state π.intervenable

def allowedB (π : WorkspaceQueryPolicy S) (I : HardIntervention S) : Bool :=
  interventionAllowed π.intervenable I

/-- Compact workspace `do` need not be an allowed experiment. -/
theorem compact_do_need_not_be_allowed (π : WorkspaceQueryPolicy S) :
    π.allowedB π.state.intervention = true →
      NodeSet.Subset π.state.intervention.targets π.intervenable :=
  (interventionAllowed_iff _ _).mp

theorem toQueryPolicy_ignores_lock (π : WorkspaceQueryPolicy S) :
    (ExtensionalMode.embed π.toQueryPolicy.mode).record.intervention =
      HardIntervention.empty S :=
  rfl

def identifyJoint (π : WorkspaceQueryPolicy S) (q : JointKernelQuery S)
    (reference : S.Assignment) (bounds : Option (QProb × QProb))
    (override : Option (ProbabilityTerm S)) : ModeIndexedAnswer S :=
  π.toQueryPolicy.identifyJoint q reference bounds override

end WorkspaceQueryPolicy

end Causality
end Thesis
