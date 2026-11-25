import Thesis.Causality.ExtensionalMode
import Thesis.Causality.ModeTheory
import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ConditionalIdentificationKernel
import Thesis.Causality.ObservationalEvaluation
import Thesis.Causality.CertifiedQuery

namespace Thesis
namespace Causality

open Probability

/-!
Identification indexed by a mode's declared experimental access.

Pearl ID is graph-indexed: it answers which observational functionals equal
`P(Y | do(X))` if every `do` in the query language is available. A mode
answers which interventions this epistemic position actually has. This module
supplies an explicit allowed query family and a presentation of results.
`CausalTransport.CertifiedModeInference` supplies the public engine adapters:
they retain class-indexed certificates and interpret population formulas
on the generative prior. Current-belief queries have a separate represented
SCM and entry point. Neither access nor the represented graph is inferred
from the compact workspace `do` field.

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

/-- Display of a class-certified population answer or a diagnostic,
or rejected as a permission miss. `failed` is the hedge engine; certified bounds retain their
proof in the indexed answer before this presentation-only projection. -/
inductive ModeIndexedAnswer (S : ObservedSignature) where
  | identified (formula : ProbabilityTerm S) (value : ProbabilityResult.Result)
  | failed (fail : IdentificationFail S)
  | unfinished
  | undefined
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

/-- Population observational law of the stored generative SCM. Graphical
identification reads this law. A current belief has a separate interpretation
and may correlate source variables that the population model keeps independent. -/
def observationalLaw (π : ModeQueryPolicy S) :
    FiniteProbRecord S.Assignment :=
  π.mode.model.observationalDist

/-- Updated observational predictions are available explicitly, without
claiming that they satisfy the original graph's independence assumptions. -/
def currentObservationalLaw (π : ModeQueryPolicy S) :
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
    π.currentObservationalLaw.probVal event = π.mode.observedValue event :=
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

/-- Forget proof data only for presentation. The public inference functions
in `CausalTransport.CertifiedModeInference` return the indexed certificate
itself; this display cannot be passed back as an identification certificate. -/
def displayAnswer {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment}
    (answer : CertifiedQuery.Answer source model reference) : ModeIndexedAnswer S :=
  match answer with
  | .identified evidence =>
      .identified evidence.certificate.formula evidence.value
  | .bounded evidence =>
      .bounded evidence.certificate.lower evidence.certificate.upper
  | .undefined => .undefined
  | .failed failure => .failed failure
  | .unfinished => .unfinished
  | .modeUnsupported => .modeUnsupported

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

end WorkspaceQueryPolicy

end Causality
end Thesis
