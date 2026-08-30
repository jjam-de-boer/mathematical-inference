import Thesis.Causality.Core
import Thesis.Causality.ModalDerivation

namespace Thesis
namespace Causality

open Probability

/-!
Causal epistemic records and their executable modal transitions.

Records carry a lock stack indexed by the current signature.
`announce` pushes an uncommitted same-`S` marker; `announceAcross` pushes a
`pending` across marker still at the old `S`. `pop` aborts that top frame
(uncommitted or pending). Pearl realisation is `commitPearl`; the indexed
public `commit` (every modality) lives in `Thesis.Causality.Structural.Commit`.
One-shot `setVariable` / `interveneNodes` / `observeNodes` / `unsetVariable`
append an already-executed frame (definitionally announce then commit).
`clearVariable` only writes `none` on a sticky note; modal `unset` /
`uncondition` / `undo` restore a snapshot. Signature-changing edits, once
committed, push an `across` frame storing the pre-edit payloads. Current
probability remains `observedValue`.
-/

namespace HardIntervention

/-- Extend a dependent intervention by setting every selected node. -/
def setNodes (intervention : HardIntervention S) (nodes : NodeSet S)
    (reference : S.Assignment) : HardIntervention S where
  value := fun i =>
    if nodes i then some (reference i) else intervention.value i

theorem targets_setNodes (intervention : HardIntervention S)
    (nodes : NodeSet S) (reference : S.Assignment) (i : Fin S.count) :
    (intervention.setNodes nodes reference).targets i =
      NodeSet.union intervention.targets nodes i := by
  cases selected : nodes i <;>
    simp [setNodes, targets, NodeSet.union, selected]

/-- From the empty mode, executing an action lock is exactly kernel intervention. -/
theorem empty_setNodes_eq_kernel_intervention (kernel : Kernel S)
    (reference : S.Assignment) (i : Fin S.count) :
    ((HardIntervention.empty S).setNodes kernel.action reference).value i =
      kernel.intervention reference i := by
  cases selected : kernel.action i <;>
    simp [setNodes, HardIntervention.empty, FiniteLatentSCM.noIntervention,
      Kernel.intervention, selected]

/-- Execute a list of primitive single-node settings from left to right. -/
def setVariablesSequentially (intervention : HardIntervention S)
    (reference : S.Assignment) :
    List (Fin S.count) -> HardIntervention S
  | [] => intervention
  | node :: rest =>
      setVariablesSequentially
        (intervention.set node (reference node)) reference rest

theorem setVariablesSequentially_value
    (intervention : HardIntervention S) (reference : S.Assignment)
    (nodes : List (Fin S.count)) (node : Fin S.count) :
    (intervention.setVariablesSequentially reference nodes).value node =
      if node ∈ nodes then some (reference node)
      else intervention.value node := by
  induction nodes generalizing intervention with
  | nil => simp [setVariablesSequentially]
  | cons selected rest ih =>
      rw [setVariablesSequentially, ih]
      by_cases inRest : node ∈ rest
      · simp [inRest]
      · by_cases same : node = selected
        · subst selected
          rw [if_neg inRest, if_pos (by simp)]
          exact intervention.set_at_target node (reference node)
        · simp only [List.mem_cons, same, false_or, inRest, if_false]
          exact intervention.set_away_from_target selected node
            (reference selected) same

end HardIntervention

/-! ## Proof-carrying epistemic records and transitions -/

/--
Same-signature modal markers.  Announcing pushes an uncommitted frame;
committing stores the pre-commit payloads on a `committed` constructor.
Signature-changing edits use `AcrossKind` on `LockStack.across`.
-/
inductive ModalMarker (S : ObservedSignature) where
  | condition
  | observe (nodes : NodeSet S) (reference : S.Assignment)
  | uncondition
  | set (target : Fin S.count) (value : S.Value target)
  | intervene (nodes : NodeSet S) (reference : S.Assignment)
  | unset (target : Fin S.count)
  | undo
  | replaceMechanism
  | restoreMechanism
  | reindexBelief
  | relateLatent
  | unrelateLatent
  | learnExogenous
  | forgetExogenous
  | forgetUnusedExogenous

/-- Signature-changing stack frames.  The destination index is `LockStack`'s. -/
inductive AcrossKind where
  | learnTerminal
  | learnEndogenous
  | forgetTerminal
  | forgetEndogenous
  | forgetUnusedEndogenous
  | relateDirected
  | unrelateDirected
  | surgery
  deriving DecidableEq, Repr

/--
Lock stack indexed by the current observed signature.  `uncommitted` and
`pending` are held locks still at `S` (`pending` is a signature-changing
marker that has not yet been realised).  `committed` stays at `S`.  `across`
is the executed snapshot at the new signature; payloads are stored rather
than nested records so the family is not nested.
-/
inductive LockStack : ObservedSignature -> Type 1 where
  | nil {S : ObservedSignature} : LockStack S
  | uncommitted {S : ObservedSignature} (marker : ModalMarker S)
      (rest : LockStack S) : LockStack S
  | pending {S : ObservedSignature} (kind : AcrossKind)
      (rest : LockStack S) : LockStack S
  | committed {S : ObservedSignature} (marker : ModalMarker S)
      (model : ExactModel S)
      (belief : FiniteProbRecord model.latent.Assignment)
      (intervention : HardIntervention S)
      (snapLocks : LockStack S)
      (rest : LockStack S) : LockStack S
  | across {S T : ObservedSignature} (kind : AcrossKind)
      (model : ExactModel S)
      (belief : FiniteProbRecord model.latent.Assignment)
      (intervention : HardIntervention S)
      (oldLocks : LockStack S)
      (rest : LockStack T) : LockStack T

namespace LockStack

def tail {S : ObservedSignature} : LockStack S -> LockStack S
  | .nil => .nil
  | .uncommitted _ rest => rest
  | .pending _ rest => rest
  | .committed _ _ _ _ _ rest => rest
  | .across _ _ _ _ _ rest => rest

@[simp] theorem tail_uncommitted (marker : ModalMarker S) (rest : LockStack S) :
    (uncommitted marker rest).tail = rest :=
  rfl

@[simp] theorem tail_pending (kind : AcrossKind) (rest : LockStack S) :
    (pending kind rest).tail = rest :=
  rfl

@[simp] theorem tail_committed (marker : ModalMarker S) (model : ExactModel S)
    (belief : FiniteProbRecord model.latent.Assignment)
    (intervention : HardIntervention S) (snapLocks rest : LockStack S) :
    (committed marker model belief intervention snapLocks rest).tail = rest :=
  rfl

def topUncommittedEq {S : ObservedSignature} (locks : LockStack S)
    (marker : ModalMarker S) : Prop :=
  match locks with
  | .uncommitted m _ => m = marker
  | _ => False

@[simp] theorem topUncommittedEq_uncommitted (marker : ModalMarker S)
    (rest : LockStack S) :
    topUncommittedEq (uncommitted marker rest) marker :=
  rfl

def topPendingEq {S : ObservedSignature} (locks : LockStack S)
    (kind : AcrossKind) : Prop :=
  match locks with
  | .pending k _ => k = kind
  | _ => False

@[simp] theorem topPendingEq_pending (kind : AcrossKind) (rest : LockStack S) :
    topPendingEq (pending kind rest) kind :=
  rfl

def unconditionReady {S : ObservedSignature} (locks : LockStack S) : Prop :=
  match locks with
  | .committed (.observe _ _) _ _ _ _ _ => True
  | .committed .condition _ _ _ _ _ => True
  | _ => False

def restoreMechanismReady {S : ObservedSignature} (locks : LockStack S) : Prop :=
  match locks with
  | .committed .replaceMechanism _ _ _ _ _ => True
  | _ => False

def forgetExogenousReady {S : ObservedSignature} (locks : LockStack S) : Prop :=
  match locks with
  | .committed .learnExogenous _ _ _ _ _ => True
  | _ => False

def undoReady {S : ObservedSignature} (locks : LockStack S) : Prop :=
  match locks with
  | .committed _ _ _ _ _ _ => True
  | _ => False

end LockStack

/--
Epistemic state.  `locks` is the signature-indexed lock stack: `announce`
and `announceAcross` push, `pop` drops an uncommitted or pending top frame,
`commitPearl` realises a same-`S` Pearl marker.  The public indexed `commit`
is in `Structural.Commit`.
-/
structure CausalEpistemicRecord (S : ObservedSignature) where
  model : ExactModel S
  belief : FiniteProbRecord model.latent.Assignment
  intervention : HardIntervention S
  locks : LockStack S

namespace CausalEpistemicRecord

def initial (model : ExactModel S) : CausalEpistemicRecord S where
  model := model
  belief := model.prior
  intervention := HardIntervention.empty S
  locks := .nil

/-- Same-`S` executed frame whose snapshot is this record. -/
def executedLocks (R : CausalEpistemicRecord S) (marker : ModalMarker S) :
    LockStack S :=
  .committed marker R.model R.belief R.intervention R.locks R.locks

/-- Signature-changing executed frame whose snapshot is this record. -/
def acrossLocks (R : CausalEpistemicRecord S) (kind : AcrossKind)
    {T : ObservedSignature} : LockStack T :=
  .across kind R.model R.belief R.intervention R.locks .nil

/-- Push an uncommitted marker.  Payloads are unchanged. -/
def announce (R : CausalEpistemicRecord S) (marker : ModalMarker S) :
    CausalEpistemicRecord S :=
  { R with locks := .uncommitted marker R.locks }

/-- Push a pending signature-changing marker.  Payloads are unchanged. -/
def announceAcross (R : CausalEpistemicRecord S) (kind : AcrossKind) :
    CausalEpistemicRecord S :=
  { R with locks := .pending kind R.locks }

/-- The top frame exists and is not yet committed or executed
(`.uncommitted` or `.pending`). -/
def TopUncommitted (R : CausalEpistemicRecord S) : Prop :=
  match R.locks with
  | .uncommitted _ _ => True
  | .pending _ _ => True
  | _ => False

theorem announce_topUncommitted (R : CausalEpistemicRecord S)
    (marker : ModalMarker S) :
    TopUncommitted (R.announce marker) := by
  simp [TopUncommitted, announce]

theorem announceAcross_topUncommitted (R : CausalEpistemicRecord S)
    (kind : AcrossKind) :
    TopUncommitted (R.announceAcross kind) := by
  simp [TopUncommitted, announceAcross]

@[simp] theorem announce_topUncommittedEq (R : CausalEpistemicRecord S)
    (marker : ModalMarker S) :
    LockStack.topUncommittedEq (R.announce marker).locks marker :=
  rfl

@[simp] theorem announceAcross_topPendingEq (R : CausalEpistemicRecord S)
    (kind : AcrossKind) :
    LockStack.topPendingEq (R.announceAcross kind).locks kind :=
  rfl

/-- Abort an uncommitted or pending top announce.  Not a flag on commit. -/
def pop (R : CausalEpistemicRecord S) (_h : TopUncommitted R) :
    CausalEpistemicRecord S :=
  { R with locks := R.locks.tail }

theorem pop_announce (R : CausalEpistemicRecord S) (marker : ModalMarker S) :
    pop (R.announce marker) (announce_topUncommitted R marker) = R := by
  cases R
  simp [pop, announce]

theorem pop_announceAcross (R : CausalEpistemicRecord S) (kind : AcrossKind) :
    pop (R.announceAcross kind) (announceAcross_topUncommitted R kind) = R := by
  cases R
  simp [pop, announceAcross]

/-- Drop the uncommitted or pending top; payloads unchanged. -/
def baseOfCommit (R : CausalEpistemicRecord S) : CausalEpistemicRecord S :=
  { R with locks := R.locks.tail }

@[simp] theorem baseOfCommit_announce (R : CausalEpistemicRecord S)
    (marker : ModalMarker S) :
    (R.announce marker).baseOfCommit = R := by
  cases R
  simp [announce, baseOfCommit]

@[simp] theorem baseOfCommit_announceAcross (R : CausalEpistemicRecord S)
    (kind : AcrossKind) :
    (R.announceAcross kind).baseOfCommit = R := by
  cases R
  simp [announceAcross, baseOfCommit]

/-- Reload the snapshot on the last committed same-`S` frame. -/
def restoreTop (R : CausalEpistemicRecord S) : CausalEpistemicRecord S :=
  match R.locks with
  | .committed _ model belief intervention snapLocks _ =>
      { model := model
        belief := belief
        intervention := intervention
        locks := snapLocks }
  | _ => R

/-- The latent event implementing observation of selected nodes at a valuation. -/
def nodeObservationEvidence (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment)
    (u : R.model.latent.Assignment) : Bool :=
  Kernel.agreesOn nodes reference
    (R.model.evalUnder R.intervention.value u)

def UnsetReady (R : CausalEpistemicRecord S) (target : Fin S.count) : Prop :=
  match R.locks with
  | .committed (.set t _) model _ _ _ _ => t = target ∧ model = R.model
  | .committed (.intervene nodes _) model _ _ _ _ =>
      nodes target = true ∧ model = R.model
  | _ => False

def UnconditionReady (R : CausalEpistemicRecord S) : Prop :=
  LockStack.unconditionReady R.locks

def RestoreMechanismReady (R : CausalEpistemicRecord S) : Prop :=
  LockStack.restoreMechanismReady R.locks

def ForgetExogenousReady (R : CausalEpistemicRecord S) : Prop :=
  LockStack.forgetExogenousReady R.locks

def UndoReady (R : CausalEpistemicRecord S) : Prop :=
  LockStack.undoReady R.locks

@[simp] theorem UnsetReady_baseOfCommit_announce
    (R : CausalEpistemicRecord S) (marker : ModalMarker S)
    (target : Fin S.count) :
    UnsetReady (R.announce marker).baseOfCommit target = R.UnsetReady target := by
  simp [baseOfCommit_announce]

@[simp] theorem UnconditionReady_baseOfCommit_announce
    (R : CausalEpistemicRecord S) (marker : ModalMarker S) :
    UnconditionReady (R.announce marker).baseOfCommit = R.UnconditionReady := by
  simp [baseOfCommit_announce]

@[simp] theorem RestoreMechanismReady_baseOfCommit_announce
    (R : CausalEpistemicRecord S) (marker : ModalMarker S) :
    RestoreMechanismReady (R.announce marker).baseOfCommit =
      R.RestoreMechanismReady := by
  simp [baseOfCommit_announce]

@[simp] theorem ForgetExogenousReady_baseOfCommit_announce
    (R : CausalEpistemicRecord S) (marker : ModalMarker S) :
    ForgetExogenousReady (R.announce marker).baseOfCommit =
      R.ForgetExogenousReady := by
  simp [baseOfCommit_announce]

@[simp] theorem UndoReady_baseOfCommit_announce
    (R : CausalEpistemicRecord S) (marker : ModalMarker S) :
    UndoReady (R.announce marker).baseOfCommit = R.UndoReady := by
  simp [baseOfCommit_announce]

/-- Side conditions for realising the current uncommitted top marker. -/
inductive CanCommitPearl (R : CausalEpistemicRecord S) : Type where
  | set (target : Fin S.count) (value : S.Value target) :
      LockStack.topUncommittedEq R.locks (.set target value) →
        CanCommitPearl R
  | intervene (nodes : NodeSet S) (reference : S.Assignment) :
      LockStack.topUncommittedEq R.locks (.intervene nodes reference) →
        CanCommitPearl R
  | observe (nodes : NodeSet S) (reference : S.Assignment) :
      LockStack.topUncommittedEq R.locks (.observe nodes reference) →
        R.belief.EventPositive
          (R.nodeObservationEvidence nodes reference) →
        CanCommitPearl R
  | condition (evidence : R.model.latent.Assignment -> Bool)
      (hEvidence : R.belief.EventPositive evidence) :
      LockStack.topUncommittedEq R.locks .condition →
        CanCommitPearl R
  | unset (target : Fin S.count) :
      LockStack.topUncommittedEq R.locks (.unset target) →
        UnsetReady R.baseOfCommit target →
        CanCommitPearl R
  | uncondition :
      LockStack.topUncommittedEq R.locks .uncondition →
        UnconditionReady R.baseOfCommit →
        CanCommitPearl R
  | restoreMechanism :
      LockStack.topUncommittedEq R.locks .restoreMechanism →
        RestoreMechanismReady R.baseOfCommit →
        CanCommitPearl R
  | undo :
      LockStack.topUncommittedEq R.locks .undo →
        UndoReady R.baseOfCommit →
        CanCommitPearl R

/-- Realise the top uncommitted marker only. -/
def commitPearl (R : CausalEpistemicRecord S) (h : CanCommitPearl R) :
    CausalEpistemicRecord S :=
  let base := R.baseOfCommit
  match h with
  | .set target value _ =>
      { model := base.model
        belief := base.belief
        intervention := base.intervention.set target value
        locks := base.executedLocks (.set target value) }
  | .intervene nodes reference _ =>
      { model := base.model
        belief := base.belief
        intervention := base.intervention.setNodes nodes reference
        locks := base.executedLocks (.intervene nodes reference) }
  | .observe nodes reference _ positive =>
      { model := base.model
        belief :=
          base.belief.conditionOn
            (base.nodeObservationEvidence nodes reference) (by
              simpa [baseOfCommit, nodeObservationEvidence] using positive)
        intervention := base.intervention
        locks := base.executedLocks (.observe nodes reference) }
  | .condition evidence hEvidence _ =>
      { model := base.model
        belief :=
          base.belief.conditionOn evidence (by simpa [baseOfCommit] using hEvidence)
        intervention := base.intervention
        locks := base.executedLocks .condition }
  | .unset _ _ _ => restoreTop base
  | .uncondition _ _ => restoreTop base
  | .restoreMechanism _ _ => restoreTop base
  | .undo _ _ => restoreTop base

def observedDist (R : CausalEpistemicRecord S) :
    FiniteProbRecord S.Assignment :=
  R.belief.map (R.model.evalUnder R.intervention.value)

def observedValue (R : CausalEpistemicRecord S)
    (event : S.Assignment -> Bool) : QProb :=
  R.observedDist.probVal event

def conditionLatent (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief.conditionOn evidence hEvidence
  intervention := R.intervention
  locks := R.executedLocks .condition

def conditionObservation (R : CausalEpistemicRecord S)
    (evidence : S.Assignment -> Bool)
    (hEvidence : R.observedDist.EventPositive evidence) :
    CausalEpistemicRecord S :=
  R.conditionLatent
    (fun u => evidence (R.model.evalUnder R.intervention.value u)) (by
      simpa [observedDist, FiniteProbRecord.EventPositive,
        FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels] using
          hEvidence)

/-- Observation lock: Bayes on selected nodes plus a committed `.observe` frame. -/
def observeNodes (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment)
    (hEvidence : R.belief.EventPositive
      (R.nodeObservationEvidence nodes reference)) :
    CausalEpistemicRecord S where
  model := R.model
  belief :=
    R.belief.conditionOn (R.nodeObservationEvidence nodes reference) hEvidence
  intervention := R.intervention
  locks := R.executedLocks (.observe nodes reference)

def setVariable (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention := R.intervention.set target value
  locks := R.executedLocks (.set target value)

theorem setVariable_eq_announce_commit
    (R : CausalEpistemicRecord S) (target : Fin S.count)
    (value : S.Value target) :
    R.setVariable target value =
      (R.announce (.set target value)).commitPearl
        (.set target value (announce_topUncommittedEq R _)) := by
  cases R
  simp [setVariable, announce, commitPearl, baseOfCommit, executedLocks]

/-- Execute a simultaneous finite hard intervention at a reference valuation. -/
def interveneNodes (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment) :     CausalEpistemicRecord S where
  model := R.model
  belief := R.belief
  intervention := R.intervention.setNodes nodes reference
  locks := R.executedLocks (.intervene nodes reference)

theorem interveneNodes_eq_announce_commit
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment) :
    R.interveneNodes nodes reference =
      (R.announce (.intervene nodes reference)).commitPearl
        (.intervene nodes reference (announce_topUncommittedEq R _)) := by
  cases R
  simp [interveneNodes, announce, commitPearl, baseOfCommit, executedLocks]

/-- Execute a list of single-node interventions from left to right. -/
def setVariablesSequentially (R : CausalEpistemicRecord S)
    (reference : S.Assignment) (nodes : List (Fin S.count)) :
    CausalEpistemicRecord S :=
  { R with
    intervention :=
      R.intervention.setVariablesSequentially reference nodes }

/-- The canonical duplicate-free list selected by a Boolean node set. -/
def selectedNodeList (S : ObservedSignature) (nodes : NodeSet S) :
    List (Fin S.count) :=
  (List.finRange S.count).filter fun node => nodes node

theorem mem_selectedNodeList (nodes : NodeSet S) (node : Fin S.count) :
    node ∈ selectedNodeList S nodes <-> nodes node = true := by
  simp [selectedNodeList]

/-- The number of nodes classified as true. -/
def selectedNodeCount (nodes : NodeSet S) : Nat :=
  (selectedNodeList S nodes).length

/--
The canonical embedding of the selected nodes, in ambient index order.
This is the map \(j_S\) of the finite node-set selection proposition.
-/
def selectedEmbed (nodes : NodeSet S)
    (i : Fin (selectedNodeCount nodes)) : Fin S.count :=
  (selectedNodeList S nodes).get i

theorem pairwise_get_of_lt {α : Type _} {R : α -> α -> Prop}
    {values : List α} (h : values.Pairwise R)
    (i j : Fin values.length) (hij : i.val < j.val) :
    R (values.get i) (values.get j) := by
  induction values with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
      have parts := List.pairwise_cons.mp h
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (Nat.lt_irrefl 0 hij).elim
          | succ j' =>
              exact parts.1 (tail.get j') (List.get_mem tail j')
      | succ i' =>
          cases j using Fin.cases with
          | zero => exact (Nat.not_lt_zero _ hij).elim
          | succ j' =>
              exact ih parts.2 i' j' (Nat.succ_lt_succ_iff.mp hij)

theorem finRange_pairwise_lt (n : Nat) :
    (List.finRange n).Pairwise (fun a b => a.val < b.val) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ]
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro b hb
        rcases List.mem_map.mp hb with ⟨k, _, eq⟩
        cases eq
        exact Nat.succ_pos k.val
      · exact List.Pairwise.map Fin.succ
          (fun _ _ hlt => Nat.succ_lt_succ hlt) ih

theorem selectedNodeList_pairwise_lt (nodes : NodeSet S) :
    (selectedNodeList S nodes).Pairwise
      (fun a b => a.val < b.val) :=
  (finRange_pairwise_lt S.count).filter (fun node => nodes node)

theorem selectedNodeList_nodup (nodes : NodeSet S) :
    (selectedNodeList S nodes).Nodup :=
  (selectedNodeList_pairwise_lt nodes).imp
    (fun hlt => Fin.ne_of_val_ne (Nat.ne_of_lt hlt))

theorem selectedEmbed_mem (nodes : NodeSet S)
    (i : Fin (selectedNodeCount nodes)) :
    nodes (selectedEmbed nodes i) = true :=
  (mem_selectedNodeList nodes (selectedEmbed nodes i)).mp
    (List.get_mem (selectedNodeList S nodes) i)

theorem selectedEmbed_strict_mono (nodes : NodeSet S)
    {i j : Fin (selectedNodeCount nodes)}
    (hij : i.val < j.val) :
    (selectedEmbed nodes i).val < (selectedEmbed nodes j).val :=
  pairwise_get_of_lt (selectedNodeList_pairwise_lt nodes) i j hij

theorem selectedEmbed_inj (nodes : NodeSet S)
    {i j : Fin (selectedNodeCount nodes)}
    (h : selectedEmbed nodes i = selectedEmbed nodes j) : i = j := by
  apply Fin.ext
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · have mono := selectedEmbed_strict_mono nodes hlt
    rw [h] at mono
    exact (Nat.lt_irrefl _ mono).elim
  · exact heq
  · have mono := selectedEmbed_strict_mono nodes hgt
    rw [h] at mono
    exact (Nat.lt_irrefl _ mono).elim

theorem selectedEmbed_lt_reflect (nodes : NodeSet S)
    {i j : Fin (selectedNodeCount nodes)}
    (hlt : (selectedEmbed nodes i).val < (selectedEmbed nodes j).val) :
    i.val < j.val := by
  rcases Nat.lt_trichotomy i.val j.val with h | h | h
  · exact h
  · have same : i = j := Fin.ext h
    rw [same] at hlt
    exact (Nat.lt_irrefl _ hlt).elim
  · have mono := selectedEmbed_strict_mono nodes h
    exact (Nat.lt_asymm hlt mono).elim

theorem exists_selectedEmbed_of_mem (nodes : NodeSet S)
    {node : Fin S.count} (h : nodes node = true) :
    Exists fun i : Fin (selectedNodeCount nodes) =>
      selectedEmbed nodes i = node := by
  have hmem : node ∈ selectedNodeList S nodes :=
    (mem_selectedNodeList nodes node).mpr h
  rcases List.get_of_mem hmem with ⟨i, hi⟩
  exact ⟨i, hi⟩

theorem mem_iff_exists_selectedEmbed (nodes : NodeSet S)
    (node : Fin S.count) :
    nodes node = true <->
      Exists fun i : Fin (selectedNodeCount nodes) =>
        selectedEmbed nodes i = node := by
  constructor
  · intro h
    exact exists_selectedEmbed_of_mem nodes h
  · intro ⟨i, hi⟩
    simpa [hi] using selectedEmbed_mem nodes i

theorem setVariablesSequentially_intervention_value
    (R : CausalEpistemicRecord S) (reference : S.Assignment)
    (nodes : List (Fin S.count)) (node : Fin S.count) :
    (R.setVariablesSequentially reference nodes).intervention.value node =
      if node ∈ nodes then some (reference node)
      else R.intervention.value node := by
  exact R.intervention.setVariablesSequentially_value reference nodes node

/-- The sequential implementation of a simultaneous node-set intervention. -/
def interveneNodesSequentially (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment) :
    CausalEpistemicRecord S :=
  R.setVariablesSequentially reference (selectedNodeList S nodes)

theorem interveneNodesSequentially_intervention_value
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment) (node : Fin S.count) :
    (R.interveneNodesSequentially nodes reference).intervention.value node =
      (R.interveneNodes nodes reference).intervention.value node := by
  rw [interveneNodesSequentially,
    setVariablesSequentially_intervention_value]
  cases selected : nodes node <;>
    simp [mem_selectedNodeList, selected, interveneNodes,
      HardIntervention.setNodes]

/--
Simultaneous finite intervention agrees with sequential setting on the
payload.  The lock stacks differ: simultaneous records one `intervene` frame.
-/
theorem interveneNodes_eq_sequential
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment) :
    (R.interveneNodes nodes reference).intervention =
      (R.interveneNodesSequentially nodes reference).intervention := by
  apply HardIntervention.extensional
  intro node
  exact (interveneNodesSequentially_intervention_value
    R nodes reference node).symm

/-- Write `none` on one sticky-note coordinate.  Not a modal inverse. -/
def clearVariable (R : CausalEpistemicRecord S)
    (target : Fin S.count) : CausalEpistemicRecord S :=
  { R with intervention := R.intervention.unset target }

/-- Modal inverse of a LIFO `set`/`intervene` frame. -/
def unsetVariable (R : CausalEpistemicRecord S)
    (target : Fin S.count) (h : R.UnsetReady target) :
    CausalEpistemicRecord S :=
  (R.announce (.unset target)).commitPearl
    (.unset target (announce_topUncommittedEq R _) (by
      simpa using h))

theorem unsetVariable_eq_announce_commit
    (R : CausalEpistemicRecord S) (target : Fin S.count)
    (h : R.UnsetReady target) :
    R.unsetVariable target h =
      (R.announce (.unset target)).commitPearl
        (.unset target (announce_topUncommittedEq R _) (by
          simpa using h)) :=
  rfl

/-- After a one-shot set, the matching unset frame is legal. -/
theorem setVariable_UnsetReady (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    (R.setVariable target value).UnsetReady target := by
  simp [setVariable, UnsetReady, executedLocks]

/-- Provenance unset after set restores the pre-set record.  A 1-cell equation. -/
theorem setVariable_unsetVariable (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    (R.setVariable target value).unsetVariable target
      (setVariable_UnsetReady R target value) = R := by
  cases R
  simp [setVariable, unsetVariable, announce, commitPearl, baseOfCommit,
    executedLocks, restoreTop]

/-- Modal inverse of a LIFO `observe`/`condition` frame. -/
def uncondition (R : CausalEpistemicRecord S)
    (h : R.UnconditionReady) : CausalEpistemicRecord S :=
  (R.announce .uncondition).commitPearl
    (.uncondition (announce_topUncommittedEq R _) (by
      simpa using h))

/-- Restore the last executed same-`S` lock, whatever it was. -/
def undo (R : CausalEpistemicRecord S)
    (h : R.UndoReady) : CausalEpistemicRecord S :=
  (R.announce .undo).commitPearl
    (.undo (announce_topUncommittedEq R _) (by
      simpa using h))

/-- Named inverse of `replaceMechanism`. -/
def restoreMechanism (R : CausalEpistemicRecord S)
    (h : R.RestoreMechanismReady) : CausalEpistemicRecord S :=
  (R.announce .restoreMechanism).commitPearl
    (.restoreMechanism (announce_topUncommittedEq R _) (by
      simpa using h))

theorem conditioning_keeps_model (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    (R.conditionLatent evidence hEvidence).model = R.model := by
  rfl

theorem conditioning_keeps_product_prior (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    (R.conditionLatent evidence hEvidence).model.prior = R.model.prior := by
  rfl

theorem setting_keeps_belief (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    (R.setVariable target value).belief = R.belief := by
  rfl

theorem unsetting_keeps_belief (R : CausalEpistemicRecord S)
    (target : Fin S.count) :
    (R.clearVariable target).belief = R.belief := by
  rfl

theorem setVariable_at_target (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    (R.setVariable target value).intervention.value target = some value := by
  exact R.intervention.set_at_target target value

theorem conditionLatent_probVal (R : CausalEpistemicRecord S)
    (evidence event : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) :
    QProb.Equiv
      ((R.conditionLatent evidence hEvidence).belief.probVal event)
      (QProb.div
        (R.belief.probVal (fun u => evidence u && event u))
        (R.belief.probVal evidence) hEvidence) :=
  R.belief.conditionOn_probVal evidence event hEvidence

theorem observedDist_probVal (R : CausalEpistemicRecord S)
    (event : S.Assignment -> Bool) :
    QProb.Equiv (R.observedDist.probVal event)
      (R.belief.probVal
        (fun u => event (R.model.evalUnder R.intervention.value u))) :=
  FiniteProbRecord.map_probVal R.belief
    (R.model.evalUnder R.intervention.value) event

theorem restoreTop_model_of_unsetReady (R : CausalEpistemicRecord S)
    (target : Fin S.count) (h : R.UnsetReady target) :
    R.restoreTop.model = R.model := by
  cases hlock : R.locks with
  | committed marker model belief intervention snapLocks rest =>
      cases marker with
      | set t _ =>
          have : t = target ∧ model = R.model := by
            simpa [UnsetReady, hlock] using h
          simp [restoreTop, hlock]
          exact this.2
      | intervene nodes _ =>
          have : nodes target = true ∧ model = R.model := by
            simpa [UnsetReady, hlock] using h
          simp [restoreTop, hlock]
          exact this.2
      | _ =>
          simp [UnsetReady, hlock] at h
  | _ =>
      simp [UnsetReady, hlock] at h

theorem unsetVariable_keeps_model (R : CausalEpistemicRecord S)
    (target : Fin S.count) (h : R.UnsetReady target) :
    (R.unsetVariable target h).model = R.model := by
  simp [unsetVariable, commitPearl, baseOfCommit_announce]
  exact restoreTop_model_of_unsetReady R target h

end CausalEpistemicRecord

inductive CausalTransitionLabel where
  | conditioning
  | setting
  | unsetting
  deriving DecidableEq, Repr

inductive CausalRecordStep :
    CausalTransitionLabel ->
      CausalEpistemicRecord S -> CausalEpistemicRecord S -> Type 1
  | conditioning (R : CausalEpistemicRecord S)
      (evidence : R.model.latent.Assignment -> Bool)
      (hEvidence : R.belief.EventPositive evidence) :
      CausalRecordStep .conditioning R (R.conditionLatent evidence hEvidence)
  | observing (R : CausalEpistemicRecord S) (nodes : NodeSet S)
      (reference : S.Assignment)
      (hEvidence : R.belief.EventPositive
        (R.nodeObservationEvidence nodes reference)) :
      CausalRecordStep .conditioning R
        (R.observeNodes nodes reference hEvidence)
  | setting (R : CausalEpistemicRecord S)
      (target : Fin S.count) (value : S.Value target) :
      CausalRecordStep .setting R (R.setVariable target value)
  | intervening (R : CausalEpistemicRecord S) (nodes : NodeSet S)
      (reference : S.Assignment) :
      CausalRecordStep .setting R (R.interveneNodes nodes reference)
  | unsetting (R : CausalEpistemicRecord S) (target : Fin S.count)
      (h : R.UnsetReady target) :
      CausalRecordStep .unsetting R (R.unsetVariable target h)

theorem CausalRecordStep.model_eq
    (step : CausalRecordStep label source dest) :
    dest.model = source.model := by
  cases step
  · rfl
  · rfl
  · rfl
  · rfl
  · exact CausalEpistemicRecord.unsetVariable_keeps_model _ _ _

structure CausalMode (S : ObservedSignature) where
  name : String
  record : CausalEpistemicRecord S

structure CausalTransition (S : ObservedSignature) where
  label : CausalTransitionLabel
  source : CausalMode S
  target : CausalMode S
  valid : CausalRecordStep label source.record target.record

namespace CausalTransition

theorem model_eq (transition : CausalTransition S) :
    transition.target.record.model = transition.source.record.model :=
  transition.valid.model_eq

def conditioning (sourceName targetName : String)
    (R : CausalEpistemicRecord S)
    (evidence : R.model.latent.Assignment -> Bool)
    (hEvidence : R.belief.EventPositive evidence) : CausalTransition S where
  label := .conditioning
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.conditionLatent evidence hEvidence⟩
  valid := CausalRecordStep.conditioning R evidence hEvidence

/-- A concrete observation transition realising an observation lock. -/
def observing (sourceName targetName : String)
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment)
    (hEvidence : R.belief.EventPositive
      (R.nodeObservationEvidence nodes reference)) : CausalTransition S where
  label := .conditioning
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.observeNodes nodes reference hEvidence⟩
  valid := CausalRecordStep.observing R nodes reference hEvidence

def setting (sourceName targetName : String)
    (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) : CausalTransition S where
  label := .setting
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.setVariable target value⟩
  valid := CausalRecordStep.setting R target value

/-- Execute every action lock in a kernel as one finite record transformation. -/
def intervening (sourceName targetName : String)
    (R : CausalEpistemicRecord S) (nodes : NodeSet S)
    (reference : S.Assignment) : CausalTransition S where
  label := .setting
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.interveneNodes nodes reference⟩
  valid := CausalRecordStep.intervening R nodes reference

def unsetting (sourceName targetName : String)
    (R : CausalEpistemicRecord S) (target : Fin S.count)
    (h : R.UnsetReady target) :
    CausalTransition S where
  label := .unsetting
  source := ⟨sourceName, R⟩
  target := ⟨targetName, R.unsetVariable target h⟩
  valid := CausalRecordStep.unsetting R target h

/-- Executable transitions that realise one of the symbolic query locks. -/
inductive Realizes : CausalTransition S -> CausalQueryModality S -> Prop
  | setting (sourceName targetName : String)
      (R : CausalEpistemicRecord S) (target : Fin S.count)
      (value : S.Value target) :
      Realizes
        (CausalTransition.setting sourceName targetName R target value)
        (.intervene (NodeSet.singleton target))
  | intervening (sourceName targetName : String)
      (R : CausalEpistemicRecord S) (nodes : NodeSet S)
      (reference : S.Assignment) :
      Realizes
        (CausalTransition.intervening sourceName targetName R nodes reference)
        (.intervene nodes)
  | observing (sourceName targetName : String)
      (R : CausalEpistemicRecord S) (nodes : NodeSet S)
      (reference : S.Assignment)
      (hEvidence : R.belief.EventPositive
        (R.nodeObservationEvidence nodes reference)) :
      Realizes
        (CausalTransition.observing sourceName targetName R nodes reference
          hEvidence)
        (.observe nodes)

theorem setting_realizes_intervention
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) :
    Realizes (CausalTransition.setting sourceName targetName R target value)
      (.intervene (NodeSet.singleton target)) :=
  .setting sourceName targetName R target value

theorem intervening_realizes_intervention
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment) :
    Realizes
      (CausalTransition.intervening sourceName targetName R nodes reference)
      (.intervene nodes) :=
  .intervening sourceName targetName R nodes reference

theorem kernel_action_realized
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (kernel : Kernel S) (reference : S.Assignment) :
    Realizes
      (CausalTransition.intervening sourceName targetName R kernel.action
        reference)
      (.intervene kernel.action) :=
  intervening_realizes_intervention sourceName targetName R kernel.action
    reference

theorem observing_realizes_observation
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment)
    (hEvidence : R.belief.EventPositive
      (R.nodeObservationEvidence nodes reference)) :
    Realizes
      (CausalTransition.observing sourceName targetName R nodes reference
        hEvidence)
      (.observe nodes) :=
  .observing sourceName targetName R nodes reference hEvidence

theorem setting_adds_intervention_target
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (target : Fin S.count) (value : S.Value target) (i : Fin S.count) :
    (CausalTransition.setting sourceName targetName R target value).target.record.intervention.targets i =
      NodeSet.union R.intervention.targets (NodeSet.singleton target) i := by
  by_cases same : i = target
  · subst i
    simp [CausalTransition.setting, CausalEpistemicRecord.setVariable,
      HardIntervention.targets, HardIntervention.set, NodeSet.union,
      NodeSet.singleton]
  · simp [CausalTransition.setting, CausalEpistemicRecord.setVariable,
      HardIntervention.targets, HardIntervention.set, NodeSet.union,
      NodeSet.singleton, same]

theorem intervening_adds_action_targets
    (sourceName targetName : String) (R : CausalEpistemicRecord S)
    (nodes : NodeSet S) (reference : S.Assignment) (i : Fin S.count) :
    (CausalTransition.intervening sourceName targetName R nodes reference).target.record.intervention.targets i =
      NodeSet.union R.intervention.targets nodes i := by
  simp [intervening, CausalEpistemicRecord.interveneNodes]
  exact R.intervention.targets_setNodes nodes reference i

end CausalTransition

end Causality
end Thesis
