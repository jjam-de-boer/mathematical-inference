import Thesis.Causality.Structural.Core

namespace Thesis
namespace Causality

open Probability

/-!
Public announce/commit for every modality.  Pearl followers stay
`commitPearl`; this module aliases them as `CanCommit.pearl` and adds
structural constructors whose followers live beside `learnRecord` / `apply`.

Forward commit runs the follower of the top marker (`spec`, evidence, or
operation on the proof).  Provenance inverses reload a snapshot (`unset`,
`uncondition`, `restoreMechanism`, `undo`, learn-forget, exogenous forget).
Structural reverses (directed/latent unrelate, unused-delete) still `apply`
or `deleteRecord`.  Each `*_eq_announce_commit` theorem is the one-shot
protocol: the existing `learnRecord` / `apply` / `deleteRecord` equals
announce then this `commit`.
-/

namespace CausalEpistemicRecord

/--
Proof-carrying permission to realise the current uncommitted or pending top
frame.  The index `T` is the signature of the record after commit.  Extra
follower data (learn `spec`, Pearl evidence, relate/replace operations) lives
on the constructor, not on the marker alone.
-/
inductive CanCommit :
    {S : ObservedSignature} -> CausalEpistemicRecord S ->
      (T : ObservedSignature) -> Type 1
  | pearl {S : ObservedSignature} {R : CausalEpistemicRecord S}
      (h : CanCommitPearl R) : CanCommit R S
  | learnTerminal {S : ObservedSignature} {R : CausalEpistemicRecord S}
      (spec : TerminalVariableSpec S) :
      LockStack.topPendingEq R.locks .learnTerminal →
        CanCommit R spec.extendSignature
  | learnEndogenous {S : ObservedSignature} {R : CausalEpistemicRecord S}
      (spec : EndogenousVariableSpec R.baseOfCommit) :
      LockStack.topPendingEq R.locks .learnEndogenous →
        CanCommit R spec.extendSignature
  | forgetTerminal {S : ObservedSignature}
      (original : CausalEpistemicRecord S) (spec : TerminalVariableSpec S)
      {R : CausalEpistemicRecord spec.extendSignature} :
      LockStack.topPendingEq R.locks .forgetTerminal →
        R.baseOfCommit.locks = original.acrossLocks .learnTerminal →
        CanCommit R S
  | forgetEndogenous {S : ObservedSignature}
      (original : CausalEpistemicRecord S)
      (spec : EndogenousVariableSpec original)
      {R : CausalEpistemicRecord spec.extendSignature} :
      LockStack.topPendingEq R.locks .forgetEndogenous →
        R.baseOfCommit = spec.learnRecord →
        CanCommit R S
  | forgetUnusedEndogenous {S : ObservedSignature}
      {R : CausalEpistemicRecord S} (spec : ObservedDeletionSpec S) :
      LockStack.topPendingEq R.locks .forgetUnusedEndogenous →
        CanCommit R spec.signature
  | learnExogenous {S : ObservedSignature} {R : CausalEpistemicRecord S}
      (spec : ExogenousVariableSpec) :
      LockStack.topUncommittedEq R.locks .learnExogenous →
        CanCommit R S
  | forgetExogenous {S : ObservedSignature} {R : CausalEpistemicRecord S} :
      LockStack.topUncommittedEq R.locks .forgetExogenous →
        ForgetExogenousReady R.baseOfCommit →
        CanCommit R S
  | forgetUnusedExogenous {S : ObservedSignature}
      {R : CausalEpistemicRecord S}
      (spec : ExogenousDeletionSpec R.baseOfCommit.model) :
      LockStack.topUncommittedEq R.locks .forgetUnusedExogenous →
        CanCommit R S
  | relatingDirected {S : ObservedSignature} {R : CausalEpistemicRecord S}
      {parent child : Fin S.count} {earlier : parent.val < child.val}
      (operation : DirectedLink.RelateOperation S parent child earlier) :
      LockStack.topPendingEq R.locks .relateDirected →
        CanCommit R (DirectedLink.addSignature S parent child earlier)
  | unrelatingDirected {S : ObservedSignature} {R : CausalEpistemicRecord S}
      {parent child : Fin S.count}
      (operation : DirectedLink.UnrelateOperation S parent child) :
      LockStack.topPendingEq R.locks .unrelateDirected →
        CanCommit R (DirectedLink.removeSignature S parent child)
  | relatingLatent {S : ObservedSignature} {R : CausalEpistemicRecord S}
      {source : Fin R.baseOfCommit.model.latent.count} {child : Fin S.count}
      (operation : LatentLink.RelateOperation R.baseOfCommit source child) :
      LockStack.topUncommittedEq R.locks .relateLatent →
        CanCommit R S
  | unrelatingLatent {S : ObservedSignature} {R : CausalEpistemicRecord S}
      {source : Fin R.baseOfCommit.model.latent.count} {child : Fin S.count}
      (operation : LatentLink.UnrelateOperation R.baseOfCommit source child) :
      LockStack.topUncommittedEq R.locks .unrelateLatent →
        CanCommit R S
  | replaceMechanismAt {S : ObservedSignature} {R : CausalEpistemicRecord S}
      {target : Fin S.count}
      (operation : StructuralSetting.Operation R.baseOfCommit target) :
      LockStack.topUncommittedEq R.locks .replaceMechanism →
        CanCommit R S
  | replaceMechanisms {S : ObservedSignature} {R : CausalEpistemicRecord S}
      (operation : StructuralMechanismReplacement.Operation R.baseOfCommit) :
      LockStack.topUncommittedEq R.locks .replaceMechanism →
        CanCommit R S
  | settingMechanism {S : ObservedSignature} {R : CausalEpistemicRecord S}
      (target : Fin S.count) (value : S.Value target) :
      LockStack.topUncommittedEq R.locks .replaceMechanism →
        CanCommit R S
  | reindexingBelief {S : ObservedSignature} {R : CausalEpistemicRecord S}
      (operation : BeliefReindexing.CertifiedOperation R.baseOfCommit) :
      LockStack.topUncommittedEq R.locks .reindexBelief →
        CanCommit R S
  | surgery {S : ObservedSignature} {R : CausalEpistemicRecord S}
      (action : (node : Fin S.count) -> Option (S.Value node)) :
      LockStack.topPendingEq R.locks .surgery →
        CanCommit R (SurgicalIntervention.signature R.baseOfCommit.model action)

/--
Realise the current top marker.  Forward constructors run the follower.
Provenance inverses restore a snapshot; structural reverses apply the
named reverse edit.
-/
def commit {S T : ObservedSignature} {R : CausalEpistemicRecord S}
    (h : CanCommit R T) : CausalEpistemicRecord T :=
  match h with
  | .pearl hPearl => R.commitPearl hPearl
  | .learnTerminal spec _ => spec.learnRecord R.baseOfCommit
  | .learnEndogenous spec _ => spec.learnRecord
  | .forgetTerminal original spec _ heq =>
      -- `heq` requires the learn `across` frame; the snapshot is `original`.
      original
  | .forgetEndogenous original spec _ _ =>
      original
  | .forgetUnusedEndogenous spec _ => spec.deleteRecord R.baseOfCommit
  | .learnExogenous spec _ => spec.learnRecord R.baseOfCommit
  | .forgetExogenous _ _ => restoreTop R.baseOfCommit
  | .forgetUnusedExogenous spec _ =>
      ExogenousDeletionSpec.deleteRecord (record := R.baseOfCommit) spec
  | .relatingDirected operation _ => operation.apply R.baseOfCommit
  | .unrelatingDirected operation _ => operation.apply R.baseOfCommit
  | .relatingLatent operation _ => operation.apply
  | .unrelatingLatent operation _ => operation.apply
  | .replaceMechanismAt operation _ => operation.apply
  | .replaceMechanisms operation _ => operation.apply
  | .settingMechanism target value _ =>
      StructuralSetting.applyConstant R.baseOfCommit target value
  | .reindexingBelief operation _ => operation.apply
  | .surgery action _ => SurgicalIntervention.apply R.baseOfCommit action

@[simp] theorem commit_pearl {S : ObservedSignature}
    (R : CausalEpistemicRecord S) (h : CanCommitPearl R) :
    R.commit (.pearl h) = R.commitPearl h :=
  rfl

end CausalEpistemicRecord

namespace TerminalVariableSpec

theorem learnRecord_eq_announce_commit (spec : TerminalVariableSpec S)
    (R : CausalEpistemicRecord S) :
    spec.learnRecord R =
      (R.announceAcross .learnTerminal).commit
        (.learnTerminal spec (by simp [CausalEpistemicRecord.announceAcross])) := by
  simp [learnRecord, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announceAcross, CausalEpistemicRecord.baseOfCommit]

theorem forgetRecord_eq_announce_commit (spec : TerminalVariableSpec S)
    (original : CausalEpistemicRecord S) :
    original =
      ((spec.learnRecord original).announceAcross .forgetTerminal).commit
        (.forgetTerminal original spec
          (by simp [CausalEpistemicRecord.announceAcross])
          (by
            simp [CausalEpistemicRecord.baseOfCommit_announceAcross,
              learnRecord])) :=
  rfl

end TerminalVariableSpec

namespace EndogenousVariableSpec

theorem learnRecord_eq_announce_commit {S : ObservedSignature}
    {R : CausalEpistemicRecord S} (spec : EndogenousVariableSpec R) :
    spec.learnRecord =
      (R.announceAcross .learnEndogenous).commit
        (.learnEndogenous (by
          simpa [CausalEpistemicRecord.baseOfCommit_announceAcross] using spec)
          (by simp [CausalEpistemicRecord.announceAcross])) := by
  simp [learnRecord, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announceAcross, CausalEpistemicRecord.baseOfCommit]

theorem forgetRecord_eq_announce_commit {S : ObservedSignature}
    {original : CausalEpistemicRecord S} (spec : EndogenousVariableSpec original) :
    original =
      (spec.learnRecord.announceAcross .forgetEndogenous).commit
        (.forgetEndogenous original spec
          (by simp [CausalEpistemicRecord.announceAcross])
          (by simp [CausalEpistemicRecord.baseOfCommit_announceAcross])) :=
  rfl

end EndogenousVariableSpec

namespace ExogenousVariableSpec

theorem learnRecord_eq_announce_commit (spec : ExogenousVariableSpec)
    (R : CausalEpistemicRecord S) :
    spec.learnRecord R =
      (R.announce .learnExogenous).commit
        (.learnExogenous spec (by simp [CausalEpistemicRecord.announce])) := by
  simp [CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announce, CausalEpistemicRecord.baseOfCommit]

theorem forgetRecord_eq_announce_commit (spec : ExogenousVariableSpec)
    (original : CausalEpistemicRecord S) :
    original =
      ((spec.learnRecord original).announce .forgetExogenous).commit
        (.forgetExogenous
          (by simp [CausalEpistemicRecord.announce])
          (by
            simp [CausalEpistemicRecord.baseOfCommit_announce,
              CausalEpistemicRecord.ForgetExogenousReady,
              LockStack.forgetExogenousReady, learnRecord,
              CausalEpistemicRecord.executedLocks])) := by
  cases original
  simp [CausalEpistemicRecord.commit, CausalEpistemicRecord.announce,
    CausalEpistemicRecord.baseOfCommit, learnRecord,
    CausalEpistemicRecord.executedLocks, CausalEpistemicRecord.restoreTop]

end ExogenousVariableSpec

namespace DirectedLink

namespace RelateOperation

theorem apply_eq_announce_commit
    (operation : RelateOperation S parent child earlier)
    (R : CausalEpistemicRecord S) :
    operation.apply R =
      (R.announceAcross .relateDirected).commit
        (.relatingDirected operation
          (by simp [CausalEpistemicRecord.announceAcross])) := by
  simp [apply, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announceAcross, CausalEpistemicRecord.baseOfCommit]

end RelateOperation

namespace UnrelateOperation

theorem apply_eq_announce_commit
    (operation : UnrelateOperation S parent child)
    (R : CausalEpistemicRecord S) :
    operation.apply R =
      (R.announceAcross .unrelateDirected).commit
        (.unrelatingDirected operation
          (by simp [CausalEpistemicRecord.announceAcross])) := by
  simp [apply, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announceAcross, CausalEpistemicRecord.baseOfCommit]

end UnrelateOperation

end DirectedLink

namespace LatentLink

namespace RelateOperation

theorem apply_eq_announce_commit {S : ObservedSignature}
    {R : CausalEpistemicRecord S}
    {source : Fin R.model.latent.count} {child : Fin S.count}
    (operation : RelateOperation R source child) :
    operation.apply =
      (R.announce .relateLatent).commit
        (.relatingLatent
          (by simpa [CausalEpistemicRecord.baseOfCommit_announce] using operation)
          (by simp [CausalEpistemicRecord.announce])) := by
  simp [apply, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announce, CausalEpistemicRecord.baseOfCommit]

end RelateOperation

namespace UnrelateOperation

theorem apply_eq_announce_commit {S : ObservedSignature}
    {R : CausalEpistemicRecord S}
    {source : Fin R.model.latent.count} {child : Fin S.count}
    (operation : UnrelateOperation R source child) :
    operation.apply =
      (R.announce .unrelateLatent).commit
        (.unrelatingLatent
          (by simpa [CausalEpistemicRecord.baseOfCommit_announce] using operation)
          (by simp [CausalEpistemicRecord.announce])) := by
  simp [apply, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announce, CausalEpistemicRecord.baseOfCommit]

end UnrelateOperation

end LatentLink

namespace StructuralSetting

namespace Operation

theorem apply_eq_announce_commit {S : ObservedSignature}
    {R : CausalEpistemicRecord S} {target : Fin S.count}
    (operation : Operation R target) :
    operation.apply =
      (R.announce .replaceMechanism).commit
        (.replaceMechanismAt
          (by simpa [CausalEpistemicRecord.baseOfCommit_announce] using operation)
          (by simp [CausalEpistemicRecord.announce])) := by
  simp [apply, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announce, CausalEpistemicRecord.baseOfCommit]

end Operation

theorem applyConstant_eq_announce_commit {S : ObservedSignature}
    (R : CausalEpistemicRecord S) (target : Fin S.count)
    (value : S.Value target) :
    applyConstant R target value =
      (R.announce .replaceMechanism).commit
        (.settingMechanism target value
          (by simp [CausalEpistemicRecord.announce])) := by
  simp [applyConstant, constantOperation, Operation.apply,
    CausalEpistemicRecord.commit, CausalEpistemicRecord.announce,
    CausalEpistemicRecord.baseOfCommit]

end StructuralSetting

namespace StructuralMechanismReplacement

namespace Operation

theorem apply_eq_announce_commit {S : ObservedSignature}
    {R : CausalEpistemicRecord S} (operation : Operation R) :
    operation.apply =
      (R.announce .replaceMechanism).commit
        (.replaceMechanisms
          (by simpa [CausalEpistemicRecord.baseOfCommit_announce] using operation)
          (by simp [CausalEpistemicRecord.announce])) := by
  simp [apply, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announce, CausalEpistemicRecord.baseOfCommit]

end Operation

end StructuralMechanismReplacement

namespace BeliefReindexing

namespace CertifiedOperation

theorem apply_eq_announce_commit {S : ObservedSignature.{0}}
    {R : CausalEpistemicRecord S} (operation : CertifiedOperation R) :
    operation.apply =
      (R.announce .reindexBelief).commit
        (.reindexingBelief
          (by simpa [CausalEpistemicRecord.baseOfCommit_announce] using operation)
          (by simp [CausalEpistemicRecord.announce])) := by
  simp [apply, toOperation, Operation.apply, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announce, CausalEpistemicRecord.baseOfCommit]

end CertifiedOperation

end BeliefReindexing

namespace SurgicalIntervention

theorem apply_eq_announce_commit (R : CausalEpistemicRecord S)
    (action : (node : Fin S.count) -> Option (S.Value node)) :
    apply R action =
      (R.announceAcross .surgery).commit
        (.surgery action (by simp [CausalEpistemicRecord.announceAcross])) := by
  simp [apply, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announceAcross, CausalEpistemicRecord.baseOfCommit]

end SurgicalIntervention

namespace ObservedDeletionSpec

theorem deleteRecord_eq_announce_commit (spec : ObservedDeletionSpec S)
    (record : CausalEpistemicRecord S) :
    spec.deleteRecord record =
      (record.announceAcross .forgetUnusedEndogenous).commit
        (.forgetUnusedEndogenous spec
          (by simp [CausalEpistemicRecord.announceAcross])) := by
  simp [deleteRecord, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announceAcross, CausalEpistemicRecord.baseOfCommit]

end ObservedDeletionSpec

namespace ExogenousDeletionSpec

theorem deleteRecord_eq_announce_commit {S : ObservedSignature}
    (record : CausalEpistemicRecord S)
    (spec : ExogenousDeletionSpec record.model) :
    spec.deleteRecord =
      (record.announce .forgetUnusedExogenous).commit
        (.forgetUnusedExogenous
          (by simpa [CausalEpistemicRecord.baseOfCommit_announce] using spec)
          (by simp [CausalEpistemicRecord.announce])) := by
  simp [deleteRecord, CausalEpistemicRecord.commit,
    CausalEpistemicRecord.announce, CausalEpistemicRecord.baseOfCommit]

end ExogenousDeletionSpec

namespace CausalEpistemicRecord

theorem setVariable_eq_announce_commit_public
    (R : CausalEpistemicRecord S) (target : Fin S.count)
    (value : S.Value target) :
    R.setVariable target value =
      (R.announce (.set target value)).commit
        (.pearl (.set target value (announce_topUncommittedEq R _))) := by
  simpa [commit_pearl] using (setVariable_eq_announce_commit R target value)

end CausalEpistemicRecord

end Causality
end Thesis
