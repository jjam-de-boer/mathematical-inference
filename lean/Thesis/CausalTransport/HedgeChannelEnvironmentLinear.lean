import Thesis.CausalTransport.HedgeChannelEnvironmentCube
import Thesis.Probability.FiniteBooleanCylinderCovariance

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability
open HedgeChannelInstallation

/-!
# Legal local XOR signals and their actual homogeneous cube phases

The interaction inequalities cannot be applied to an arbitrary parent signal:
its actual phase must be homogeneous and XOR-additive on the complete cube.
This module constructs a concrete local signal family from Boolean parent and
incident-root masks, and proves those properties for the functions installed
in the model.  They are theorems, not extra readiness flags.

A parent mask entry is read only behind its actual directed-edge guard.
A root mask entry is read only behind its actual pair-root incidence guard.
Off-graph mask entries are ignored, so even a mask awaiting its graph proof
never grants access to an unavailable input.  The whole cube occurs only in
the proof-level evaluation of the legal local function; no model mechanism
receives that cube or another child's latent inputs.

Both local folds begin at false, with no constant odd offset.  Their exact
zero and XOR identities give a homogeneous phase for each actual observed
row.  Folding any supplied forest's rows gives its actual full signal phase,
including every original small-forest coordinate and every selected incident
environment bit.  These identities cover arbitrary masks without enumerating
a concrete exponential cube.

This is the local-function part of the conditional countermodel argument.
An arbitrary terminal active path must still supply masks and strict parity
data for the complete normalized query.  Local homogeneity alone does not
prove that universal graph obligation.
-/

variable {S : ObservedSignature.{0}}

/-- Explicit masks for a legal local homogeneous signal family.  The
interpreter guards each read by its actual edge or incidence, rather than
assuming that an unrestricted mask denotes available model inputs. -/
structure LinearSignal (G : ObservedGraph S) where
  parentMask : Fin S.count -> Fin S.count -> Bool
  rootMask : Fin S.count -> Fin (pairRootCount G.binary) -> Bool

namespace LinearSignal

variable {G : ObservedGraph S}

private def parentEntry (data : LinearSignal G) (child : Fin S.count)
    (parents : S.binary.ParentValues child) (parent : Fin S.count) : Bool :=
  if edge : S.directed parent child = true then
    if data.parentMask child parent then parents parent edge else false
  else false

private def rootEntry (data : LinearSignal G) (child : Fin S.count)
    (inputs : EnvironmentInputs G child) (root : Fin (pairRootCount G.binary)) : Bool :=
  if incident : pairRootIncident G.binary root child = true then
    if data.rootMask child root then inputs root incident else false
  else false

/-- The actual local parent signal installed in both countermodels.  Its
two finite XOR folds read only typed declared parents and incident reserved
bits; a shared root is not replaced by an observed parent's value. -/
def signal (data : LinearSignal G) : ParentSignal G :=
  fun child parents inputs => Bool.xor
    ((List.finRange S.count).foldl (fun total parent => Bool.xor total (parentEntry data child parents parent)) false)
    ((List.finRange (pairRootCount G.binary)).foldl (fun total root => Bool.xor total (rootEntry data child inputs root)) false)

private theorem parentEntry_zero (data : LinearSignal G) (child parent : Fin S.count) :
    parentEntry data child (fun _ _ => false) parent = false := by
  unfold parentEntry
  split <;> simp only [ite_self]

private theorem rootEntry_zero (data : LinearSignal G) (child : Fin S.count) (root : Fin (pairRootCount G.binary)) :
    rootEntry data child (fun _ _ => false) root = false := by
  unfold rootEntry
  split <;> simp only [ite_self]

/-- The installed signal has no hidden constant phase.  Every selected
actual input is false at the local zero assignment, including reserved bits. -/
theorem signal_zero (data : LinearSignal G) (child : Fin S.count) :
    signal data child (fun _ _ => false) (fun _ _ => false) = false := by
  have parentsZero : (List.finRange S.count).foldl
      (fun total parent => Bool.xor total (parentEntry data child (fun _ _ => false) parent)) false = false := by
    apply foldl_unchanged
    intro total parent
    rw [parentEntry_zero, Bool.xor_false]
  have rootsZero : (List.finRange (pairRootCount G.binary)).foldl
      (fun total root => Bool.xor total (rootEntry data child (fun _ _ => false) root)) false = false := by
    apply foldl_unchanged
    intro total root
    rw [rootEntry_zero, Bool.xor_false]
  unfold signal
  rw [parentsZero, rootsZero]
  rfl

private theorem parentEntry_xor (data : LinearSignal G) (child parent : Fin S.count)
    (left right : S.binary.ParentValues child) :
    parentEntry data child (fun node edge => Bool.xor (left node edge) (right node edge)) parent =
      Bool.xor (parentEntry data child left parent) (parentEntry data child right parent) := by
  unfold parentEntry
  by_cases edge : S.directed parent child = true
  · rw [dif_pos edge, dif_pos edge, dif_pos edge]
    cases data.parentMask child parent <;> rfl
  · rw [dif_neg edge, dif_neg edge, dif_neg edge]
    rfl

private theorem rootEntry_xor (data : LinearSignal G) (child : Fin S.count) (root : Fin (pairRootCount G.binary))
    (left right : EnvironmentInputs G child) :
    rootEntry data child (fun source incident => Bool.xor (left source incident) (right source incident)) root =
      Bool.xor (rootEntry data child left root) (rootEntry data child right root) := by
  unfold rootEntry
  by_cases incident : pairRootIncident G.binary root child = true
  · rw [dif_pos incident, dif_pos incident, dif_pos incident]
    cases data.rootMask child root <;> rfl
  · rw [dif_neg incident, dif_neg incident, dif_neg incident]
    rfl

/-- Exact additivity of the legal local function on its actual typed inputs.
The two folds are distributed before being combined, retaining all selected
parent and incident-root contributions even when several share an input. -/
theorem signal_xor (data : LinearSignal G) (child : Fin S.count)
    (leftParents rightParents : S.binary.ParentValues child)
    (leftInputs rightInputs : EnvironmentInputs G child) :
    signal data child (fun parent edge => Bool.xor (leftParents parent edge) (rightParents parent edge))
        (fun root incident => Bool.xor (leftInputs root incident) (rightInputs root incident)) =
      Bool.xor (signal data child leftParents leftInputs) (signal data child rightParents rightInputs) := by
  have parentsXor := (foldl_congr _ _ false (List.finRange S.count)
    (fun total parent => congrArg (Bool.xor total) (parentEntry_xor data child parent leftParents rightParents))).trans
      (foldl_xor_pointwise _ _ (List.finRange S.count))
  have rootsXor := (foldl_congr _ _ false (List.finRange (pairRootCount G.binary))
    (fun total root => congrArg (Bool.xor total) (rootEntry_xor data child root leftInputs rightInputs))).trans
      (foldl_xor_pointwise _ _ (List.finRange (pairRootCount G.binary)))
  unfold signal
  rw [parentsXor, rootsXor]
  generalize (List.finRange S.count).foldl _ false = first
  generalize (List.finRange S.count).foldl _ false = second
  generalize (List.finRange (pairRootCount G.binary)).foldl _ false = third
  generalize (List.finRange (pairRootCount G.binary)).foldl _ false = fourth
  cases first <;> cases second <;> cases third <;> cases fourth <;> rfl

/-- The homogeneous phase of one actual installed row.  Cube evaluation
recovers the child's typed inputs; its proof does not expose a cube to the
mechanism.  The row's own observed bit is retained in the character. -/
def rowPhase (data : LinearSignal G) (child : Fin S.count) :
    FiniteBooleanInteraction.HomogeneousPhase (pairRootCount G.binary + S.count) where
  value := fun point => Bool.xor (cubeSample G point child)
    (frozenParentSignal data.signal (cubeEnvironment G point) child (fun parent _edge => cubeSample G point parent))
  at_zero := by
    change Bool.xor false (signal data child (fun _ _ => false) (fun _ _ => false)) = false
    rw [signal_zero]
    rfl
  xor_additive := by
    intro left right
    change Bool.xor (Bool.xor (cubeSample G left child) (cubeSample G right child))
        (signal data child (fun parent _edge => Bool.xor (cubeSample G left parent) (cubeSample G right parent))
          (fun root _incident => Bool.xor (cubeEnvironment G left root) (cubeEnvironment G right root))) =
      Bool.xor
        (Bool.xor (cubeSample G left child)
          (signal data child (fun parent _edge => cubeSample G left parent) (fun root _incident => cubeEnvironment G left root)))
        (Bool.xor (cubeSample G right child)
          (signal data child (fun parent _edge => cubeSample G right parent) (fun root _incident => cubeEnvironment G right root)))
    rw [signal_xor]
    generalize cubeSample G left child = first
    generalize cubeSample G right child = second
    generalize signal data child _ _ = third
    generalize signal data child _ _ = fourth
    cases first <;> cases second <;> cases third <;> cases fourth <;> rfl

/-- Any selected forest's actual whole signal phase is homogeneous on the
same complete cube.  In particular the full small forest is not replaced by
one selected vertex when the conditional perturbation is compared. -/
def forestPhase (data : LinearSignal G) (nodes : NodeSet S) :
    FiniteBooleanInteraction.HomogeneousPhase (pairRootCount G.binary + S.count) where
  value := fun point => signalPhase nodes (frozenParentSignal data.signal (cubeEnvironment G point)) (cubeSample G point)
  at_zero := by
    unfold signalPhase
    apply foldl_unchanged
    intro total child
    change Bool.xor total ((rowPhase data child).value (fun _ => false)) = total
    rw [(rowPhase data child).at_zero, Bool.xor_false]
  xor_additive := by
    intro left right
    unfold signalPhase
    exact (foldl_congr _ _ false (NodeSet.members nodes)
      (fun total child => congrArg (Bool.xor total) ((rowPhase data child).xor_additive left right))).trans
        (foldl_xor_pointwise _ _ (NodeSet.members nodes))

/-- Expand the actual installed row into its guarded cube-coordinate folds.
This proof-level calculation retains the declared-edge and root-incidence
guards, but does not expose the private typed-input interpreter.  It is useful
for checking concrete routing masks without unfolding model construction,
forest certificates, or the much larger likelihood support. -/
theorem rowPhase_value (data : LinearSignal G) (child : Fin S.count) (point : Cube G) :
    (rowPhase data child).value point = Bool.xor (cubeSample G point child)
      (Bool.xor
        ((List.finRange S.count).foldl (fun total parent => Bool.xor total
          (if S.directed parent child = true then
            if data.parentMask child parent then cubeSample G point parent else false
          else false)) false)
        ((List.finRange (pairRootCount G.binary)).foldl (fun total root => Bool.xor total
          (if pairRootIncident G.binary root child = true then
            if data.rootMask child root then cubeEnvironment G point root else false
          else false)) false)) := rfl

/-- Expand the full forest phase into exactly its actual member-row fold.
The forest remains arbitrary; this identity does not select one endpoint or
discard an unqueried small-forest row when checking a conditional character. -/
theorem forestPhase_value (data : LinearSignal G) (nodes : NodeSet S) (point : Cube G) :
    (forestPhase data nodes).value point =
      (NodeSet.members nodes).foldl (fun total child => Bool.xor total ((rowPhase data child).value point)) false := rfl

end LinearSignal
end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
