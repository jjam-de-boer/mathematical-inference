import Thesis.CausalTransport.HiddenDAGPlacedNoise
import Thesis.CausalTransport.HiddenDAGFullFamily
import Thesis.Probability.FiniteRecordDefaults

namespace Thesis
namespace Causality

open Probability

/-!
# Finite value presentations for reverse hidden-DAG relays

Observed nodes retain exactly their original domains.  Hidden nodes carry
two finite vectors: observed-parent signals and canonical latent-root inputs.
Different signals remain different coordinates, even when they share paths.
Both vector presentations and their complete enumerations are explicit.

Off-route inputs use the observed signature's supplied defaults and concrete
first labels of root-factor records.  Those labels need not have positive
mass.  They make equations total without choice; they do not justify any
probability or support claim.  The relay preservation argument must separately
prove that every required active input reads its actual routed value.

The carrier universe matches the existing identification/certificate APIs;
the finite sizes of hidden values and private-noise vectors are unrestricted.
-/

namespace HiddenDAGRelay

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- A finite vector of parent signals and a separate finite vector of root
inputs.  The hidden alphabet can grow as needed; observed alphabets do not. -/
abbrev Payload (model : ExactModel S) := S.Assignment × model.latent.Assignment

/-- Total off-route root inputs read an actual stored label of each factor,
not a representative selected from a propositional nonemptiness proof. -/
def defaultRoots (model : ExactModel S) : model.latent.Assignment :=
  fun root => (model.factor root).firstLabel

def defaultPayload (model : ExactModel S) : Payload model :=
  ⟨S.defaultValue, defaultRoots model⟩

/-- The complete product list, not just the positive support of the noise
law.  Hidden equations are total on their whole declared finite alphabet. -/
def payloadEnumeration (model : ExactModel S) : List (Payload model) :=
  S.assignmentEnumeration.flatMap fun signals =>
    (FiniteProduct.enumeration model.latent.count model.latent.Value
      model.latent.valueEnumeration).map (fun roots => (signals, roots))

theorem payloadEnumeration_complete (model : ExactModel S) (payload : Payload model) :
    payload ∈ payloadEnumeration model := by
  refine List.mem_flatMap.mpr ⟨payload.1, S.assignmentEnumeration_complete payload.1, ?_⟩
  exact List.mem_map.mpr ⟨payload.2,
    FiniteProduct.enumeration_complete model.latent.count model.latent.Value
      model.latent.valueEnumeration model.latent.value_complete payload.2, rfl⟩

/-- Keep each node's domain and finite presentation together.  Matching the
computed observed index then selects an observed domain or a relay payload
without choosing an inverse of the observed embedding. -/
private structure NodePresentation where
  Value : Type
  enumeration : List Value
  complete : forall value, value ∈ enumeration
  valueDecidableEq : DecidableEq Value

private def nodePresentation (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count) : NodePresentation :=
  match projection.hiddenDAG.observedIndex node with
  | none => {
      Value := Payload model
      enumeration := payloadEnumeration model
      complete := payloadEnumeration_complete model
      valueDecidableEq := inferInstance }
  | some index => {
      Value := S.Value index
      enumeration := S.valueEnumeration index
      complete := S.value_complete index
      valueDecidableEq := S.valueDecidableEq index }

def NodeValue (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count) : Type :=
  (nodePresentation model projection node).Value

def nodeEnumeration (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count) : List (NodeValue model projection node) :=
  (nodePresentation model projection node).enumeration

theorem node_complete (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count) :
    forall value, value ∈ nodeEnumeration model projection node :=
  (nodePresentation model projection node).complete

def nodeDecidableEq (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count) : DecidableEq (NodeValue model projection node) :=
  (nodePresentation model projection node).valueDecidableEq

/-- Exact type equality on a computed hidden-node branch.  This equality is
used only to read or pack the same payload, never to select a new value. -/
theorem nodeValue_of_none (model : ExactModel S) (node : Fin P.hiddenDAG.count)
    (missing : P.hiddenDAG.observedIndex node = none) :
    NodeValue model P node = Payload model := by
  unfold NodeValue nodePresentation
  rw [missing]

/-- Exact type equality on a computed observed-node branch. -/
theorem nodeValue_of_some (model : ExactModel S) (node : Fin P.hiddenDAG.count)
    (index : Fin S.count) (found : P.hiddenDAG.observedIndex node = some index) :
    NodeValue model P node = S.Value index := by
  unfold NodeValue nodePresentation
  rw [found]

/-- Converting a supplied value across a proved type equality and back is
literal identity.  These small transport laws eliminate only equality casts;
they neither select values nor assume an extensional semantic equivalence. -/
private theorem transport_forward_backward {left right : Type} (same : left = right)
    (value : right) : same.mp (same.mpr value) = value := by
  cases same
  rfl

private theorem transport_backward_forward {left right : Type} (same : left = right)
    (value : left) : same.mpr (same.mp value) = value := by
  cases same
  rfl

/-- The original observed domain is unchanged, with explicit forward and
backward conversion and both inverse laws. -/
def observedEquivalence (model : ExactModel S) (projection : FiniteLatentProjection S)
    (index : Fin S.count) :
    ValueEquivalence (NodeValue model projection (projection.hiddenDAG.observedNode index))
      (S.Value index) := by
  let same := nodeValue_of_some (P := projection) model
    (projection.hiddenDAG.observedNode index) index
    (projection.hiddenDAG.observedIndex_observed index)
  exact ⟨same.mp, same.mpr, transport_forward_backward same,
    transport_backward_forward same⟩

/-- An incoming observed node supplies only its own observed coordinate.
An incoming hidden node supplies the corresponding payload signal.  A
different observed node is not permitted to stand in for the requested one. -/
def readSignal (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count) (value : NodeValue model projection node)
    (index : Fin S.count) : S.Value index :=
  match found : projection.hiddenDAG.observedIndex node with
  | none => ((nodeValue_of_none model node found).mp value).1 index
  | some ownIndex =>
      if same : ownIndex = index then
        same ▸ (nodeValue_of_some model node ownIndex found).mp value
      else S.defaultValue index

/-- Root inputs are carried only by hidden payloads.  An unrelated observed
node is never treated as exposing its private noise to a relay mechanism. -/
def readRoot (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count) (value : NodeValue model projection node)
    (root : Fin model.latent.count) : model.latent.Value root :=
  match found : projection.hiddenDAG.observedIndex node with
  | none => ((nodeValue_of_none model node found).mp value).2 root
  | some _ => defaultRoots model root

/-! ## Read back explicitly packed node values -/

/-- A packed hidden payload exposes exactly its observed-signal coordinate.
The proof handles the dependent lookup without rewriting a cast-bearing
match, then cancels the two transports using proof irrelevance. -/
theorem readSignal_hidden (model : ExactModel S) (node : Fin P.hiddenDAG.count)
    (missing : P.hiddenDAG.observedIndex node = none) (payload : Payload model)
    (index : Fin S.count) :
    readSignal model P node ((nodeValue_of_none model node missing).mpr payload) index =
      payload.1 index := by
  unfold readSignal
  split
  · exact congrArg (fun carried : Payload model => carried.1 index)
      (transport_forward_backward (nodeValue_of_none model node missing) payload)
  · rename_i ownIndex found
    rw [missing] at found
    cases found

/-- A packed hidden payload exposes exactly its independent root-input
coordinate; the root and observed signal vectors are never merged. -/
theorem readRoot_hidden (model : ExactModel S) (node : Fin P.hiddenDAG.count)
    (missing : P.hiddenDAG.observedIndex node = none) (payload : Payload model)
    (root : Fin model.latent.count) :
    readRoot model P node ((nodeValue_of_none model node missing).mpr payload) root =
      payload.2 root := by
  unfold readRoot
  split
  · exact congrArg (fun carried : Payload model => carried.2 root)
      (transport_forward_backward (nodeValue_of_none model node missing) payload)
  · rename_i ownIndex found
    rw [missing] at found
    cases found

/-- An embedded observed node supplies its own original value through the
explicit two-sided presentation, even when that value was forced by an
intervention.  No observed equation is evaluated by this reader. -/
theorem readSignal_observed (model : ExactModel S) (index : Fin S.count)
    (value : S.Value index) :
    readSignal model P (P.hiddenDAG.observedNode index)
      ((observedEquivalence model P index).backward value) index = value := by
  unfold readSignal
  split
  · rename_i missing
    have found := P.hiddenDAG.observedIndex_observed index
    rw [missing] at found
    cases found
  · rename_i ownIndex found
    have same : ownIndex = index := Option.some.inj
      (found.symm.trans (P.hiddenDAG.observedIndex_observed index))
    subst ownIndex
    rw [dif_pos rfl]
    exact transport_forward_backward
      (nodeValue_of_some model (P.hiddenDAG.observedNode index) index found) value

end HiddenDAGRelay
end Causality
end Thesis
