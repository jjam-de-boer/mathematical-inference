import Thesis.CausalTransport.Correspondence
import Thesis.Causality.Reductions

namespace Thesis
namespace Causality

open Probability

namespace FiniteHiddenDAG

abbrev Assignment (H : FiniteHiddenDAG S)
    (Value : Fin H.count -> Type u) :=
  (node : Fin H.count) -> Value node

def ParentValues (H : FiniteHiddenDAG S)
    (Value : Fin H.count -> Type u) (child : Fin H.count) :=
  (parent : Fin H.count) -> H.edge parent child = true -> Value parent

end FiniteHiddenDAG

/-- Constructive two-sided conversion between value presentations. -/
structure ValueEquivalence (left : Type u) (right : Type v) where
  forward : left -> right
  backward : right -> left
  forward_backward : forall value, forward (backward value) = value
  backward_forward : forall value, backward (forward value) = value

/-!
A structurally generated SCM over a full finite hidden DAG.

Every node has private exogenous noise.  Shared observed dependence is induced
by directed paths through explicit hidden nodes, not by arbitrary probability
tables attached after projection.
-/
structure FiniteHiddenDAGSCM.{u} (S : ObservedSignature.{u})
    (projection : FiniteLatentProjection S) where
  NodeValue : Fin projection.hiddenDAG.count -> Type u
  nodeEnumeration : (node : Fin projection.hiddenDAG.count) ->
    List (NodeValue node)
  node_complete : forall node value, value ∈ nodeEnumeration node
  nodeDecidableEq : (node : Fin projection.hiddenDAG.count) ->
    DecidableEq (NodeValue node)
  observedEquiv : (i : Fin S.count) ->
    ValueEquivalence
      (NodeValue (projection.hiddenDAG.observedNode i)) (S.Value i)
  observedIndex : Fin projection.hiddenDAG.count -> Option (Fin S.count)
  observedIndex_observed : forall i,
    observedIndex (projection.hiddenDAG.observedNode i) = some i
  observedIndex_sound : forall node i,
    observedIndex node = some i -> projection.hiddenDAG.observedNode i = node
  hidden_has_no_observed_index : forall node,
    projection.hiddenDAG.hidden node = true -> observedIndex node = none
  Noise : Fin projection.hiddenDAG.count -> Type u
  noiseEnumeration : (node : Fin projection.hiddenDAG.count) -> List (Noise node)
  noise_complete : forall node value, value ∈ noiseEnumeration node
  noiseDecidableEq : (node : Fin projection.hiddenDAG.count) ->
    DecidableEq (Noise node)
  factor : (node : Fin projection.hiddenDAG.count) ->
    FiniteProbRecord (Noise node)
  prior : FiniteProbRecord (projection.hiddenDAG.Assignment Noise)
  product_law :
    forall events : (node : Fin projection.hiddenDAG.count) -> Noise node -> Bool,
      QProb.Equiv
        (prior.probVal
          (FiniteProduct.rectangularEvent
            projection.hiddenDAG.count Noise events))
        (FiniteProduct.qProduct projection.hiddenDAG.count
          (fun node => (factor node).probVal (events node)))
  mechanism :
    (child : Fin projection.hiddenDAG.count) ->
      projection.hiddenDAG.ParentValues NodeValue child ->
      Noise child -> NodeValue child

namespace FiniteHiddenDAGSCM

instance (M : FiniteHiddenDAGSCM S projection)
    (node : Fin projection.hiddenDAG.count) : DecidableEq (M.NodeValue node) :=
  M.nodeDecidableEq node

instance (M : FiniteHiddenDAGSCM S projection)
    (node : Fin projection.hiddenDAG.count) : DecidableEq (M.Noise node) :=
  M.noiseDecidableEq node

abbrev NodeAssignment (M : FiniteHiddenDAGSCM S projection) :=
  projection.hiddenDAG.Assignment M.NodeValue

abbrev NoiseAssignment (M : FiniteHiddenDAGSCM S projection) :=
  projection.hiddenDAG.Assignment M.Noise

def interventionValueAt (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S)
    (node : Fin projection.hiddenDAG.count) : Option (M.NodeValue node) :=
  match hindex : M.observedIndex node with
  | none => none
  | some i =>
      match intervention.value i with
      | none => none
      | some value =>
          some (M.observedIndex_sound node i hindex ▸
            (M.observedEquiv i).backward value)

/-- Well-founded structural evaluation along the full DAG rank. -/
def evalNode (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) (noise : M.NoiseAssignment)
    (node : Fin projection.hiddenDAG.count) : M.NodeValue node :=
  match M.interventionValueAt intervention node with
  | some value => value
  | none =>
      M.mechanism node
        (fun parent _edge => M.evalNode intervention noise parent)
        (noise node)
termination_by projection.hiddenDAG.rank node
decreasing_by
  exact projection.hiddenDAG.edge_rank_lt _edge

def evalFull (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) (noise : M.NoiseAssignment) :
    M.NodeAssignment :=
  fun node => M.evalNode intervention noise node

def evalObserved (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) (noise : M.NoiseAssignment) :
    S.Assignment :=
  fun i => (M.observedEquiv i).forward
    (M.evalNode intervention noise (projection.hiddenDAG.observedNode i))

def observationalDist (M : FiniteHiddenDAGSCM S projection) :
    FiniteProbRecord S.Assignment :=
  M.prior.map (M.evalObserved (HardIntervention.empty S))

def interventionalDist (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) : FiniteProbRecord S.Assignment :=
  M.prior.map (M.evalObserved intervention)

def observationalValue (M : FiniteHiddenDAGSCM S projection)
    (event : S.Assignment -> Bool) : QProb :=
  M.observationalDist.probVal event

def interventionalValue (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S)
    (event : S.Assignment -> Bool) : QProb :=
  (M.interventionalDist intervention).probVal event

end FiniteHiddenDAGSCM

end Causality
end Thesis
