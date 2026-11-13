import Thesis.Causality.HardIntervention
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
An executable finite SCM record over a full finite hidden DAG.

Every node has private exogenous noise. Shared observed dependence is induced
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

/-- Hard observed interventions never force a node with no observed index.
The dependent lookup is split explicitly so its value-conversion proof stays
attached to the branch that produced it. -/
theorem interventionValueAt_eq_none (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) (node : Fin projection.hiddenDAG.count)
    (missing : M.observedIndex node = none) :
    M.interventionValueAt intervention node = none := by
  unfold interventionValueAt
  split
  · rfl
  · rename_i index found
    rw [missing] at found
    cases found

/-- At an embedded observed node the intervention is exactly its supplied
value converted into the node's unchanged observed presentation.  An absent
intervention remains absent; no default conditional or equation is inserted. -/
theorem interventionValueAt_observed_eq_map (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) (index : Fin S.count) :
    M.interventionValueAt intervention (projection.hiddenDAG.observedNode index) =
      (intervention.value index).map (M.observedEquiv index).backward := by
  unfold interventionValueAt
  split
  · rename_i missing
    have found := M.observedIndex_observed index
    rw [missing] at found
    cases found
  · rename_i ownIndex found
    have same : ownIndex = index := Option.some.inj
      (found.symm.trans (M.observedIndex_observed index))
    subst ownIndex
    cases intervention.value index <;> rfl

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

/-- An explicit assignment satisfying every intervened structural equation
is the evaluator's assignment.  This is uniqueness for the finite acyclic
equations, not existence obtained by choice: the candidate and its equation
proof are supplied as data, and each parent comparison recurses along the
graph's strict rank.  Reverse model constructions can therefore prove local
relay equations first, without interleaving two different evaluators. -/
theorem evalNode_eq_of_solution (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) (noise : M.NoiseAssignment)
    (candidate : M.NodeAssignment)
    (solution : forall node, candidate node =
      match M.interventionValueAt intervention node with
      | some value => value
      | none => M.mechanism node (fun parent _edge => candidate parent) (noise node))
    (node : Fin projection.hiddenDAG.count) :
    M.evalNode intervention noise node = candidate node := by
  rw [evalNode, solution node]
  cases M.interventionValueAt intervention node with
  | some => rfl
  | none =>
      apply congrArg (fun parents : projection.hiddenDAG.ParentValues M.NodeValue node =>
        M.mechanism node parents (noise node))
      funext parent edge
      exact evalNode_eq_of_solution M intervention noise candidate solution parent
termination_by projection.hiddenDAG.rank node
decreasing_by exact projection.hiddenDAG.edge_rank_lt edge

/-- The same uniqueness statement for the complete dependent assignment.
No observational positivity or value-domain richness is used. -/
theorem evalFull_eq_of_solution (M : FiniteHiddenDAGSCM S projection)
    (intervention : HardIntervention S) (noise : M.NoiseAssignment)
    (candidate : M.NodeAssignment)
    (solution : forall node, candidate node =
      match M.interventionValueAt intervention node with
      | some value => value
      | none => M.mechanism node (fun parent _edge => candidate parent) (noise node)) :
    M.evalFull intervention noise = candidate := by
  funext node
  exact M.evalNode_eq_of_solution intervention noise candidate solution node

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

/-- Replace one node's mechanism, keeping types, noise, and the DAG.  Any
Janzing-style arrow cut that does not need extra randomness is an instance. -/
def withMechanism (M : FiniteHiddenDAGSCM S projection)
    (child : Fin projection.hiddenDAG.count)
    (newMechanism :
      projection.hiddenDAG.ParentValues M.NodeValue child →
        M.Noise child → M.NodeValue child) :
    FiniteHiddenDAGSCM S projection :=
  { M with
    mechanism := fun node parents seed =>
      if h : node = child then
        h.symm ▸ newMechanism (h ▸ parents) (h ▸ seed)
      else
        M.mechanism node parents seed }

/-- Ignore one incoming parent, substituting a supplied default.  This is
always possible at the original noise type.  A stochastic cut that preserves
`P(Y | PA \ {X})` needs extra randomness when the child's noise is degenerate. -/
def cutIncoming (M : FiniteHiddenDAGSCM S projection)
    (parent child : Fin projection.hiddenDAG.count)
    (_edge : projection.hiddenDAG.edge parent child = true)
    (default : M.NodeValue parent) :
    FiniteHiddenDAGSCM S projection :=
  M.withMechanism child fun parents seed =>
    M.mechanism child
      (fun predecessor edge =>
        if h : predecessor = parent then h ▸ default else parents predecessor edge)
      seed

/-- The rewritten child mechanism is exactly the supplied function.  Noise,
the prior, and every other mechanism stay the original ones. -/
theorem withMechanism_at_child (M : FiniteHiddenDAGSCM S projection)
    (child : Fin projection.hiddenDAG.count)
    (newMechanism :
      projection.hiddenDAG.ParentValues M.NodeValue child →
        M.Noise child → M.NodeValue child)
    (parents : projection.hiddenDAG.ParentValues M.NodeValue child)
    (seed : M.Noise child) :
    (M.withMechanism child newMechanism).mechanism child parents seed =
      newMechanism parents seed := by
  dsimp [withMechanism]
  rw [if_pos rfl]

theorem withMechanism_at_other (M : FiniteHiddenDAGSCM S projection)
    (child node : Fin projection.hiddenDAG.count)
    (newMechanism :
      projection.hiddenDAG.ParentValues M.NodeValue child →
        M.Noise child → M.NodeValue child)
    (parents : projection.hiddenDAG.ParentValues M.NodeValue node)
    (seed : M.Noise node) (different : node ≠ child) :
    (M.withMechanism child newMechanism).mechanism node parents seed =
      M.mechanism node parents seed := by
  dsimp [withMechanism]
  exact dif_neg different

/-- Ignore every parent and emit a function of the child's own noise.
This is a same-type randomized intervention; it cannot enlarge the noise
alphabet or change `NodeValue`. -/
def randomizeWith (M : FiniteHiddenDAGSCM S projection)
    (child : Fin projection.hiddenDAG.count)
    (emit : M.Noise child → M.NodeValue child) :
    FiniteHiddenDAGSCM S projection :=
  M.withMechanism child fun _parents seed => emit seed

theorem randomizeWith_at_child (M : FiniteHiddenDAGSCM S projection)
    (child : Fin projection.hiddenDAG.count)
    (emit : M.Noise child → M.NodeValue child)
    (parents : projection.hiddenDAG.ParentValues M.NodeValue child)
    (seed : M.Noise child) :
    (M.randomizeWith child emit).mechanism child parents seed = emit seed := by
  simpa only [randomizeWith] using
    M.withMechanism_at_child child (fun _parents seed => emit seed) parents seed

/-- Same-type incoming cut at the child: the parent coordinate is replaced by
the supplied default before the original mechanism runs. -/
theorem cutIncoming_at_child (M : FiniteHiddenDAGSCM S projection)
    (parent child : Fin projection.hiddenDAG.count)
    (edge : projection.hiddenDAG.edge parent child = true)
    (default : M.NodeValue parent)
    (parents : projection.hiddenDAG.ParentValues M.NodeValue child)
    (seed : M.Noise child) :
    (M.cutIncoming parent child edge default).mechanism child parents seed =
      M.mechanism child
        (fun predecessor incident =>
          if h : predecessor = parent then h ▸ default else parents predecessor incident)
        seed := by
  simpa only [cutIncoming] using
    M.withMechanism_at_child child
      (fun parents seed =>
        M.mechanism child
          (fun predecessor incident =>
            if h : predecessor = parent then h ▸ default else parents predecessor incident)
          seed)
      parents seed

end FiniteHiddenDAGSCM

end Causality
end Thesis
