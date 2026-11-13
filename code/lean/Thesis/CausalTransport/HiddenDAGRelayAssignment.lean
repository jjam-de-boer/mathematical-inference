import Thesis.CausalTransport.HiddenDAGRealization

namespace Thesis
namespace Causality

/-!
# The explicit assignment carried by original-DAG relays

Fix arbitrary observed signals and original root values.  An observed node
contains its own supplied signal.  A hidden node contains every observed
signal that reaches it through a hidden-internal path, and every root channel
that is installed there or reaches it from its allocated hidden source.
All other coordinates use the constructor's total off-route defaults.

This assignment is explicit finite data.  The path lemmas below prove that
every required incoming route reads the actual supplied coordinate, regardless
of which successful path the finite search returns.  No probability law,
positivity premise or assumed model-equivalence interface is used here.

Later the observed signals will be the original model's evaluation under a
hard intervention.  Proving the local equations for this assignment, then
using acyclic equation uniqueness, gives the general unitwise preservation
theorem.  Merely defining this assignment is not that theorem.
-/

namespace HiddenDAGRelay

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- A hidden relay stores exactly the reachable observed signals.  The
reachability test is the already proved complete finite path search, not
an existential choice of a route or an observed ancestor's equation. -/
def expectedSignals (projection : FiniteLatentProjection S) (signals : S.Assignment)
    (node : Fin projection.hiddenDAG.count) : S.Assignment :=
  fun index => if
      (projection.hiddenDAG.hiddenInternalPath? (projection.hiddenDAG.observedNode index) node).isSome
    then signals index else S.defaultValue index

/-- A channel's actual allocated source contains its supplied root value.
Hidden descendants on a valid relay route carry that same coordinate.  A
private observed source is deliberately not exposed to downstream relays. -/
def expectedRoots (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (roots : model.latent.Assignment) (node : Fin P.hiddenDAG.count) : model.latent.Assignment :=
  fun root =>
    match (model.hiddenDAGRootPlacements compatible root).source? with
    | none => defaultRoots model root
    | some source =>
        if source = node then roots root
        else if P.hiddenDAG.hidden source then
          if (P.hiddenDAG.hiddenInternalPath? source node).isSome then roots root
          else defaultRoots model root
        else defaultRoots model root

/-- Pack the supplied observed scalar or the hidden relay payload into the
node's exact declared alphabet.  Observed domains remain unchanged; hidden
nodes use the complete finite pair presentation from the constructor. -/
def expectedValue (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (signals : S.Assignment) (roots : model.latent.Assignment)
    (node : Fin P.hiddenDAG.count) : NodeValue model P node :=
  match found : P.hiddenDAG.observedIndex node with
  | none => (nodeValue_of_none model node found).mpr
      ⟨expectedSignals P signals node, expectedRoots model compatible roots node⟩
  | some index => (P.hiddenDAG.observedIndex_sound node index found) ▸
      (observedEquivalence model P index).backward (signals index)

/-- Read the exact payload branch at a node whose finite lookup is absent.
This statement does not require choosing an observed index or a root value. -/
theorem expectedValue_hidden (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (signals : S.Assignment) (roots : model.latent.Assignment) (node : Fin P.hiddenDAG.count)
    (missing : P.hiddenDAG.observedIndex node = none) :
    expectedValue model compatible signals roots node =
      (nodeValue_of_none model node missing).mpr
        ⟨expectedSignals P signals node, expectedRoots model compatible roots node⟩ := by
  unfold expectedValue
  split
  · rfl
  · rename_i index found
    rw [missing] at found
    cases found

/-- At an embedded observed node the packed value is its own supplied
signal, not a hidden payload and not a fresh evaluation of its equation. -/
theorem expectedValue_observed (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (signals : S.Assignment) (roots : model.latent.Assignment) (index : Fin S.count) :
    expectedValue model compatible signals roots (P.hiddenDAG.observedNode index) =
      (observedEquivalence model P index).backward (signals index) := by
  unfold expectedValue
  split
  · rename_i missing
    have found := P.hiddenDAG.observedIndex_observed index
    rw [missing] at found
    cases found
  · rename_i ownIndex found
    have same : ownIndex = index := Option.some.inj
      (found.symm.trans (P.hiddenDAG.observedIndex_observed index))
    subst ownIndex
    rfl

/-- Every actual observed-signal path is recognized by the finite search.
The stored coordinate therefore cannot fall back to an off-route default. -/
theorem expectedSignals_of_path (signals : S.Assignment) (index : Fin S.count)
    (node : Fin P.hiddenDAG.count)
    (path : P.hiddenDAG.HiddenInternalPathData (P.hiddenDAG.observedNode index) node) :
    expectedSignals P signals node index = signals index := by
  unfold expectedSignals
  rw [P.hiddenDAG.hiddenInternalPath?_complete path.toSpecification]
  rfl

/-- The allocated owner stores the root value even if there is no nonempty
path from that owner to itself.  Sampling is the local source case, not a
reflexive path added to the graph's reachability convention. -/
theorem expectedRoots_at_source (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (roots : model.latent.Assignment) (root : Fin model.latent.count)
    (source : Fin P.hiddenDAG.count)
    (placed : (model.hiddenDAGRootPlacements compatible root).source? = some source) :
    expectedRoots model compatible roots source root = roots root := by
  unfold expectedRoots
  rw [placed]
  dsimp only []
  rw [if_pos rfl]

/-- A hidden source's root coordinate reaches every actual hidden-internal
descendant.  The finite search need not choose this supplied path: completeness
ensures its chosen path has the same reachable-coordinate tag. -/
theorem expectedRoots_of_path (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (roots : model.latent.Assignment) (root : Fin model.latent.count)
    (source node : Fin P.hiddenDAG.count)
    (placed : (model.hiddenDAGRootPlacements compatible root).source? = some source)
    (hidden : P.hiddenDAG.hidden source = true)
    (path : P.hiddenDAG.HiddenInternalPathData source node) :
    expectedRoots model compatible roots node root = roots root := by
  unfold expectedRoots
  rw [placed]
  dsimp only []
  by_cases localSource : source = node
  · rw [if_pos localSource]
  · rw [if_neg localSource, if_pos hidden,
      P.hiddenDAG.hiddenInternalPath?_complete path.toSpecification]
    rfl

/-! ## Every required route reads its original coordinate -/

/-- A projected-parent route reads the supplied observed signal at its
last actual predecessor.  Direct paths read the source scalar; longer paths
read a hidden predecessor whose stored prefix is proved reachable. -/
theorem signalAlong_expectedValue (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (signals : S.Assignment)
    (roots : model.latent.Assignment) (index : Fin S.count) (node : Fin P.hiddenDAG.count)
    (path : P.hiddenDAG.HiddenInternalPathData (P.hiddenDAG.observedNode index) node) :
    signalAlong model P node (fun parent _edge => expectedValue model compatible signals roots parent)
      index path = signals index := by
  cases path with
  | direct edge =>
      change readSignal model P (P.hiddenDAG.observedNode index)
        (expectedValue model compatible signals roots (P.hiddenDAG.observedNode index)) index = _
      rw [expectedValue_observed]
      exact readSignal_observed model index (signals index)
  | @tail middle _target earlierRoute hidden edge =>
      change readSignal model P middle (expectedValue model compatible signals roots middle) index = _
      rw [expectedValue_hidden model compatible signals roots middle
        (P.hiddenDAG.observedIndex_hidden middle hidden),
        readSignal_hidden model middle (P.hiddenDAG.observedIndex_hidden middle hidden)]
      exact expectedSignals_of_path signals index middle earlierRoute

/-- A shared-root route reads the supplied root channel at its last actual
predecessor.  The hidden-source premise is essential: an observed node's
private noise is never exposed by its scalar value. -/
theorem rootAlong_expectedValue (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (signals : S.Assignment)
    (roots : model.latent.Assignment) (root : Fin model.latent.count)
    (source node : Fin P.hiddenDAG.count)
    (placed : (model.hiddenDAGRootPlacements compatible root).source? = some source)
    (hidden : P.hiddenDAG.hidden source = true)
    (path : P.hiddenDAG.HiddenInternalPathData source node) :
    rootAlong model P node (fun parent _edge => expectedValue model compatible signals roots parent)
      root path = roots root := by
  cases path with
  | direct edge =>
      change readRoot model P source (expectedValue model compatible signals roots source) root = _
      rw [expectedValue_hidden model compatible signals roots source
        (P.hiddenDAG.observedIndex_hidden source hidden),
        readRoot_hidden model source (P.hiddenDAG.observedIndex_hidden source hidden)]
      exact expectedRoots_at_source model compatible roots root source placed
  | @tail middle _target earlierRoute lastHidden edge =>
      change readRoot model P middle (expectedValue model compatible signals roots middle) root = _
      rw [expectedValue_hidden model compatible signals roots middle
        (P.hiddenDAG.observedIndex_hidden middle lastHidden),
        readRoot_hidden model middle (P.hiddenDAG.observedIndex_hidden middle lastHidden)]
      exact expectedRoots_of_path model compatible roots root source middle placed hidden earlierRoute

end HiddenDAGRelay
end Causality
end Thesis
