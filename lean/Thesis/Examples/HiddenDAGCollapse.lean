import Thesis.CausalTransport.HiddenDAGCollapse
import Thesis.CausalTransport.HiddenDAGFullFamily

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGCollapse

open Probability

/-!
# A collapsed hidden relay with an intervened observed parent

The full graph has vertices `U, X, V, Y, Z` in that order.  `U,V` are hidden;
the arrows are `U -> X`, `U -> V`, `X -> V`, `V -> Y`, and `U -> Z`.
The projection has `X -> Y` and a shared hidden input feeding all of `X,Y,Z`.
It therefore tests a genuinely noncanonical three-child collapse, not merely
a graph already representable by private or pairwise roots.

Use an unbiased `U` bit, `X = U`, `V = U xor X`, `Y = V`, and `Z = U`.
Factually `Y` is always false.  Setting `X = false` instead makes `Y = U`.
The collapsed mechanism must read the intervened observed parent `X`; if it
silently re-evaluated `X` from its factual equation, this test would fail.

Every private noise coordinate is retained, including the unused ones.  The
finite numerical checks use kernel reduction; the arbitrary-intervention
record equality is also obtained by the general collapse theorem.  No
positivity or external transfer premise is supplied.
-/

/-- Three Boolean observed domains in the topological order `X,Y,Z`. -/
def signature : ObservedSignature where
  count := 3
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by decide +kernel

def x : Fin signature.count := ⟨0, by decide⟩
def y : Fin signature.count := ⟨1, by decide⟩
def z : Fin signature.count := ⟨2, by decide⟩

/-- The original five-node graph, with explicit finite classification and
rank proofs.  Observed `X,Y,Z` occupy full-graph positions `1,3,4`. -/
def fullGraph : FiniteHiddenDAG signature where
  count := 5
  observedNode := fun index =>
    if index.val = 0 then ⟨1, by decide⟩
    else if index.val = 1 then ⟨3, by decide⟩
    else ⟨4, by decide⟩
  observedNode_injective := by unfold Function.Injective; decide +kernel
  hidden := fun node => decide (node.val = 0 ∨ node.val = 2)
  observed_not_hidden := by decide +kernel
  node_classified := by decide +kernel
  edge := fun source target => decide
    ((source.val = 0 ∧ target.val = 1) ∨
      (source.val = 0 ∧ target.val = 2) ∨
      (source.val = 1 ∧ target.val = 2) ∨
      (source.val = 2 ∧ target.val = 3) ∨
      (source.val = 0 ∧ target.val = 4))
  rank := Fin.val
  edge_rank_lt := by decide +kernel

def u : Fin fullGraph.count := ⟨0, by decide⟩
def fullX : Fin fullGraph.count := ⟨1, by decide⟩
def v : Fin fullGraph.count := ⟨2, by decide⟩

/-- Check all observed endpoint pairs with the finite path search, including
the observed-to-observed hidden relay `X -> V -> Y`. -/
private theorem directed_search_matches : forall first second : Fin signature.count,
    signature.directed first second =
      (fullGraph.hiddenInternalPath? (fullGraph.observedNode first)
        (fullGraph.observedNode second)).isSome := by
  decide +kernel

theorem directed_matches : fullGraph.DirectedProjectionMatches := by
  intro first second
  change signature.directed first second = true <->
    fullGraph.HiddenInternalPath (fullGraph.observedNode first)
      (fullGraph.observedNode second)
  rw [directed_search_matches first second]
  exact fullGraph.hiddenInternalPath?_iff _ _

/-- The bidirected part is computed and verified, not provided as a graph
agreement assumption by a fixture caller. -/
def projection : FiniteLatentProjection signature :=
  fullGraph.computedLatentProjection directed_matches

def unbiased : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- A concrete full-DAG SCM.  All private noises are independent unbiased
bits; only `U` uses its own bit, and the other mechanisms use declared parents.
Keeping the unused bits also tests that collapse retains the original prior. -/
def model : FiniteHiddenDAGSCM signature projection where
  NodeValue := fun _ => Bool
  nodeEnumeration := fun _ => [false, true]
  node_complete := by intro _ value; cases value <;> simp
  nodeDecidableEq := fun _ => inferInstance
  observedEquiv := fun _ => ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  observedIndex := fullGraph.observedIndex
  observedIndex_observed := fullGraph.observedIndex_observed
  observedIndex_sound := fullGraph.observedIndex_sound
  hidden_has_no_observed_index := fullGraph.observedIndex_hidden
  Noise := fun _ => Bool
  noiseEnumeration := fun _ => [false, true]
  noise_complete := by intro _ value; cases value <;> simp
  noiseDecidableEq := fun _ => inferInstance
  factor := fun _ => unbiased
  prior := FiniteProduct.record 5 (fun _ => Bool) (fun _ => unbiased)
  product_law := FiniteProduct.record_rectangular_probVal 5
    (fun _ => Bool) (fun _ => unbiased)
  mechanism := fun node parents seed =>
    if atU : node.val = 0 then seed
    else if atX : node.val = 1 then
      parents u (by simp [projection, FiniteHiddenDAG.computedLatentProjection,
        fullGraph, u, atX])
    else if atV : node.val = 2 then
      Bool.xor (parents u (by simp [projection, FiniteHiddenDAG.computedLatentProjection,
        fullGraph, u, atV]))
        (parents fullX (by simp [projection, FiniteHiddenDAG.computedLatentProjection,
          fullGraph, fullX, atV]))
    else if atY : node.val = 3 then
      parents v (by simp [projection, FiniteHiddenDAG.computedLatentProjection,
        fullGraph, v, atY])
    else parents u (by
      have bounded : node.val < 5 := node.isLt
      have atZ : node.val = 4 := by omega
      simp [projection, FiniteHiddenDAG.computedLatentProjection, fullGraph, u, atZ])

def allTrueNoise : model.NoiseAssignment := fun _ => true

def forceXFalse : HardIntervention signature :=
  (HardIntervention.empty signature).set x false

/-- Factually the shared `U` and its observed copy `X` cancel at the relay. -/
theorem factual_y_false :
    model.evalObserved (HardIntervention.empty signature) allTrueNoise y = false := by
  decide +kernel

/-- Under the hard intervention the old full model keeps `X = false`, so
the nonzero `U` bit passes through the relay to `Y`. -/
theorem forced_full_y_true :
    model.evalObserved forceXFalse allTrueNoise y = true := by
  decide +kernel

/-- The new mechanism reads the forced observed parent rather than its old
factual equation.  This is a separate kernel-level execution check. -/
theorem forced_collapsed_y_true :
    model.toLatentRootSCM.evalUnder forceXFalse.value allTrueNoise y = true := by
  decide +kernel

/-- The same original private-noise input reaches three distinct observed
children, including `Y` through a nontrivial hidden relay. -/
theorem shared_root_three_children :
    model.toLatentRootSCM.latent.incident u x = true ∧
      model.toLatentRootSCM.latent.incident u y = true ∧
      model.toLatentRootSCM.latent.incident u z = true := by
  decide +kernel

/-- A law-preserving collapse cannot be advertised as canonical here.
Its actual shared root has three children; no pairwise-independent replacement
has been silently substituted for that common noise coordinate. -/
theorem collapsed_not_canonical : ¬ model.toLatentRootSCM.IsCanonicalSemiMarkovian := by
  intro canonical
  rcases canonical u x y z shared_root_three_children.1
      shared_root_three_children.2.1 shared_root_three_children.2.2 with
      same | same | same
  · exact (by decide : x ≠ y) same
  · exact (by decide : x ≠ z) same
  · exact (by decide : y ≠ z) same

/-- The fixture contains actual observational zeros, so its record-preserving
conversion is not only being tested on positive distributions. -/
theorem observational_y_true_zero :
    (model.observationalValue (fun assignment => assignment y)).num = 0 := by
  decide +kernel

/-- The corresponding interventional event has probability one half.
The test compares rational values, rather than requiring a normalized record. -/
theorem interventional_y_true_half :
    QProb.Equiv (model.interventionalValue forceXFalse (fun assignment => assignment y))
      ⟨1, 2, by decide⟩ := by
  decide +kernel

/-- Instantiate full record preservation at every intervention, not only the
single numerical regression above.  No external interface is consumed. -/
theorem every_intervention_preserved (intervention : HardIntervention signature) :
    model.toLatentRootSCM.interventionalDist intervention.value =
      model.interventionalDist intervention :=
  model.toLatentRootSCM_interventionalDist intervention

/-- The new model's graph is also exactly the computed projection. -/
theorem projected_graph_preserved (first second : Fin signature.count) :
    model.toLatentRootSCM.observedGraph.bidirected first second =
      projection.observedGraph.bidirected first second :=
  model.toLatentRootSCM_projectedGraph first second

end HiddenDAGCollapse
end Examples
end Causality
end Thesis
