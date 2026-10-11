import Thesis.Causality.HiddenPathSearch

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenPathSearch

/-!
# A hidden common cause with a nontrivial hidden relay

The full DAG has four vertices, ordered as `U, X, V, Y`, with arrows
`U -> X`, `U -> V`, and `V -> Y`.  Its observed vertices are `X,Y`; the
two hidden vertices are `U,V`.  There is no observed directed arrow, but the
actual hidden common ancestor `U` induces `X <-> Y` after projection.

The search must retain the two-edge hidden relay to `Y`, not merely test
direct adjacency.  Reverse and reflexive searches must fail.  Concrete
Boolean checks use the Lean kernel, while the general path-to-data adapter
is instantiated with the original propositional projection witness.
-/

/-- Two Boolean observed domains, with no allowed observed directed edge. -/
def signature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := by intro _; simp
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

/-- Observed positions are exactly `1,3`; hidden positions are `0,2`.
Every declared edge increases its natural vertex rank. -/
def fullGraph : FiniteHiddenDAG signature where
  count := 4
  observedNode := fun index => ⟨2 * index.val + 1, by have := index.isLt; omega⟩
  observedNode_injective := by
    intro left right equal
    apply Fin.ext
    have values := congrArg Fin.val equal
    change 2 * left.val + 1 = 2 * right.val + 1 at values
    omega
  hidden := fun node => decide (node.val = 0 ∨ node.val = 2)
  observed_not_hidden := by decide +kernel
  node_classified := by decide +kernel
  edge := fun source target => decide
    ((source.val = 0 ∧ target.val = 1) ∨
      (source.val = 0 ∧ target.val = 2) ∨
      (source.val = 2 ∧ target.val = 3))
  rank := Fin.val
  edge_rank_lt := by decide +kernel

def u : Fin fullGraph.count := ⟨0, by decide⟩
def v : Fin fullGraph.count := ⟨2, by decide⟩
def x : Fin signature.count := ⟨0, by decide⟩
def y : Fin signature.count := ⟨1, by decide⟩

/-- The propositional path includes an actual hidden interior vertex. -/
theorem relay_path : fullGraph.HiddenInternalPath u (fullGraph.observedNode y) :=
  .tail (j := v) (.direct (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

/-- Read computed relay data without choosing from the propositional path. -/
def relay_data : fullGraph.HiddenInternalPathData u (fullGraph.observedNode y) :=
  relay_path.toData

theorem relay_found :
    (fullGraph.hiddenInternalPath? u (fullGraph.observedNode y)).isSome = true := by
  decide +kernel

/-- The observed sink cannot become a hidden common cause by reversing arrows. -/
theorem reverse_missing :
    (fullGraph.hiddenInternalPath? (fullGraph.observedNode y) u).isNone = true := by
  decide +kernel

/-- Projection paths are nonempty and nonreflexive, unlike ordinary
reflexive reachability.  A zero-length route would be a spurious incidence. -/
theorem reflexive_missing : (fullGraph.hiddenInternalPath? u u).isNone = true := by
  decide +kernel

theorem common_cause_edge : fullGraph.projectedBidirected? x y = true := by
  decide +kernel

theorem no_reflexive_bidirected : fullGraph.projectedBidirected? x x = false := by
  decide +kernel

/-- Exhaust the two observed endpoints, without making any choice about
the graph's hidden path witnesses.  Both observed vertices are sinks. -/
private theorem observed_paths_missing : forall first second : Fin signature.count,
    (fullGraph.hiddenInternalPath? (fullGraph.observedNode first)
      (fullGraph.observedNode second)).isSome = false := by
  decide +kernel

/-- The original observed directed relation exactly matches the full DAG's
hidden-internal directed projection.  The search proves absence as well as
presence; no externally assumed projection match is used in this fixture. -/
theorem directed_matches : fullGraph.DirectedProjectionMatches := by
  intro first second
  rw [← fullGraph.hiddenInternalPath?_iff]
  change false = true <-> _
  rw [observed_paths_missing first second]

/-- Assemble the projection using the internally computed bidirected field. -/
def projection : FiniteLatentProjection signature :=
  fullGraph.computedLatentProjection directed_matches

theorem projection_has_common_cause : projection.observedGraph.bidirected x y = true :=
  common_cause_edge

end HiddenPathSearch
end Examples
end Causality
end Thesis
