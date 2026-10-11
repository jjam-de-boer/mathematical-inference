import Thesis.CausalTransport.HiddenDAGRootPlacement
import Thesis.Examples.HiddenDAGCollapse

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGRootPlacement

open HiddenDAGCollapse

/-!
# Allocate all input kinds on an original three-child hidden cause

The original five-node graph has a hidden `U` reaching `X,Y,Z`; its route to
`Y` goes through the hidden relay `V`.  This fixture uses a canonical latent
extension with five distinct roots: one unused, one private to `X`, and one
for each of `X-Y`, `X-Z`, `Y-Z`.  All three pair roots are placed at that same
original `U`, while their root indices remain distinct.  This is the geometry
needed to group independent channels there, not a claim that those channels
can be identified as one common bit.

The root value type is `Unit` here because these are graph-data tests.  No
noise law, countermodel, distribution-preservation interface or axiom is
silently supplied.  Shared deliveries retain actual hidden-internal path
data; private and unused inputs exercise the two other placement branches.
-/

/-- Retain unused and private inputs as well as every projected pair root.
The complete Boolean graph is computed from these actual incidences. -/
def latent : LatentExtension signature where
  count := 5
  Value := fun _ => Unit
  valueEnumeration := fun _ => [()]
  value_complete := by intro _ value; cases value; simp
  valueDecidableEq := fun _ => inferInstance
  incident := fun root child =>
    if root.val = 0 then false
    else if root.val = 1 then decide (child = x)
    else if root.val = 2 then decide (child = x ∨ child = y)
    else if root.val = 3 then decide (child = x ∨ child = z)
    else decide (child = y ∨ child = z)

theorem canonical : latent.CanonicalSemiMarkovian := by
  unfold LatentExtension.CanonicalSemiMarkovian
  decide +kernel

theorem graph_matches : forall left right : Fin signature.count,
    latent.projectedBidirected left right = projection.observedGraph.bidirected left right := by
  decide +kernel

/-- Apply the general construction once to every root, with no root-specific
placement witness supplied to it. -/
def placements (root : Fin latent.count) :
    Causality.HiddenDAGRootPlacement latent projection root :=
  latent.hiddenDAGRootPlacement canonical graph_matches root

def unusedRoot : Fin latent.count := ⟨0, by decide⟩
def privateRoot : Fin latent.count := ⟨1, by decide⟩
def xyRoot : Fin latent.count := ⟨2, by decide⟩
def xzRoot : Fin latent.count := ⟨3, by decide⟩
def yzRoot : Fin latent.count := ⟨4, by decide⟩

theorem unused_has_no_source : (placements unusedRoot).source? = none := by
  decide +kernel

theorem private_is_local :
    (placements privateRoot).source? = some (fullGraph.observedNode x) := by
  decide +kernel

/-- Several independent canonical root channels can be installed at one
real hidden node; none of their original root labels is collapsed away. -/
theorem pair_sources_are_u :
    (placements xyRoot).source? = some u ∧
      (placements xzRoot).source? = some u ∧
        (placements yzRoot).source? = some u := by
  decide +kernel

theorem pair_root_indices_distinct : xyRoot ≠ xzRoot ∧ xyRoot ≠ yzRoot ∧ xzRoot ≠ yzRoot := by
  decide

/-- Both recipients read delivery data from the same allocated source.
The `Y` delivery cannot use a fictitious direct `U -> Y` edge. -/
def xy_to_y : HiddenDAGRootDelivery (placements xyRoot) y :=
  (placements xyRoot).delivery y (by decide +kernel)

theorem xy_to_y_source : xy_to_y.source = u := by
  decide +kernel

theorem u_y_has_no_direct_edge : fullGraph.edge u (fullGraph.observedNode y) = false := by
  decide +kernel

/-- The projected parent edge also obtains its actual relay data internally.
The original `X -> V -> Y` route must retain the hidden interior vertex. -/
def observed_parent_relay : fullGraph.HiddenInternalPathData
    (fullGraph.observedNode x) (fullGraph.observedNode y) :=
  projection.directedPathData x y (by decide +kernel)

theorem x_y_has_no_direct_edge :
    fullGraph.edge (fullGraph.observedNode x) (fullGraph.observedNode y) = false := by
  decide +kernel

/-- Common-cause search keeps the projection's irreflexivity convention. -/
theorem reflexive_cause_absent : (fullGraph.hiddenCommonCause? x x).isNone = true := by
  decide +kernel

end HiddenDAGRootPlacement
end Examples
end Causality
end Thesis
