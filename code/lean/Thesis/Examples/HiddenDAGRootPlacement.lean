import Thesis.CausalTransport.HiddenDAGRootPlacement
import Thesis.CausalTransport.HiddenDAGPlacedNoise
import Thesis.Examples.HiddenDAGCollapse

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGRootPlacement

open Probability HiddenDAGCollapse

/-!
# Allocate all input kinds on an original three-child hidden cause

The original five-node graph has a hidden `U` reaching `X,Y,Z`; its route to
`Y` goes through the hidden relay `V`.  This fixture uses a canonical latent
extension with five distinct roots: one unused, one private to `X`, and one
for each of `X-Y`, `X-Z`, `Y-Z`.  All three pair roots are placed at that same
original `U`, while their root indices remain distinct.  This is the geometry
needed to group independent channels there, not a claim that those channels
can be identified as one common bit.

The first fixture uses `Unit` root values because it tests graph data only.
Shared deliveries retain actual hidden-internal path data; private and unused
inputs exercise the two other placement branches.  The second fixture gives
all roots independent fair bits and checks the actual grouped noise prior.
The probability that two channels at `U` are both true is one quarter, not
the one half produced by merging them as one common bit.  No countermodel
or distribution-preservation interface is supplied by these noise tests.
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

/-! ## Distinct independent bit channels sharing one allocated node -/

/-- Keep the same five input incidences, with actual Boolean root alphabets. -/
def booleanLatent : LatentExtension signature where
  count := 5
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  valueDecidableEq := fun _ => inferInstance
  incident := latent.incident

/-- A concrete canonical source model with an actual independent root prior.
Its constant observed equations are allowed and contain observational zeros;
no observed positivity premise is needed to construct the placed noise law. -/
def noiseModel : ExactModel signature where
  latent := booleanLatent
  factor := fun _ => unbiased
  prior := FiniteProduct.record 5 (fun _ => Bool) (fun _ => unbiased)
  product_law := FiniteProduct.record_rectangular_probVal 5 (fun _ => Bool) (fun _ => unbiased)
  mechanism := fun _child _parents _inputs => false

theorem noiseModel_compatible : Compatible noiseModel projection.observedGraph :=
  ⟨canonical, graph_matches⟩

/-- A nontrivial joint-noise check: the two channels share their original
hidden source, but retain separate independent random coordinates there. -/
theorem two_channels_at_u_are_independent :
    QProb.Equiv ((HiddenDAGPlacedNoise.prior noiseModel noiseModel_compatible).probVal
      (fun noise => decide (noise u xyRoot = some true) && decide (noise u xzRoot = some true)))
      ⟨1, 4, by decide⟩ := by
  decide +kernel

/-- Relay nodes receive no new random copy of a root channel.  Its absent
local slot is filled later by the hidden-node relay mechanism, not by noise. -/
theorem relay_has_no_random_copy :
    QProb.Equiv ((HiddenDAGPlacedNoise.prior noiseModel noiseModel_compatible).probVal
      (fun noise => (noise v xyRoot).isNone)) QProb.one := by
  decide +kernel

/-- Every encoded channel retains the original root value at its actual
allocated source, independent of the other root assignments. -/
theorem encoded_xy_channel (roots : noiseModel.latent.Assignment) :
    HiddenDAGPlacedNoise.encode noiseModel noiseModel_compatible roots u xyRoot = some (roots xyRoot) :=
  HiddenDAGPlacedNoise.encode_of_placed noiseModel noiseModel_compatible roots u xyRoot (by decide +kernel)

end HiddenDAGRootPlacement
end Examples
end Causality
end Thesis
