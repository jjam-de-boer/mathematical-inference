import Thesis.CausalTransport.Hedge.Models
import Thesis.Causality.InterventionalCounterexample

namespace Thesis
namespace Causality

open Probability

/-!
# C-forest incidence, support and nested parity

These shared forest-flow, exact-support and incidence-compatibility arguments
are independent of any identification recursion. Pair-root realizers and their
finite fibers retain the actual latent enumeration; no existential choice is
used to obtain representatives. The selected node sets, observed alphabets,
and the hypotheses of every local model theorem remain unchanged.

The one-anchor correction is a Boolean parity fact, not a positive-model
construction. It is shared by partial-channel incidence and the older carrier
models without requiring either client to import the other's development.

This layer contains no legacy failure-stack proof and does not itself assemble
published completeness. Its old `CompletenessHedgeParity` path reexports all
original declarations and retains historical import compatibility. The final
unrestricted channel counterexample and theorem packages remain in their
dedicated current-engine modules.
-/

/-- Correct a Boolean incidence target at one anchor by its total selected
parity. -/
def hedgeDefectAdjustedTarget (nodes : NodeSet S) (anchor : Fin S.count)
    (target : Fin S.count → Bool) (node : Fin S.count) : Bool :=
  Bool.xor (target node)
    (if node = anchor then hedgeNodeXor nodes target else false)

/-- XOR of a one-anchor vector is its selected bit. -/
theorem hedgeNodeXor_singleAnchor (nodes : NodeSet S)
    (anchor : Fin S.count) (inside : nodes anchor = true) (bit : Bool) :
    hedgeNodeXor nodes (fun node => if node = anchor then bit else false) =
      bit := by
  unfold hedgeNodeXor
  cases bit with
  | false =>
      exact foldl_unchanged _ false (NodeSet.members nodes)
        (fun total node => by simp)
  | true =>
      have member := (NodeSet.mem_members_iff nodes anchor).mpr inside
      simpa using foldl_xor_indicator_of_mem_nodup
        (NodeSet.members nodes) anchor member (NodeSet.nodup_members nodes)

/-- The anchor correction has even support, stated in the exact list-parity
form consumed by `BidirectedComponent.evenTargetPairBits`. -/
theorem hedgeDefectAdjustedTarget_even (nodes : NodeSet S)
    (anchor : Fin S.count) (inside : nodes anchor = true)
    (target : Fin S.count → Bool) :
    (hedgeTrueVertices nodes
      (hedgeDefectAdjustedTarget nodes anchor target)).length % 2 = 0 := by
  apply (foldl_xor_eq_false_iff_filter_even
    (hedgeDefectAdjustedTarget nodes anchor target)
    (NodeSet.members nodes)).mp
  unfold hedgeDefectAdjustedTarget
  rw [foldl_xor_pointwise]
  change Bool.xor (hedgeNodeXor nodes target)
      (hedgeNodeXor nodes (fun node =>
        if node = anchor then hedgeNodeXor nodes target else false)) = false
  rw [hedgeNodeXor_singleAnchor nodes anchor inside (hedgeNodeXor nodes target)]
  generalize hedgeNodeXor nodes target = parity
  cases parity <;> rfl

/-!
### C-forest incidence flow all the way to query outcomes

The abstract root-flow wrapper in `Hedge.Models` requires a caller to reconstruct
the root bits.  The models below instead put the pair-root incidence directly
at every selected c-forest vertex and use the route-priority combined
successor.  Forest incidence therefore flows toward common roots and, once it
touches a canonical readout route, continues to a query outcome without
splitting or returning through an intervened vertex.

On the small side every selected vertex is free under the query intervention.
Flow conservation and the finite handshaking identity immediately force even
parity at the outcome sinks.  The corresponding odd large-side construction
is developed separately because its selected action vertices deliberately
break their local structural equations.
-/

/-- Local source bit supplied by pair-roots internal to `nodes`; vertices
outside the forest inject zero into the routing flow. -/
def hedgeForestIncidenceSource (G : ObservedGraph S)
    (nodes : NodeSet S) (child : Fin S.count)
    (_parents : S.ParentValues child)
    (inputs : (hedgeLatentExtension G).Inputs child) : Bool :=
  if nodes child then hedgeXorPairBitsWithin G nodes child inputs else false

/-- Large c-forest incidence followed through the combined action-free
outcome routing map. -/
def HedgeWitness.largeOutcomeFlowModel
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ExactModel S :=
  hedgeFlowReadoutModel rich w.largeOutcomeFlowNodes
    w.largeOutcomeFlowSuccessor (w.largeParityModel rich)
    (hedgeForestIncidenceSource G w.large)

/-- Small c-forest incidence followed through the corresponding combined
outcome routing map. -/
def HedgeWitness.smallOutcomeFlowModel
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ExactModel S :=
  hedgeFlowReadoutModel rich w.smallOutcomeFlowNodes
    w.smallOutcomeFlowSuccessor (w.smallParityModel rich)
    (hedgeForestIncidenceSource G w.small)

/-- The combined large flow changes mechanisms but retains the canonical
latent extension and projected graph. -/
theorem HedgeWitness.largeOutcomeFlowModel_compatible
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Compatible (w.largeOutcomeFlowModel rich) G :=
  hedgeFlowReadoutModel_compatible rich w.largeOutcomeFlowNodes
    w.largeOutcomeFlowSuccessor (w.largeParityModel rich)
    (hedgeForestIncidenceSource G w.large)
    (w.largeParityModel_compatible rich)

/-- The combined small flow has the same compatibility guarantee. -/
theorem HedgeWitness.smallOutcomeFlowModel_compatible
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Compatible (w.smallOutcomeFlowModel rich) G :=
  hedgeFlowReadoutModel_compatible rich w.smallOutcomeFlowNodes
    w.smallOutcomeFlowSuccessor (w.smallParityModel rich)
    (hedgeForestIncidenceSource G w.small)
    (w.smallParityModel_compatible rich)

/-- In an observational run of the combined large model, the assignment
itself determines the local pair-root source at every selected flow vertex.

This is the inverse form of the structural equation.  It is more useful for
support counting than the forward equation: a proposed observed target fixes
the left-hand side through `hedgeRoutingLocalSource`, while the right-hand
side is exactly the incidence constraint imposed on the latent pair bits. -/
theorem HedgeWitness.largeOutcomeFlowModel_observational_localSource
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment)
    (child : Fin S.count) (selected : w.largeOutcomeFlowNodes child = true) :
    let bits := fun node => hedgeIsSecond rich node
      ((w.largeOutcomeFlowModel rich).eval u node)
    hedgeRoutingLocalSource w.largeOutcomeFlowSuccessor bits child =
      if w.large child then
        hedgeXorPairBitsWithin G w.large child (fun latent _ => u latent)
      else false := by
  have recovered := hedgeFlowReadoutModel_localSource_of_free rich
    w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
    w.largeOutcomeFlowSuccessor_wellFormed (w.largeParityModel rich)
    (hedgeForestIncidenceSource G w.large)
    (FiniteLatentSCM.noIntervention S) u child selected rfl
  simpa [HedgeWitness.largeOutcomeFlowModel,
    hedgeForestIncidenceSource, FiniteLatentSCM.eval] using recovered

/-- The small combined flow has the same observational inversion principle,
with incidence restricted to the inner c-forest.  Route-only vertices inject
zero; recording that fact explicitly will become the route-consistency part
of the two models' common observational support. -/
theorem HedgeWitness.smallOutcomeFlowModel_observational_localSource
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment)
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true) :
    let bits := fun node => hedgeIsSecond rich node
      ((w.smallOutcomeFlowModel rich).eval u node)
    hedgeRoutingLocalSource w.smallOutcomeFlowSuccessor bits child =
      if w.small child then
        hedgeXorPairBitsWithin G w.small child (fun latent _ => u latent)
      else false := by
  have recovered := hedgeFlowReadoutModel_localSource_of_free rich
    w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed (w.smallParityModel rich)
    (hedgeForestIncidenceSource G w.small)
    (FiniteLatentSCM.noIntervention S) u child selected rfl
  simpa [HedgeWitness.smallOutcomeFlowModel,
    hedgeForestIncidenceSource, FiniteLatentSCM.eval] using recovered

/-- At a free vertex of the combined large flow, cancelling its incoming
routed bits recovers exactly the pair-root incidence injected by the large
c-forest.  This packages the structural equation in the effective-source
form needed to compare an ordinary run with the endpoint-toggle run. -/
theorem HedgeWitness.largeOutcomeFlowModel_localSource_of_free
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment)
    (child : Fin S.count) (selected : w.largeOutcomeFlowNodes child = true)
    (free : hedgeDoSecond rich q.action child = none) :
    let bits := fun node => hedgeIsSecond rich node
      ((w.largeOutcomeFlowModel rich).evalNodeUnder
        (hedgeDoSecond rich q.action) u node)
    hedgeRoutingLocalSource w.largeOutcomeFlowSuccessor bits child =
      if w.large child then
        hedgeXorPairBitsWithin G w.large child (fun latent _ => u latent)
      else false := by
  have recovered := hedgeFlowReadoutModel_localSource_of_free rich
    w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
    w.largeOutcomeFlowSuccessor_wellFormed (w.largeParityModel rich)
    (hedgeForestIncidenceSource G w.large)
    (hedgeDoSecond rich q.action) u child selected free
  simpa [HedgeWitness.largeOutcomeFlowModel,
    hedgeForestIncidenceSource] using recovered

/-- Restricted incidence is the rootwise fold of single-root contributions. -/
theorem hedgeXorPairBitsWithinFrom_eq_contribution_fold
    (G : ObservedGraph S) (nodes : NodeSet S)
    (pairBits : Fin (pairRootCount G) → Bool) (node : Fin S.count) :
    hedgeXorPairBitsWithinFrom G nodes node pairBits =
      (List.finRange (pairRootCount G)).foldl
        (fun total root => Bool.xor total
          (hedgePairRootContributionWithin G nodes root
            (pairBits root) node)) false := by
  unfold hedgeXorPairBitsWithinFrom
  apply foldl_congr
  intro total root
  cases selected :
      ((hedgeLatentExtension G).incident (hedgePairRoot G root) node &&
        hedgePairRootWithin G nodes root) <;>
    simp [hedgePairRootContributionWithin, selected]

/--
The XOR of every coordinate of a restricted incidence vector is zero.
Transposing the node/root folds reduces the statement to the two-endpoint
parity of each individual pair-root.
-/
theorem hedgeNodeXor_incidence
    (G : ObservedGraph S) (nodes : NodeSet S)
    (pairBits : Fin (pairRootCount G) → Bool) :
    hedgeNodeXor nodes
        (fun node => hedgeXorPairBitsWithinFrom G nodes node pairBits) =
      false := by
  unfold hedgeNodeXor
  have expanded := foldl_congr
    (fun total node => Bool.xor total
      (hedgeXorPairBitsWithinFrom G nodes node pairBits))
    (fun total node => Bool.xor total
      ((List.finRange (pairRootCount G)).foldl
        (fun rootTotal root => Bool.xor rootTotal
          (hedgePairRootContributionWithin G nodes root
            (pairBits root) node)) false))
    false (NodeSet.members nodes)
    (fun total node => by
      change Bool.xor total _ = Bool.xor total _
      rw [hedgeXorPairBitsWithinFrom_eq_contribution_fold
        G nodes pairBits node])
  rw [expanded, foldl_xor_swap]
  exact foldl_unchanged _ false (List.finRange (pairRootCount G))
    (fun total root => by
      rw [hedgePairRootContributionWithin_parity G nodes root
        (pairBits root)]
      simp)

/-- Masking incidence to a forest inside a larger union does not change its
total XOR, which is even by the pair-root handshaking identity. -/
theorem hedgeNodeXor_incidenceSource_union
    (G : ObservedGraph S) (nodes extra : NodeSet S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeNodeXor (NodeSet.union extra nodes) (fun child =>
        if nodes child then
          hedgeXorPairBitsWithin G nodes child (fun latent _ => u latent)
        else false) = false := by
  rw [hedgeNodeXor_mask_of_subset nodes (NodeSet.union extra nodes)
    (NodeSet.subset_union_right extra nodes)
    (fun child => hedgeXorPairBitsWithin G nodes child
      (fun latent _ => u latent))]
  have converted :
      hedgeNodeXor nodes (fun child =>
          hedgeXorPairBitsWithin G nodes child (fun latent _ => u latent)) =
        hedgeNodeXor nodes (fun child =>
          hedgeXorPairBitsWithinFrom G nodes child (hedgePairBitsOf G u)) := by
    unfold hedgeNodeXor
    apply foldl_congr
    intro total child
    change Bool.xor total
        (hedgeXorPairBitsWithin G nodes child (fun latent _ => u latent)) =
      Bool.xor total
        (hedgeXorPairBitsWithinFrom G nodes child (hedgePairBitsOf G u))
    rw [hedgeXorPairBitsWithin_pairBitsOf]
  rw [converted]
  exact hedgeNodeXor_incidence G nodes (hedgePairBitsOf G u)

/-- Every observational output of the combined large model has even parity
on its canonical outcome sinks.  The readout forest can merge and reroute
streams, but it cannot change total parity: after conservation, the only
remaining sources are the two-ended pair-root incidences inside `large`. -/
theorem HedgeWitness.largeOutcomeFlowModel_sinkParity_observational
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeNodeXor
        (keptSinks w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor)
        (fun node => hedgeIsSecond rich node
          ((w.largeOutcomeFlowModel rich).eval u node)) = false := by
  unfold HedgeWitness.largeOutcomeFlowModel
  rw [hedgeFlowReadoutModel_sinkParity_observational rich
    w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
    w.largeOutcomeFlowSuccessor_wellFormed (w.largeParityModel rich)
    (hedgeForestIncidenceSource G w.large) u]
  simpa [HedgeWitness.largeOutcomeFlowNodes,
    hedgeForestIncidenceSource] using
      hedgeNodeXor_incidenceSource_union G w.large w.rootReadoutNodes u

/-- The combined small model satisfies the identical observational sink
parity invariant.  Here conservation exposes incidence internal to `small`;
the larger readout-node union contributes only zero local sources. -/
theorem HedgeWitness.smallOutcomeFlowModel_sinkParity_observational
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeNodeXor
        (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor)
        (fun node => hedgeIsSecond rich node
          ((w.smallOutcomeFlowModel rich).eval u node)) = false := by
  unfold HedgeWitness.smallOutcomeFlowModel
  rw [hedgeFlowReadoutModel_sinkParity_observational rich
    w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed (w.smallParityModel rich)
    (hedgeForestIncidenceSource G w.small) u]
  simpa [HedgeWitness.smallOutcomeFlowNodes,
    hedgeForestIncidenceSource] using
      hedgeNodeXor_incidenceSource_union G w.small w.rootReadoutNodes u

/-- Every latent assignment of the combined small model has even parity over
its query-outcome sinks under `do(X = second)`.  Both the small forest and the
readout routes avoid the action, so all local flow equations remain active;
their total source is an even internal incidence vector. -/
theorem HedgeWitness.smallOutcomeFlowModel_sinkParity_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeNodeXor
        (keptSinks w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor)
        (fun node => hedgeIsSecond rich node
          ((w.smallOutcomeFlowModel rich).evalNodeUnder
            (hedgeDoSecond rich q.action) u node)) = false := by
  let bits := fun node => hedgeIsSecond rich node
    ((w.smallOutcomeFlowModel rich).evalNodeUnder
      (hedgeDoSecond rich q.action) u node)
  let source := fun child =>
    if w.small child then
      hedgeXorPairBitsWithin G w.small child (fun latent _ => u latent)
    else false
  have flow : forall node, w.smallOutcomeFlowNodes node = true →
      bits node = Bool.xor (source node)
        (hedgeRoutingIncomingBits w.smallOutcomeFlowSuccessor bits node) := by
    intro node selected
    have free : hedgeDoSecond rich q.action node = none := by
      apply hedgeDoSecond_of_false rich q.action
      cases inReadout : w.rootReadoutNodes node with
      | true => exact w.rootReadoutNodes_avoids_action node inReadout
      | false =>
          have inSmall : w.small node = true := by
            simpa [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
              inReadout] using selected
          exact w.small_avoids_intervention node inSmall
    have equation := hedgeFlowReadoutModel_evalNodeUnder_bit rich
      w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
      w.smallOutcomeFlowSuccessor_wellFormed (w.smallParityModel rich)
      (hedgeForestIncidenceSource G w.small)
      (hedgeDoSecond rich q.action) u node selected free
    simpa [bits, source, HedgeWitness.smallOutcomeFlowModel,
      hedgeForestIncidenceSource] using equation
  rw [hedgeRoutingFlow_conservation w.smallOutcomeFlowNodes
    w.smallOutcomeFlowSuccessor w.smallOutcomeFlowSuccessor_wellFormed
    source bits flow]
  exact hedgeNodeXor_incidenceSource_union G w.small w.rootReadoutNodes u

/-- Every restricted incidence vector has an even number of true vertices. -/
theorem hedgeXorPairBitsWithinFrom_even
    (G : ObservedGraph S) (nodes : NodeSet S)
    (pairBits : Fin (pairRootCount G) → Bool) :
    (hedgeTrueVertices nodes
      (fun node => hedgeXorPairBitsWithinFrom G nodes node pairBits)).length %
        2 = 0 := by
  exact (foldl_xor_eq_false_iff_filter_even
    (fun node => hedgeXorPairBitsWithinFrom G nodes node pairBits)
    (NodeSet.members nodes)).mp
      (hedgeNodeXor_incidence G nodes pairBits)

/--
Incidence pattern required for `target` by a forest-parity equation.  Solving
the structural equation for its latent term gives observed bit XOR kept-parent
parity.
-/
def hedgeForestRequiredIncidence
    (rich : ObservedSignature.ValueRich S) (kept : ForestChild S)
    (target : S.Assignment) (child : Fin S.count) : Bool :=
  Bool.xor (hedgeIsSecond rich child (target child))
    (hedgeForestParentBitsFrom rich kept child
      (fun parent _ => target parent))

/--
The pair-root coordinates of a latent assignment realize the incidence
pattern required by that assignment's observed forest-parity output.
-/
theorem hedgeForestParityModel_pairBitsRealizes_eval
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (kept : ForestChild S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgePairBitsRealizes G nodes
        (hedgeForestRequiredIncidence rich kept
          ((hedgeForestParityModel G rich nodes kept).eval u))
        (hedgePairBitsOf G u) = true := by
  apply hedgePairBitsRealizes_of
  intro child hin
  rw [← hedgeXorPairBitsWithin_pairBitsOf G nodes u child]
  have equation :
      hedgeIsSecond rich child
          ((hedgeForestParityModel G rich nodes kept).eval u child) =
        Bool.xor
          (hedgeXorPairBitsWithin G nodes child (fun latent _ => u latent))
          (hedgeForestParentBitsFrom rich kept child
            (fun parent _ =>
              (hedgeForestParityModel G rich nodes kept).eval u parent)) := by
    change hedgeIsSecond rich child
        ((hedgeForestParityModel G rich nodes kept).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child) = _
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    exact hedgeForestParityOutput_bit_of_mem G rich nodes kept child _ _ hin
  unfold hedgeForestRequiredIncidence
  rw [equation]
  generalize
    hedgeXorPairBitsWithin G nodes child (fun latent _ => u latent) = pair
  generalize hedgeForestParentBitsFrom rich kept child
    (fun parent _ => (hedgeForestParityModel G rich nodes kept).eval u parent) =
      parents
  cases pair <;> cases parents <;> rfl

/-- Every observed output of a forest-parity model requires an even incidence. -/
theorem hedgeForestParityModel_requiredIncidence_even
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (kept : ForestChild S)
    (u : (hedgeLatentExtension G).Assignment) :
    (hedgeTrueVertices nodes
      (hedgeForestRequiredIncidence rich kept
        ((hedgeForestParityModel G rich nodes kept).eval u))).length % 2 = 0 := by
  let required := hedgeForestRequiredIncidence rich kept
    ((hedgeForestParityModel G rich nodes kept).eval u)
  let actual := fun node =>
    hedgeXorPairBitsWithinFrom G nodes node (hedgePairBitsOf G u)
  have realization :=
    hedgeForestParityModel_pairBitsRealizes_eval G rich nodes kept u
  have agrees :=
    hedgePairBitsRealizes_spec G nodes required (hedgePairBitsOf G u)
      realization
  have trueVerticesEq :
      hedgeTrueVertices nodes required = hedgeTrueVertices nodes actual := by
    unfold hedgeTrueVertices
    apply List.filter_congr
    intro node member
    exact (agrees node ((NodeSet.mem_members_iff nodes node).mp member)).symm
  rw [trueVerticesEq]
  exact hedgeXorPairBitsWithinFrom_even G nodes (hedgePairBitsOf G u)

/-- The small hedge model realizes its restricted forest equation on `F'`. -/
theorem HedgeWitness.smallParityModel_pairBitsRealizes_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgePairBitsRealizes G w.small
        (hedgeForestRequiredIncidence rich (restrictChild w.small w.child)
          ((w.smallParityModel rich).eval u))
        (hedgePairBitsOf G u) = true := by
  apply hedgePairBitsRealizes_of
  intro child hin
  rw [← hedgeXorPairBitsWithin_pairBitsOf G w.small u child]
  have equation :=
    w.smallParityModel_evalNodeUnder_bit rich
      (FiniteLatentSCM.noIntervention S) u child rfl hin
  change hedgeIsSecond rich child ((w.smallParityModel rich).eval u child) =
      Bool.xor
        (hedgeXorPairBitsWithin G w.small child (fun latent _ => u latent))
        (hedgeForestParentBitsFrom rich (restrictChild w.small w.child) child
          (fun parent _ => (w.smallParityModel rich).eval u parent)) at equation
  unfold hedgeForestRequiredIncidence
  rw [equation]
  generalize
    hedgeXorPairBitsWithin G w.small child (fun latent _ => u latent) = pair
  generalize hedgeForestParentBitsFrom rich
    (restrictChild w.small w.child) child
    (fun parent _ => (w.smallParityModel rich).eval u parent) = parents
  cases pair <;> cases parents <;> rfl

/-- Every small-model output requires an even incidence on the small forest. -/
theorem HedgeWitness.smallParityModel_requiredIncidence_even
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    (hedgeTrueVertices w.small
      (hedgeForestRequiredIncidence rich (restrictChild w.small w.child)
        ((w.smallParityModel rich).eval u))).length % 2 = 0 := by
  let required := hedgeForestRequiredIncidence rich
    (restrictChild w.small w.child) ((w.smallParityModel rich).eval u)
  let actual := fun node =>
    hedgeXorPairBitsWithinFrom G w.small node (hedgePairBitsOf G u)
  have realization := w.smallParityModel_pairBitsRealizes_eval rich u
  have agrees :=
    hedgePairBitsRealizes_spec G w.small required (hedgePairBitsOf G u)
      realization
  have trueVerticesEq :
      hedgeTrueVertices w.small required = hedgeTrueVertices w.small actual := by
    unfold hedgeTrueVertices
    apply List.filter_congr
    intro node member
    exact (agrees node
      ((NodeSet.mem_members_iff w.small node).mp member)).symm
  rw [trueVerticesEq]
  exact hedgeXorPairBitsWithinFrom_even G w.small (hedgePairBitsOf G u)

/-- Keep only pair-root coordinates whose two endpoints lie in `nodes`. -/
def hedgePairBitsRestrict (G : ObservedGraph S) (nodes : NodeSet S)
    (pairBits : Fin (pairRootCount G) → Bool) :
    Fin (pairRootCount G) → Bool :=
  fun root => if hedgePairRootWithin G nodes root then pairBits root else false

/-- Restricting a root vector to `nodes` preserves its incidence on `nodes`. -/
theorem hedgePairBitsRestrict_same
    (G : ObservedGraph S) (nodes : NodeSet S)
    (pairBits : Fin (pairRootCount G) → Bool) (child : Fin S.count) :
    hedgeXorPairBitsWithinFrom G nodes child
        (hedgePairBitsRestrict G nodes pairBits) =
      hedgeXorPairBitsWithinFrom G nodes child pairBits := by
  unfold hedgeXorPairBitsWithinFrom
  apply foldl_congr
  intro total root
  cases hinc :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child <;>
    cases hwithin : hedgePairRootWithin G nodes root <;>
    simp [hedgePairBitsRestrict, hwithin]

/--
A vector supported on roots internal to `inner` has zero incidence at every
vertex outside `inner`, even when incidence is measured in a larger forest.
-/
theorem hedgePairBitsRestrict_outside
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (pairBits : Fin (pairRootCount G) → Bool)
    (child : Fin S.count) (outside : inner child = false) :
    hedgeXorPairBitsWithinFrom G outer child
        (hedgePairBitsRestrict G inner pairBits) = false := by
  unfold hedgeXorPairBitsWithinFrom
  apply foldl_unchanged
  intro total root
  cases hinc :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child
  · simp
  · cases houter : hedgePairRootWithin G outer root
    · simp
    · cases hinner : hedgePairRootWithin G inner root
      · simp [hedgePairBitsRestrict, hinner]
      · have inside := hedgePairRootWithin_child G inner hinner hinc
        exact False.elim (Bool.false_ne_true (outside.symm.trans inside))

/-- On a selected node, the true-vertex list tests exactly the target bit. -/
theorem hedgeTrueVertices_spec (nodes : NodeSet S)
    (target : Fin S.count → Bool) (node : Fin S.count)
    (inside : nodes node = true) :
    decide (node ∈ hedgeTrueVertices nodes target) = target node := by
  cases htarget : target node <;>
    simp [hedgeTrueVertices, List.mem_filter,
      NodeSet.mem_members_iff, inside, htarget]

/--
An arbitrary target outside a nonempty inner component has an outer-component
incidence realization.  If the outside target has odd support, one inner
anchor is added before applying even-target surjectivity; that anchor is
irrelevant at every outside coordinate.
-/
theorem BidirectedComponent.pairBits_of_outside_target
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (target : Fin S.count → Bool) :
    Exists fun pairBits : Fin (pairRootCount G) → Bool =>
      ∀ node, outer node = true → inner node = false →
        hedgeXorPairBitsWithinFrom G outer node pairBits = target node := by
  rcases innerComponent.1 with ⟨anchor, anchorInside⟩
  have anchorOuter : outer anchor = true := subset anchor anchorInside
  let outsideNodes := NodeSet.diff outer inner
  let vertices := hedgeTrueVertices outsideNodes target
  have verticesNodup : vertices.Nodup := hedgeTrueVertices_nodup _ _
  have verticesOuter : ∀ node, node ∈ vertices → outer node = true := by
    intro node member
    exact NodeSet.diff_subset_left outer inner node
      (hedgeTrueVertices_inside outsideNodes target node member)
  have anchorNotMem : anchor ∉ vertices := by
    intro member
    have outsideAnchor :=
      hedgeTrueVertices_inside outsideNodes target anchor member
    have outsideFalse := NodeSet.disjoint_diff outer inner anchor anchorInside
    exact Bool.false_ne_true (outsideFalse.symm.trans outsideAnchor)
  by_cases even : vertices.length % 2 = 0
  · rcases outerComponent.pairBits_of_even_list G outer vertices
        verticesNodup verticesOuter even with ⟨pairBits, boundary⟩
    refine ⟨pairBits, ?_⟩
    intro node inOuter outInner
    rw [boundary node]
    have inOutside : outsideNodes node = true := by
      simp [outsideNodes, NodeSet.diff, inOuter, outInner]
    exact hedgeTrueVertices_spec outsideNodes target node inOutside
  · have extendedNodup : (anchor :: vertices).Nodup :=
      List.nodup_cons.mpr ⟨anchorNotMem, verticesNodup⟩
    have extendedOuter : ∀ node,
        node ∈ anchor :: vertices → outer node = true := by
      intro node member
      rcases List.mem_cons.mp member with equal | inVertices
      · exact equal ▸ anchorOuter
      · exact verticesOuter node inVertices
    have extendedEven : (anchor :: vertices).length % 2 = 0 := by
      simp only [List.length_cons]
      cases hmod : vertices.length % 2 with
      | zero => exact False.elim (even hmod)
      | succ remainder =>
          have remainderZero : remainder = 0 := by omega
          subst remainder
          simp [Nat.add_mod, hmod]
    rcases outerComponent.pairBits_of_even_list G outer
        (anchor :: vertices) extendedNodup extendedOuter extendedEven with
      ⟨pairBits, boundary⟩
    refine ⟨pairBits, ?_⟩
    intro node inOuter outInner
    rw [boundary node]
    have different : node ≠ anchor := by
      intro equal
      subst node
      exact Bool.false_ne_true (outInner.symm.trans anchorInside)
    have inOutside : outsideNodes node = true := by
      simp [outsideNodes, NodeSet.diff, inOuter, outInner]
    rw [show decide (node ∈ anchor :: vertices) =
        decide (node ∈ vertices) by simp [different]]
    exact hedgeTrueVertices_spec outsideNodes target node inOutside

/--
Piecewise incidence used by the nested parity model: inner vertices see only
inner roots, whereas outer vertices outside `inner` see every outer root.
-/
def hedgeNestedXorPairBitsWithinFrom (G : ObservedGraph S)
    (outer inner : NodeSet S) (node : Fin S.count)
    (pairBits : Fin (pairRootCount G) → Bool) : Bool :=
  if inner node then
    hedgeXorPairBitsWithinFrom G inner node pairBits
  else
    hedgeXorPairBitsWithinFrom G outer node pairBits

/--
Every outside target has a nested-incidence realization that is zero on the
inner component.  XORing an outer solution with its own inner restriction
cancels its inner incidence and leaves all outside coordinates unchanged.
-/
theorem BidirectedComponent.nestedOutsidePairBits
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (target : Fin S.count → Bool) :
    Exists fun pairBits : Fin (pairRootCount G) → Bool =>
      ∀ node, outer node = true →
        hedgeNestedXorPairBitsWithinFrom G outer inner node pairBits =
          if inner node then false else target node := by
  rcases outerComponent.pairBits_of_outside_target G outer inner
      innerComponent subset target with ⟨outerBits, realizesOutside⟩
  let innerPart := hedgePairBitsRestrict G inner outerBits
  let pairBits := hedgePairBitsXor G outerBits innerPart
  refine ⟨pairBits, ?_⟩
  intro node inOuter
  cases inInner : inner node
  · simp only [hedgeNestedXorPairBitsWithinFrom, inInner,
      Bool.false_eq_true, ↓reduceIte]
    rw [hedgeXorPairBitsWithinFrom_xor,
      realizesOutside node inOuter inInner,
      hedgePairBitsRestrict_outside G outer inner outerBits node inInner]
    simp
  · simp only [hedgeNestedXorPairBitsWithinFrom, inInner, ↓reduceIte]
    rw [hedgeXorPairBitsWithinFrom_xor, hedgePairBitsRestrict_same]
    generalize hedgeXorPairBitsWithinFrom G inner node outerBits = bit
    cases bit <;> rfl

/--
Surjectivity of the nested incidence map.  The only compatibility condition
is even parity on `inner`: an internal solution handles those coordinates,
and `nestedOutsidePairBits` independently supplies every remaining outer
coordinate.  Both vectors are restricted/XORed explicitly.
-/
theorem BidirectedComponent.nestedPairBits_of_inner_even
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (target : Fin S.count → Bool)
    (innerEven : (hedgeTrueVertices inner target).length % 2 = 0) :
    Exists fun pairBits : Fin (pairRootCount G) → Bool =>
      ∀ node, outer node = true →
        hedgeNestedXorPairBitsWithinFrom G outer inner node pairBits =
          target node := by
  rcases innerComponent.pairBits_of_even_target G inner target innerEven with
    ⟨innerBits, realizesInner⟩
  rcases outerComponent.nestedOutsidePairBits G outer inner innerComponent
      subset target with ⟨outsideBits, realizesOutside⟩
  let innerPart := hedgePairBitsRestrict G inner innerBits
  let pairBits := hedgePairBitsXor G innerPart outsideBits
  refine ⟨pairBits, ?_⟩
  intro node inOuter
  cases inInner : inner node
  · have outsideAt := realizesOutside node inOuter
    simp [hedgeNestedXorPairBitsWithinFrom, inInner] at outsideAt
    simp only [hedgeNestedXorPairBitsWithinFrom, inInner,
      Bool.false_eq_true, ↓reduceIte]
    rw [hedgeXorPairBitsWithinFrom_xor,
      hedgePairBitsRestrict_outside G outer inner innerBits node inInner,
      outsideAt]
    simp
  · have outsideAt := realizesOutside node inOuter
    simp [hedgeNestedXorPairBitsWithinFrom, inInner] at outsideAt
    simp only [hedgeNestedXorPairBitsWithinFrom, inInner, ↓reduceIte]
    rw [hedgeXorPairBitsWithinFrom_xor, hedgePairBitsRestrict_same,
      realizesInner node inInner, outsideAt]
    simp

/-- Nested incidence is linear in the pair-root vector. -/
theorem hedgeNestedXorPairBitsWithinFrom_xor
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (node : Fin S.count)
    (left right : Fin (pairRootCount G) → Bool) :
    hedgeNestedXorPairBitsWithinFrom G outer inner node
        (hedgePairBitsXor G left right) =
      Bool.xor
        (hedgeNestedXorPairBitsWithinFrom G outer inner node left)
        (hedgeNestedXorPairBitsWithinFrom G outer inner node right) := by
  unfold hedgeNestedXorPairBitsWithinFrom
  split <;> exact hedgeXorPairBitsWithinFrom_xor G _ node left right

/-- Executable realization test for the piecewise nested incidence map. -/
def hedgeNestedPairBitsRealizes (G : ObservedGraph S)
    (outer inner : NodeSet S) (target : Fin S.count → Bool)
    (pairBits : Fin (pairRootCount G) → Bool) : Bool :=
  (NodeSet.members outer).all fun node =>
    hedgeNestedXorPairBitsWithinFrom G outer inner node pairBits == target node

theorem hedgeNestedPairBitsRealizes_of
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (target : Fin S.count → Bool)
    (pairBits : Fin (pairRootCount G) → Bool)
    (agrees : ∀ node, outer node = true →
      hedgeNestedXorPairBitsWithinFrom G outer inner node pairBits =
        target node) :
    hedgeNestedPairBitsRealizes G outer inner target pairBits = true := by
  unfold hedgeNestedPairBitsRealizes
  refine List.all_eq_true.mpr ?_
  intro node member
  exact beq_iff_eq.mpr
    (agrees node ((NodeSet.mem_members_iff outer node).mp member))

theorem hedgeNestedPairBitsRealizes_spec
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (target : Fin S.count → Bool)
    (pairBits : Fin (pairRootCount G) → Bool)
    (realizes :
      hedgeNestedPairBitsRealizes G outer inner target pairBits = true) :
    ∀ node, outer node = true →
      hedgeNestedXorPairBitsWithinFrom G outer inner node pairBits =
        target node := by
  intro node inside
  have member := (NodeSet.mem_members_iff outer node).mpr inside
  exact beq_iff_eq.mp ((List.all_eq_true.mp realizes) node member)

/-- The exhaustive pair-bit enumeration detects every admissible nested target. -/
theorem BidirectedComponent.nestedPairBitsRealizes_any_of_inner_even
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (target : Fin S.count → Bool)
    (innerEven : (hedgeTrueVertices inner target).length % 2 = 0) :
    (hedgePairBitEnum G).any
      (hedgeNestedPairBitsRealizes G outer inner target) = true := by
  rcases outerComponent.nestedPairBits_of_inner_even G outer inner
      innerComponent subset target innerEven with ⟨pairBits, agrees⟩
  exact List.any_eq_true.mpr
    ⟨pairBits, hedgePairBitEnum_complete G pairBits,
      hedgeNestedPairBitsRealizes_of G outer inner target pairBits agrees⟩

/--
First enumerated root vector realizing a nested target whose inner restriction
is even.  As for `evenTargetPairBits`, finite search turns propositional
surjectivity into data without eliminating an existential into `Type`.
-/
def BidirectedComponent.nestedEvenTargetPairBits
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (target : Fin S.count → Bool)
    (innerEven : (hedgeTrueVertices inner target).length % 2 = 0) :
    Fin (pairRootCount G) → Bool :=
  listFirstAny (hedgePairBitEnum G)
    (hedgeNestedPairBitsRealizes G outer inner target)
    (outerComponent.nestedPairBitsRealizes_any_of_inner_even G outer inner
      innerComponent subset target innerEven)

/-- The computed nested vector realizes its target on every outer vertex. -/
theorem BidirectedComponent.nestedEvenTargetPairBits_spec
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (target : Fin S.count → Bool)
    (innerEven : (hedgeTrueVertices inner target).length % 2 = 0) :
    ∀ node, outer node = true →
      hedgeNestedXorPairBitsWithinFrom G outer inner node
          (outerComponent.nestedEvenTargetPairBits G outer inner
            innerComponent subset target innerEven) = target node :=
  hedgeNestedPairBitsRealizes_spec G outer inner target _
    (listFirstAny_pred (hedgePairBitEnum G)
      (hedgeNestedPairBitsRealizes G outer inner target)
      (outerComponent.nestedPairBitsRealizes_any_of_inner_even G outer inner
        innerComponent subset target innerEven))

/-- Root-vector translation between two admissible nested incidence targets. -/
def BidirectedComponent.nestedTargetTranslation
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (left right : Fin S.count → Bool)
    (leftEven : (hedgeTrueVertices inner left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices inner right).length % 2 = 0) :
    Fin (pairRootCount G) → Bool :=
  hedgePairBitsXor G
    (outerComponent.nestedEvenTargetPairBits G outer inner
      innerComponent subset left leftEven)
    (outerComponent.nestedEvenTargetPairBits G outer inner
      innerComponent subset right rightEven)

/-- The nested translation has incidence `left XOR right` on the outer forest. -/
theorem BidirectedComponent.nestedTargetTranslation_spec
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (left right : Fin S.count → Bool)
    (leftEven : (hedgeTrueVertices inner left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices inner right).length % 2 = 0) :
    ∀ node, outer node = true →
      hedgeNestedXorPairBitsWithinFrom G outer inner node
          (outerComponent.nestedTargetTranslation G outer inner
            innerComponent subset left right leftEven rightEven) =
        Bool.xor (left node) (right node) := by
  intro node inside
  rw [BidirectedComponent.nestedTargetTranslation,
    hedgeNestedXorPairBitsWithinFrom_xor,
    outerComponent.nestedEvenTargetPairBits_spec G outer inner
      innerComponent subset left leftEven node inside,
    outerComponent.nestedEvenTargetPairBits_spec G outer inner
      innerComponent subset right rightEven node inside]

/-- Nested translation carries the `left` realization test exactly to `right`. -/
theorem BidirectedComponent.nestedTargetTranslation_realizes_eq
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (left right : Fin S.count → Bool)
    (leftEven : (hedgeTrueVertices inner left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices inner right).length % 2 = 0)
    (pairBits : Fin (pairRootCount G) → Bool) :
    hedgeNestedPairBitsRealizes G outer inner right
        (hedgePairBitsXor G pairBits
          (outerComponent.nestedTargetTranslation G outer inner
            innerComponent subset left right leftEven rightEven)) =
      hedgeNestedPairBitsRealizes G outer inner left pairBits := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro translatedRealizes
    apply hedgeNestedPairBitsRealizes_of
    intro node inside
    have translatedAtNode :=
      hedgeNestedPairBitsRealizes_spec G outer inner right _
        translatedRealizes node inside
    rw [hedgeNestedXorPairBitsWithinFrom_xor,
      outerComponent.nestedTargetTranslation_spec G outer inner
        innerComponent subset left right leftEven rightEven node inside]
      at translatedAtNode
    cases hpair :
        hedgeNestedXorPairBitsWithinFrom G outer inner node pairBits <;>
      cases hleft : left node <;> cases hright : right node <;>
      simp_all
  · intro leftRealizes
    apply hedgeNestedPairBitsRealizes_of
    intro node inside
    rw [hedgeNestedXorPairBitsWithinFrom_xor,
      hedgeNestedPairBitsRealizes_spec G outer inner left pairBits
        leftRealizes node inside,
      outerComponent.nestedTargetTranslation_spec G outer inner
        innerComponent subset left right leftEven rightEven node inside]
    cases left node <;> cases right node <;> rfl

/--
All nested targets with even inner restriction have equally many pair-root
preimages.  The proof is the same explicit XOR permutation used for a single
component, now with the piecewise incidence realization test.
-/
theorem BidirectedComponent.nestedPairBitRealizers_length_eq_of_inner_even
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (left right : Fin S.count → Bool)
    (leftEven : (hedgeTrueVertices inner left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices inner right).length % 2 = 0) :
    ((hedgePairBitEnum G).filter
        (hedgeNestedPairBitsRealizes G outer inner left)).length =
      ((hedgePairBitEnum G).filter
        (hedgeNestedPairBitsRealizes G outer inner right)).length := by
  let delta := outerComponent.nestedTargetTranslation G outer inner
    innerComponent subset left right leftEven rightEven
  have translatedEnumeration := hedgePairBitEnum_map_xor_perm G delta
  have translatedRealizers :=
    translatedEnumeration.filter
      (hedgeNestedPairBitsRealizes G outer inner right)
  have predicateEq :
      hedgeNestedPairBitsRealizes G outer inner right ∘
          (fun pairBits => hedgePairBitsXor G pairBits delta) =
        hedgeNestedPairBitsRealizes G outer inner left := by
    funext pairBits
    exact outerComponent.nestedTargetTranslation_realizes_eq G outer inner
      innerComponent subset left right leftEven rightEven pairBits
  rw [List.filter_map, predicateEq] at translatedRealizers
  simpa using translatedRealizers.length_eq

/-- The all-false incidence target on observed vertices. -/
def hedgeZeroIncidenceTarget (S : ObservedSignature) : Fin S.count → Bool :=
  fun _node => false

theorem hedgeZeroIncidenceTarget_trueVertices (nodes : NodeSet S) :
    hedgeTrueVertices nodes (hedgeZeroIncidenceTarget S) = [] := by
  unfold hedgeTrueVertices hedgeZeroIncidenceTarget
  induction NodeSet.members nodes with
  | nil => rfl
  | cons node rest inductionHypothesis =>
      simp [inductionHypothesis]

/-- The zero incidence target has even support on every node set. -/
theorem hedgeZeroIncidenceTarget_even (nodes : NodeSet S) :
    (hedgeTrueVertices nodes (hedgeZeroIncidenceTarget S)).length % 2 = 0 := by
  rw [hedgeZeroIncidenceTarget_trueVertices]
  rfl

/--
Canonical even-target section supported only on roots internal to `nodes`.
Restriction preserves its requested incidence while making every external
coordinate inert.
-/
def BidirectedComponent.internalEvenTargetPairBits
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (target : Fin S.count → Bool)
    (even : (hedgeTrueVertices nodes target).length % 2 = 0) :
    Fin (pairRootCount G) → Bool :=
  hedgePairBitsRestrict G nodes
    (component.evenTargetPairBits G nodes target even)

/-- The internal section realizes its requested target on `nodes`. -/
theorem BidirectedComponent.internalEvenTargetPairBits_spec
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    (target : Fin S.count → Bool)
    (even : (hedgeTrueVertices nodes target).length % 2 = 0) :
    ∀ node, nodes node = true →
      hedgeXorPairBitsWithinFrom G nodes node
          (component.internalEvenTargetPairBits G nodes target even) =
        target node := by
  intro node inside
  rw [BidirectedComponent.internalEvenTargetPairBits,
    hedgePairBitsRestrict_same]
  exact component.evenTargetPairBits_spec G nodes target even node inside

/-- Pointwise-equal targets give the same canonical internal section. -/
theorem BidirectedComponent.internalEvenTargetPairBits_congr
    (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes)
    {left right : Fin S.count → Bool} (equal : left = right)
    (leftEven : (hedgeTrueVertices nodes left).length % 2 = 0)
    (rightEven : (hedgeTrueVertices nodes right).length % 2 = 0) :
    component.internalEvenTargetPairBits G nodes left leftEven =
      component.internalEvenTargetPairBits G nodes right rightEven := by
  subst right
  rfl

/--
At every vertex, a vector supported internally to `inner` has the same
incidence whether measured in `inner` or in a containing `outer` set.
-/
theorem hedgePairBitsRestrict_inside
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (subset : NodeSet.Subset inner outer)
    (pairBits : Fin (pairRootCount G) → Bool)
    (child : Fin S.count) :
    hedgeXorPairBitsWithinFrom G outer child
        (hedgePairBitsRestrict G inner pairBits) =
      hedgeXorPairBitsWithinFrom G inner child pairBits := by
  unfold hedgeXorPairBitsWithinFrom
  apply foldl_congr
  intro total root
  cases hinner : hedgePairRootWithin G inner root
  · cases hinc :
        (hedgeLatentExtension G).incident (hedgePairRoot G root) child <;>
      cases houter : hedgePairRootWithin G outer root <;>
      simp [hedgePairBitsRestrict, hinner]
  · have innerEndpoints := Bool.and_eq_true_iff.mp hinner
    have outerWithin : hedgePairRootWithin G outer root = true := by
      unfold hedgePairRootWithin at hinner ⊢
      exact Bool.and_eq_true_iff.mpr
        ⟨subset _ innerEndpoints.1, subset _ innerEndpoints.2⟩
    cases hinc :
        (hedgeLatentExtension G).incident (hedgePairRoot G root) child <;>
      simp [hedgePairBitsRestrict, hinner, outerWithin]

/-- Restricted incidence vanishes at a vertex outside the restricting set. -/
theorem hedgeXorPairBitsWithinFrom_of_child_outside
    (G : ObservedGraph S) (nodes : NodeSet S)
    (pairBits : Fin (pairRootCount G) → Bool) (child : Fin S.count)
    (outside : nodes child = false) :
    hedgeXorPairBitsWithinFrom G nodes child pairBits = false := by
  unfold hedgeXorPairBitsWithinFrom
  apply foldl_unchanged
  intro total root
  cases hinc :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) child
  · simp
  · cases hwithin : hedgePairRootWithin G nodes root
    · simp
    · have inside := hedgePairRootWithin_child G nodes hwithin hinc
      exact False.elim (Bool.false_ne_true (outside.symm.trans inside))

/--
If nested incidence is zero, the full outer incidence restricted to `inner`
has even support.  Full incidence is globally even, while the nested zero
equations make every outer coordinate outside `inner` false.
-/
theorem hedgeInnerFullIncidence_even_of_nested_zero
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (subset : NodeSet.Subset inner outer)
    (pairBits : Fin (pairRootCount G) → Bool)
    (realizes : hedgeNestedPairBitsRealizes G outer inner
      (hedgeZeroIncidenceTarget S) pairBits = true) :
    (hedgeTrueVertices inner
      (fun node => hedgeXorPairBitsWithinFrom G outer node pairBits)).length %
        2 = 0 := by
  let target := fun node =>
    hedgeXorPairBitsWithinFrom G outer node pairBits
  have nestedAgrees := hedgeNestedPairBitsRealizes_spec G outer inner
    (hedgeZeroIncidenceTarget S) pairBits realizes
  have trueVerticesEq :
      hedgeTrueVertices outer target = hedgeTrueVertices inner target := by
    unfold hedgeTrueVertices NodeSet.members
    rw [List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro node _member
    cases inOuter : outer node <;> cases inInner : inner node <;>
      cases htarget : target node
    all_goals simp
    · exact False.elim
        (Bool.false_ne_true (inOuter.symm.trans (subset node inInner)))
    · have outsideAt := nestedAgrees node inOuter
      simp [hedgeNestedXorPairBitsWithinFrom, inInner,
        hedgeZeroIncidenceTarget] at outsideAt
      exact False.elim (Bool.false_ne_true (outsideAt.symm.trans htarget))
  rw [← trueVerticesEq]
  exact hedgeXorPairBitsWithinFrom_even G outer pairBits

/-- Full outer incidence, masked to the inner set. -/
def hedgeInnerFullIncidenceTarget (G : ObservedGraph S)
    (outer inner : NodeSet S) (pairBits : Fin (pairRootCount G) → Bool)
    (node : Fin S.count) : Bool :=
  if inner node then
    hedgeXorPairBitsWithinFrom G outer node pairBits
  else
    false

theorem hedgeInnerFullIncidenceTarget_trueVertices
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (pairBits : Fin (pairRootCount G) → Bool) :
    hedgeTrueVertices inner
        (hedgeInnerFullIncidenceTarget G outer inner pairBits) =
      hedgeTrueVertices inner
        (fun node => hedgeXorPairBitsWithinFrom G outer node pairBits) := by
  unfold hedgeTrueVertices
  apply List.filter_congr
  intro node member
  have inside := (NodeSet.mem_members_iff inner node).mp member
  simp [hedgeInnerFullIncidenceTarget, inside]

theorem hedgeInnerFullIncidenceTarget_even_of_nested_zero
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (subset : NodeSet.Subset inner outer)
    (pairBits : Fin (pairRootCount G) → Bool)
    (realizes : hedgeNestedPairBitsRealizes G outer inner
      (hedgeZeroIncidenceTarget S) pairBits = true) :
    (hedgeTrueVertices inner
      (hedgeInnerFullIncidenceTarget G outer inner pairBits)).length % 2 = 0 := by
  rw [hedgeInnerFullIncidenceTarget_trueVertices]
  exact hedgeInnerFullIncidence_even_of_nested_zero G outer inner subset
    pairBits realizes

/--
Map an ordinary outer-incidence kernel vector to a nested-incidence kernel
vector.  Subtracting a canonical internal section cancels exactly its inner
incidence and preserves all outside coordinates.
-/
def BidirectedComponent.largeKernelToNestedPairBits
    (G : ObservedGraph S) (inner : NodeSet S)
    (innerComponent : BidirectedComponent G inner)
    (pairBits : Fin (pairRootCount G) → Bool) :
    Fin (pairRootCount G) → Bool :=
  let target := fun node =>
    hedgeXorPairBitsWithinFrom G inner node pairBits
  hedgePairBitsXor G pairBits
    (innerComponent.internalEvenTargetPairBits G inner target
      (hedgeXorPairBitsWithinFrom_even G inner pairBits))

theorem BidirectedComponent.largeKernelToNestedPairBits_realizes
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (innerComponent : BidirectedComponent G inner)
    (pairBits : Fin (pairRootCount G) → Bool)
    (largeZero : hedgePairBitsRealizes G outer
      (hedgeZeroIncidenceTarget S) pairBits = true) :
    hedgeNestedPairBitsRealizes G outer inner
        (hedgeZeroIncidenceTarget S)
        (innerComponent.largeKernelToNestedPairBits G inner pairBits) = true := by
  apply hedgeNestedPairBitsRealizes_of
  intro node inOuter
  cases inInner : inner node
  · simp only [hedgeNestedXorPairBitsWithinFrom, inInner,
      Bool.false_eq_true, ↓reduceIte]
    rw [BidirectedComponent.largeKernelToNestedPairBits,
      hedgeXorPairBitsWithinFrom_xor,
      hedgePairBitsRealizes_spec G outer (hedgeZeroIncidenceTarget S)
        pairBits largeZero node inOuter,
      BidirectedComponent.internalEvenTargetPairBits,
      hedgePairBitsRestrict_outside G outer inner _ node inInner]
    rfl
  · simp only [hedgeNestedXorPairBitsWithinFrom, inInner, ↓reduceIte]
    rw [BidirectedComponent.largeKernelToNestedPairBits,
      hedgeXorPairBitsWithinFrom_xor,
      innerComponent.internalEvenTargetPairBits_spec G inner _ _ node inInner]
    generalize hedgeXorPairBitsWithinFrom G inner node pairBits = bit
    cases bit <;> rfl

/-- The ordinary-to-nested kernel map is injective on the ordinary zero fiber. -/
theorem BidirectedComponent.largeKernelToNestedPairBits_injective
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (subset : NodeSet.Subset inner outer)
    (innerComponent : BidirectedComponent G inner)
    (left right : Fin (pairRootCount G) → Bool)
    (leftZero : hedgePairBitsRealizes G outer
      (hedgeZeroIncidenceTarget S) left = true)
    (rightZero : hedgePairBitsRealizes G outer
      (hedgeZeroIncidenceTarget S) right = true)
    (equal : innerComponent.largeKernelToNestedPairBits G inner left =
      innerComponent.largeKernelToNestedPairBits G inner right) :
    left = right := by
  let leftTarget := fun node =>
    hedgeXorPairBitsWithinFrom G inner node left
  let rightTarget := fun node =>
    hedgeXorPairBitsWithinFrom G inner node right
  let leftCorrection := innerComponent.internalEvenTargetPairBits G inner
    leftTarget (hedgeXorPairBitsWithinFrom_even G inner left)
  let rightCorrection := innerComponent.internalEvenTargetPairBits G inner
    rightTarget (hedgeXorPairBitsWithinFrom_even G inner right)
  have targetEq : leftTarget = rightTarget := by
    funext node
    by_cases inInner : inner node = true
    · have atNode := congrArg
        (fun bits => hedgeXorPairBitsWithinFrom G outer node bits) equal
      have inOuter := subset node inInner
      change hedgeXorPairBitsWithinFrom G outer node
          (hedgePairBitsXor G left leftCorrection) =
        hedgeXorPairBitsWithinFrom G outer node
          (hedgePairBitsXor G right rightCorrection) at atNode
      have leftCorrectionAt :
          hedgeXorPairBitsWithinFrom G outer node leftCorrection =
            leftTarget node := by
        unfold leftCorrection BidirectedComponent.internalEvenTargetPairBits
        rw [hedgePairBitsRestrict_inside G outer inner subset,
          innerComponent.evenTargetPairBits_spec G inner leftTarget _
            node inInner]
      have rightCorrectionAt :
          hedgeXorPairBitsWithinFrom G outer node rightCorrection =
            rightTarget node := by
        unfold rightCorrection BidirectedComponent.internalEvenTargetPairBits
        rw [hedgePairBitsRestrict_inside G outer inner subset,
          innerComponent.evenTargetPairBits_spec G inner rightTarget _
            node inInner]
      rw [hedgeXorPairBitsWithinFrom_xor,
        hedgeXorPairBitsWithinFrom_xor,
        hedgePairBitsRealizes_spec G outer (hedgeZeroIncidenceTarget S)
          left leftZero node inOuter,
        hedgePairBitsRealizes_spec G outer (hedgeZeroIncidenceTarget S)
          right rightZero node inOuter,
        leftCorrectionAt, rightCorrectionAt] at atNode
      simpa [leftTarget, rightTarget, hedgeZeroIncidenceTarget] using atNode
    · have leftFalse : leftTarget node = false := by
        unfold leftTarget
        exact hedgeXorPairBitsWithinFrom_of_child_outside G inner left node
          (Bool.eq_false_iff.mpr inInner)
      have rightFalse : rightTarget node = false := by
        unfold rightTarget
        exact hedgeXorPairBitsWithinFrom_of_child_outside G inner right node
          (Bool.eq_false_iff.mpr inInner)
      rw [leftFalse, rightFalse]
  have correctionEq : leftCorrection = rightCorrection := by
    unfold leftCorrection rightCorrection
    exact innerComponent.internalEvenTargetPairBits_congr G inner targetEq _ _
  change hedgePairBitsXor G left leftCorrection =
      hedgePairBitsXor G right rightCorrection at equal
  rw [correctionEq] at equal
  have twice := congrArg
    (fun bits => hedgePairBitsXor G bits rightCorrection) equal
  simpa only [hedgePairBitsXor_self_right] using twice

/--
Map a nested-incidence kernel vector back to an ordinary outer kernel vector.
The correction is enabled only when the masked full incidence is even, making
the definition total; nested kernel membership proves that branch is taken.
-/
def BidirectedComponent.nestedKernelToLargePairBits
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (innerComponent : BidirectedComponent G inner)
    (pairBits : Fin (pairRootCount G) → Bool) :
    Fin (pairRootCount G) → Bool :=
  let target := hedgeInnerFullIncidenceTarget G outer inner pairBits
  if even : (hedgeTrueVertices inner target).length % 2 = 0 then
    hedgePairBitsXor G pairBits
      (innerComponent.internalEvenTargetPairBits G inner target even)
  else
    pairBits

theorem BidirectedComponent.nestedKernelToLargePairBits_realizes
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (subset : NodeSet.Subset inner outer)
    (innerComponent : BidirectedComponent G inner)
    (pairBits : Fin (pairRootCount G) → Bool)
    (nestedZero : hedgeNestedPairBitsRealizes G outer inner
      (hedgeZeroIncidenceTarget S) pairBits = true) :
    hedgePairBitsRealizes G outer (hedgeZeroIncidenceTarget S)
        (innerComponent.nestedKernelToLargePairBits G outer inner pairBits) =
      true := by
  have even := hedgeInnerFullIncidenceTarget_even_of_nested_zero
    G outer inner subset pairBits nestedZero
  rw [BidirectedComponent.nestedKernelToLargePairBits, dif_pos even]
  apply hedgePairBitsRealizes_of
  intro node inOuter
  cases inInner : inner node
  · have nestedAt := hedgeNestedPairBitsRealizes_spec G outer inner
      (hedgeZeroIncidenceTarget S) pairBits nestedZero node inOuter
    simp [hedgeNestedXorPairBitsWithinFrom, inInner,
      hedgeZeroIncidenceTarget] at nestedAt
    rw [hedgeXorPairBitsWithinFrom_xor, nestedAt,
      BidirectedComponent.internalEvenTargetPairBits,
      hedgePairBitsRestrict_outside G outer inner _ node inInner]
    rfl
  · rw [hedgeXorPairBitsWithinFrom_xor]
    have correctionAt :
        hedgeXorPairBitsWithinFrom G outer node
            (innerComponent.internalEvenTargetPairBits G inner
              (hedgeInnerFullIncidenceTarget G outer inner pairBits) even) =
          hedgeXorPairBitsWithinFrom G outer node pairBits := by
      unfold BidirectedComponent.internalEvenTargetPairBits
      rw [hedgePairBitsRestrict_inside G outer inner subset,
        innerComponent.evenTargetPairBits_spec G inner _ even node inInner]
      simp [hedgeInnerFullIncidenceTarget, inInner]
    rw [correctionAt]
    generalize hedgeXorPairBitsWithinFrom G outer node pairBits = bit
    cases bit <;> rfl

/-- The nested-to-ordinary kernel map is injective on the nested zero fiber. -/
theorem BidirectedComponent.nestedKernelToLargePairBits_injective
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (subset : NodeSet.Subset inner outer)
    (innerComponent : BidirectedComponent G inner)
    (left right : Fin (pairRootCount G) → Bool)
    (leftZero : hedgeNestedPairBitsRealizes G outer inner
      (hedgeZeroIncidenceTarget S) left = true)
    (rightZero : hedgeNestedPairBitsRealizes G outer inner
      (hedgeZeroIncidenceTarget S) right = true)
    (equal : innerComponent.nestedKernelToLargePairBits G outer inner left =
      innerComponent.nestedKernelToLargePairBits G outer inner right) :
    left = right := by
  let leftTarget := hedgeInnerFullIncidenceTarget G outer inner left
  let rightTarget := hedgeInnerFullIncidenceTarget G outer inner right
  have leftEven := hedgeInnerFullIncidenceTarget_even_of_nested_zero
    G outer inner subset left leftZero
  have rightEven := hedgeInnerFullIncidenceTarget_even_of_nested_zero
    G outer inner subset right rightZero
  let leftCorrection := innerComponent.internalEvenTargetPairBits G inner
    leftTarget leftEven
  let rightCorrection := innerComponent.internalEvenTargetPairBits G inner
    rightTarget rightEven
  have expandedEqual :
      hedgePairBitsXor G left leftCorrection =
        hedgePairBitsXor G right rightCorrection := by
    simpa [BidirectedComponent.nestedKernelToLargePairBits,
      leftEven, rightEven, leftTarget, rightTarget,
      leftCorrection, rightCorrection] using equal
  have targetEq : leftTarget = rightTarget := by
    funext node
    by_cases inInner : inner node = true
    · have inOuter := subset node inInner
      have atNode := congrArg
        (fun bits => hedgeXorPairBitsWithinFrom G inner node bits)
        expandedEqual
      change hedgeXorPairBitsWithinFrom G inner node
          (hedgePairBitsXor G left leftCorrection) =
        hedgeXorPairBitsWithinFrom G inner node
          (hedgePairBitsXor G right rightCorrection) at atNode
      have leftNestedAt := hedgeNestedPairBitsRealizes_spec G outer inner
        (hedgeZeroIncidenceTarget S) left leftZero node inOuter
      have rightNestedAt := hedgeNestedPairBitsRealizes_spec G outer inner
        (hedgeZeroIncidenceTarget S) right rightZero node inOuter
      simp [hedgeNestedXorPairBitsWithinFrom, inInner,
        hedgeZeroIncidenceTarget] at leftNestedAt rightNestedAt
      have leftCorrectionAt :
          hedgeXorPairBitsWithinFrom G inner node leftCorrection =
            leftTarget node := by
        unfold leftCorrection
        exact innerComponent.internalEvenTargetPairBits_spec G inner
          leftTarget leftEven node inInner
      have rightCorrectionAt :
          hedgeXorPairBitsWithinFrom G inner node rightCorrection =
            rightTarget node := by
        unfold rightCorrection
        exact innerComponent.internalEvenTargetPairBits_spec G inner
          rightTarget rightEven node inInner
      rw [hedgeXorPairBitsWithinFrom_xor,
        hedgeXorPairBitsWithinFrom_xor, leftNestedAt, rightNestedAt,
        leftCorrectionAt, rightCorrectionAt] at atNode
      simpa [leftTarget, rightTarget, hedgeZeroIncidenceTarget] using atNode
    · have leftFalse : leftTarget node = false := by
        simp [leftTarget, hedgeInnerFullIncidenceTarget, inInner]
      have rightFalse : rightTarget node = false := by
        simp [rightTarget, hedgeInnerFullIncidenceTarget, inInner]
      rw [leftFalse, rightFalse]
  have correctionEq : leftCorrection = rightCorrection := by
    unfold leftCorrection rightCorrection
    exact innerComponent.internalEvenTargetPairBits_congr G inner targetEq _ _
  rw [correctionEq] at expandedEqual
  have twice := congrArg
    (fun bits => hedgePairBitsXor G bits rightCorrection) expandedEqual
  simpa only [hedgePairBitsXor_self_right] using twice

/--
The ordinary and nested zero fibers have equal size.  Explicit injections in
both directions are mapped over the duplicate-free filtered enumeration;
constructive finite-list cardinality and antisymmetry finish the comparison.
-/
theorem BidirectedComponent.pairBitKernel_length_eq_nested
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (subset : NodeSet.Subset inner outer)
    (innerComponent : BidirectedComponent G inner) :
    ((hedgePairBitEnum G).filter
        (hedgePairBitsRealizes G outer
          (hedgeZeroIncidenceTarget S))).length =
      ((hedgePairBitEnum G).filter
        (hedgeNestedPairBitsRealizes G outer inner
          (hedgeZeroIncidenceTarget S))).length := by
  let largeKernel := (hedgePairBitEnum G).filter
    (hedgePairBitsRealizes G outer (hedgeZeroIncidenceTarget S))
  let nestedKernel := (hedgePairBitEnum G).filter
    (hedgeNestedPairBitsRealizes G outer inner
      (hedgeZeroIncidenceTarget S))
  let forward := innerComponent.largeKernelToNestedPairBits G inner
  let backward :=
    innerComponent.nestedKernelToLargePairBits G outer inner
  have largeNodup : largeKernel.Nodup :=
    List.Sublist.nodup List.filter_sublist (hedgePairBitEnum_nodup G)
  have nestedNodup : nestedKernel.Nodup :=
    List.Sublist.nodup List.filter_sublist (hedgePairBitEnum_nodup G)
  have forwardNodup : (largeKernel.map forward).Nodup := by
    apply Probability.ConstructivePermutation.nodup_map_of_injective_on
      forward largeKernel
    · intro left leftMem right rightMem equal
      exact innerComponent.largeKernelToNestedPairBits_injective
        G outer inner subset left right
        (List.mem_filter.mp leftMem).2 (List.mem_filter.mp rightMem).2 equal
    · exact largeNodup
  have forwardSubset : ∀ value, value ∈ largeKernel.map forward →
      value ∈ nestedKernel := by
    intro value member
    rcases List.mem_map.mp member with ⟨source, sourceMem, equal⟩
    subst value
    apply List.mem_filter.mpr
    exact ⟨hedgePairBitEnum_complete G _,
      innerComponent.largeKernelToNestedPairBits_realizes
        G outer inner source (List.mem_filter.mp sourceMem).2⟩
  have forwardLe : largeKernel.length ≤ nestedKernel.length := by
    have mappedLe :=
      Probability.ConstructivePermutation.length_le_of_nodup_subset
        forwardNodup forwardSubset
    simpa using mappedLe
  have backwardNodup : (nestedKernel.map backward).Nodup := by
    apply Probability.ConstructivePermutation.nodup_map_of_injective_on
      backward nestedKernel
    · intro left leftMem right rightMem equal
      exact innerComponent.nestedKernelToLargePairBits_injective
        G outer inner subset left right
        (List.mem_filter.mp leftMem).2 (List.mem_filter.mp rightMem).2 equal
    · exact nestedNodup
  have backwardSubset : ∀ value, value ∈ nestedKernel.map backward →
      value ∈ largeKernel := by
    intro value member
    rcases List.mem_map.mp member with ⟨source, sourceMem, equal⟩
    subst value
    apply List.mem_filter.mpr
    exact ⟨hedgePairBitEnum_complete G _,
      innerComponent.nestedKernelToLargePairBits_realizes
        G outer inner subset source (List.mem_filter.mp sourceMem).2⟩
  have backwardLe : nestedKernel.length ≤ largeKernel.length := by
    have mappedLe :=
      Probability.ConstructivePermutation.length_le_of_nodup_subset
        backwardNodup backwardSubset
    simpa using mappedLe
  exact Nat.le_antisymm forwardLe backwardLe

/--
Cross-map fiber equality: an even ordinary outer target and an arbitrary
nested target with even inner restriction have the same number of pair-root
preimages.  Each map is reduced to its zero fiber, whose sizes agree above.
-/
theorem BidirectedComponent.pairBitRealizers_length_eq_nested
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (outerComponent : BidirectedComponent G outer)
    (innerComponent : BidirectedComponent G inner)
    (subset : NodeSet.Subset inner outer)
    (largeTarget nestedTarget : Fin S.count → Bool)
    (largeEven : (hedgeTrueVertices outer largeTarget).length % 2 = 0)
    (nestedEven : (hedgeTrueVertices inner nestedTarget).length % 2 = 0) :
    ((hedgePairBitEnum G).filter
        (hedgePairBitsRealizes G outer largeTarget)).length =
      ((hedgePairBitEnum G).filter
        (hedgeNestedPairBitsRealizes G outer inner nestedTarget)).length := by
  calc
    ((hedgePairBitEnum G).filter
        (hedgePairBitsRealizes G outer largeTarget)).length =
        ((hedgePairBitEnum G).filter
          (hedgePairBitsRealizes G outer
            (hedgeZeroIncidenceTarget S))).length :=
      outerComponent.pairBitRealizers_length_eq_of_even G outer
        largeTarget (hedgeZeroIncidenceTarget S) largeEven
        (hedgeZeroIncidenceTarget_even outer)
    _ = ((hedgePairBitEnum G).filter
          (hedgeNestedPairBitsRealizes G outer inner
            (hedgeZeroIncidenceTarget S))).length :=
      innerComponent.pairBitKernel_length_eq_nested G outer inner subset
    _ = ((hedgePairBitEnum G).filter
          (hedgeNestedPairBitsRealizes G outer inner nestedTarget)).length :=
      outerComponent.nestedPairBitRealizers_length_eq_of_inner_even
        G outer inner innerComponent subset
        (hedgeZeroIncidenceTarget S) nestedTarget
        (hedgeZeroIncidenceTarget_even inner) nestedEven

/-! ### Lifting pair-root fibers to complete latent assignments -/

/--
The private coordinates of the hedge latent extension, indexed directly by
their observed children.  Separating this dependent vector from the Boolean
pair-root vector makes the multiplicity ignored by the parity mechanisms
explicit without changing the latent extension itself.
-/
abbrev HedgePrivateCoordinates (S : ObservedSignature) :=
  (child : Fin S.count) → Fin (hedgePrivateCard S child)

instance : DecidableEq (HedgePrivateCoordinates S) :=
  FiniteProduct.assignmentDecidableEq S.count
    (fun child => Fin (hedgePrivateCard S child)) (fun _child => inferInstance)

/-- Read every canonical private coordinate from a hedge latent assignment. -/
def hedgePrivateCoordinatesOf (G : ObservedGraph S)
    (u : (hedgeLatentExtension G).Assignment) : HedgePrivateCoordinates S :=
  fun child => hedgePrivateIndex G child (fun root _incident => u root)

/-- The project-specific pair-root embedding is Lean's left `Fin` injection. -/
theorem hedgePairRoot_eq_castAdd (G : ObservedGraph S)
    (root : Fin (pairRootCount G)) :
    hedgePairRoot G root = Fin.castAdd S.count root := by
  apply Fin.ext
  rfl

/-- The project-specific private-root embedding is Lean's right `Fin` injection. -/
theorem hedgePrivateRoot_eq_natAdd (G : ObservedGraph S)
    (child : Fin S.count) :
    hedgePrivateRoot G child = Fin.natAdd (pairRootCount G) child := by
  apply Fin.ext
  rfl

/--
Reassemble a hedge latent assignment from its two independent coordinate
blocks.  Prefix roots receive the prescribed Boolean values; every remaining
root is the canonical private root of `hedgeChildOfPrivate` and receives that
child's finite enumeration index.
-/
def hedgeLatentOfCoordinates (G : ObservedGraph S)
    (pairBits : Fin (pairRootCount G) → Bool)
    (privateCoordinates : HedgePrivateCoordinates S) :
    (hedgeLatentExtension G).Assignment :=
  Fin.addCases
    (fun root =>
      cast (hedgeLatentValue_pair G root).symm (pairBits root))
    (fun child =>
      cast
        (hedgeLatentValue_eq_fin G (hedgePrivateRoot G child)
          (hedgePrivateRoot_not_pair G child)).symm
        ((privateCoordinates child).cast
          (by rw [hedgeChildOfPrivate_privateRoot])))

/-- Coordinate reassembly computes directly on a pair-root index. -/
theorem hedgeLatentOfCoordinates_pair (G : ObservedGraph S)
    (pairBits : Fin (pairRootCount G) → Bool)
    (privateCoordinates : HedgePrivateCoordinates S)
    (root : Fin (pairRootCount G)) :
    hedgeLatentOfCoordinates G pairBits privateCoordinates
        (hedgePairRoot G root) =
      cast (hedgeLatentValue_pair G root).symm (pairBits root) := by
  unfold hedgeLatentOfCoordinates hedgePairRoot
  exact Fin.addCases_left root

/-- Coordinate reassembly computes directly on a canonical private root. -/
theorem hedgeLatentOfCoordinates_private (G : ObservedGraph S)
    (pairBits : Fin (pairRootCount G) → Bool)
    (privateCoordinates : HedgePrivateCoordinates S)
    (child : Fin S.count) :
    hedgeLatentOfCoordinates G pairBits privateCoordinates
        (hedgePrivateRoot G child) =
      cast
        (hedgeLatentValue_eq_fin G (hedgePrivateRoot G child)
          (hedgePrivateRoot_not_pair G child)).symm
        ((privateCoordinates child).cast
          (by rw [hedgeChildOfPrivate_privateRoot])) := by
  unfold hedgeLatentOfCoordinates hedgePrivateRoot
  exact Fin.addCases_right child

/-- Transporting a value along an equality and immediately back is identity. -/
theorem cast_symm_cast_value {A B : Type} (equal : A = B) (value : B) :
    cast equal (cast equal.symm value) = value := by
  cases equal
  rfl

/-- Transport along a type equality is injective. -/
theorem cast_injective_value {A B : Type} (equal : A = B)
    {left right : A} (same : cast equal left = cast equal right) :
    left = right := by
  cases equal
  exact same

/-- Reassembling coordinates preserves the pair-root block exactly. -/
theorem hedgePairBitsOf_latentOfCoordinates (G : ObservedGraph S)
    (pairBits : Fin (pairRootCount G) → Bool)
    (privateCoordinates : HedgePrivateCoordinates S) :
    hedgePairBitsOf G
        (hedgeLatentOfCoordinates G pairBits privateCoordinates) =
      pairBits := by
  funext root
  unfold hedgePairBitsOf
  rw [hedgeLatentOfCoordinates_pair]
  exact cast_symm_cast_value (hedgeLatentValue_pair G root) (pairBits root)

/-- Reassembling coordinates preserves every private coordinate exactly. -/
theorem hedgePrivateCoordinatesOf_latentOfCoordinates
    (G : ObservedGraph S)
    (pairBits : Fin (pairRootCount G) → Bool)
    (privateCoordinates : HedgePrivateCoordinates S) :
    hedgePrivateCoordinatesOf G
        (hedgeLatentOfCoordinates G pairBits privateCoordinates) =
      privateCoordinates := by
  funext child
  apply Fin.ext
  unfold hedgePrivateCoordinatesOf hedgePrivateIndex
  change
    ((cast
      (hedgeLatentValue_eq_fin G (hedgePrivateRoot G child)
        (hedgePrivateRoot_not_pair G child))
      (hedgeLatentOfCoordinates G pairBits privateCoordinates
        (hedgePrivateRoot G child))).cast _).val =
      (privateCoordinates child).val
  rw [hedgeLatentOfCoordinates_private, cast_cast]
  simp [Fin.cast]

/-- Pair and private coordinates jointly determine a hedge latent assignment. -/
theorem hedgeLatentAssignment_ext (G : ObservedGraph S)
    {left right : (hedgeLatentExtension G).Assignment}
    (pairEqual : hedgePairBitsOf G left = hedgePairBitsOf G right)
    (privateEqual : hedgePrivateCoordinatesOf G left =
      hedgePrivateCoordinatesOf G right) :
    left = right := by
  funext root
  refine Fin.addCases ?_ ?_ root
  · intro pairRoot
    apply cast_injective_value (hedgeLatentValue_pair G pairRoot)
    exact congrFun pairEqual pairRoot
  · intro child
    change left (hedgePrivateRoot G child) =
      right (hedgePrivateRoot G child)
    have leftInverse := hedgePrivateIndex_inv_at_child G left child
    have rightInverse := hedgePrivateIndex_inv_at_child G right child
    rw [← leftInverse, ← rightInverse]
    have coordinateEqual := congrFun privateEqual child
    change hedgePrivateIndex G child (fun root _ => left root) =
      hedgePrivateIndex G child (fun root _ => right root) at coordinateEqual
    rw [coordinateEqual]

/--
Pair and private coordinate recovery is a left inverse of reassembly.  The
proof covers pair-prefix and private-suffix roots separately and uses the
canonical private-root section instead of comparing dependent types by hand.
-/
theorem hedgeLatentOfCoordinates_recover (G : ObservedGraph S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeLatentOfCoordinates G (hedgePairBitsOf G u)
        (hedgePrivateCoordinatesOf G u) =
      u := by
  apply hedgeLatentAssignment_ext G
  · exact hedgePairBitsOf_latentOfCoordinates G _ _
  · exact hedgePrivateCoordinatesOf_latentOfCoordinates G _ _

/-- Package the two coordinate blocks as the source of the reassembly map. -/
def hedgeLatentOfCoordinatePair (G : ObservedGraph S)
    (coordinates :
      (Fin (pairRootCount G) → Bool) × HedgePrivateCoordinates S) :
    (hedgeLatentExtension G).Assignment :=
  hedgeLatentOfCoordinates G coordinates.1 coordinates.2

/-- Distinct coordinate pairs reassemble to distinct latent assignments. -/
theorem hedgeLatentOfCoordinatePair_injective (G : ObservedGraph S)
    {left right :
      (Fin (pairRootCount G) → Bool) × HedgePrivateCoordinates S}
    (equal : hedgeLatentOfCoordinatePair G left =
      hedgeLatentOfCoordinatePair G right) :
    left = right := by
  apply Prod.ext
  · have recovered := congrArg (hedgePairBitsOf G) equal
    simpa [hedgeLatentOfCoordinatePair,
      hedgePairBitsOf_latentOfCoordinates] using recovered
  · have recovered := congrArg (hedgePrivateCoordinatesOf G) equal
    simpa [hedgeLatentOfCoordinatePair,
      hedgePrivateCoordinatesOf_latentOfCoordinates] using recovered

/-- Duplicate-free exhaustive enumeration of all private-coordinate vectors. -/
def hedgePrivateCoordinateEnum (S : ObservedSignature) :
    List (HedgePrivateCoordinates S) :=
  deduplicate
    (FiniteProduct.enumeration S.count
      (fun child => Fin (hedgePrivateCard S child))
      (fun child => List.finRange (hedgePrivateCard S child)))

theorem hedgePrivateCoordinateEnum_complete (S : ObservedSignature)
    (privateCoordinates : HedgePrivateCoordinates S) :
    privateCoordinates ∈ hedgePrivateCoordinateEnum S := by
  unfold hedgePrivateCoordinateEnum
  rw [mem_deduplicate]
  exact FiniteProduct.enumeration_complete S.count
    (fun child => Fin (hedgePrivateCard S child))
    (fun child => List.finRange (hedgePrivateCard S child))
    (fun _child value => List.mem_finRange value) privateCoordinates

theorem hedgePrivateCoordinateEnum_nodup (S : ObservedSignature) :
    (hedgePrivateCoordinateEnum S).Nodup := by
  unfold hedgePrivateCoordinateEnum
  exact deduplicate_nodup _

/--
Private coordinates compatible with an observed target outside `nodes`.
Coordinates at selected parity nodes remain unrestricted because those
mechanisms ignore their private roots.
-/
def hedgePrivateCoordinatesFit (outer : NodeSet S) (target : S.Assignment)
    (privateCoordinates : HedgePrivateCoordinates S) : Bool :=
  (List.finRange S.count).all fun child =>
    if outer child then true
    else privateCoordinates child == hedgeIndexOfValue S child (target child)

theorem hedgePrivateCoordinatesFit_of (outer : NodeSet S)
    (target : S.Assignment)
    (privateCoordinates : HedgePrivateCoordinates S)
    (outside : ∀ child, outer child = false →
      privateCoordinates child = hedgeIndexOfValue S child (target child)) :
    hedgePrivateCoordinatesFit outer target privateCoordinates = true := by
  unfold hedgePrivateCoordinatesFit
  apply List.all_eq_true.mpr
  intro child _member
  cases inside : outer child
  · simpa [inside] using beq_iff_eq.mpr (outside child inside)
  · rfl

theorem hedgePrivateCoordinatesFit_spec (outer : NodeSet S)
    (target : S.Assignment)
    (privateCoordinates : HedgePrivateCoordinates S)
    (fits : hedgePrivateCoordinatesFit outer target privateCoordinates = true)
    (child : Fin S.count) (outside : outer child = false) :
    privateCoordinates child = hedgeIndexOfValue S child (target child) := by
  have tested := (List.all_eq_true.mp fits) child (List.mem_finRange child)
  simp [outside] at tested
  exact tested

/-- All private-coordinate vectors that fit `target` outside `outer`. -/
def hedgePrivateSupportEnum (outer : NodeSet S) (target : S.Assignment) :
    List (HedgePrivateCoordinates S) :=
  (hedgePrivateCoordinateEnum S).filter
    (hedgePrivateCoordinatesFit outer target)

theorem hedgePrivateSupportEnum_complete (outer : NodeSet S)
    (target : S.Assignment)
    (privateCoordinates : HedgePrivateCoordinates S)
    (fits : hedgePrivateCoordinatesFit outer target privateCoordinates = true) :
    privateCoordinates ∈ hedgePrivateSupportEnum outer target := by
  exact List.mem_filter.mpr
    ⟨hedgePrivateCoordinateEnum_complete S privateCoordinates, fits⟩

theorem hedgePrivateSupportEnum_nodup (outer : NodeSet S)
    (target : S.Assignment) :
    (hedgePrivateSupportEnum outer target).Nodup :=
  List.Sublist.nodup List.filter_sublist
    (hedgePrivateCoordinateEnum_nodup S)

/--
Full latent support associated with an arbitrary executable pair-root test.
The Cartesian source keeps the common private multiplicity visible; mapping
by coordinate reassembly returns actual assignments of `hedgeLatentExtension`.
-/
def hedgeCoordinateSupportLatents (G : ObservedGraph S)
    (outer : NodeSet S) (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool) :
    List (hedgeLatentExtension G).Assignment :=
  (Probability.ConstructivePermutation.pairList
      ((hedgePairBitEnum G).filter pairTest)
      (hedgePrivateSupportEnum outer target)).map
    (hedgeLatentOfCoordinatePair G)

/-- Coordinate support contains no duplicate latent assignment. -/
theorem hedgeCoordinateSupportLatents_nodup (G : ObservedGraph S)
    (outer : NodeSet S) (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool) :
    (hedgeCoordinateSupportLatents G outer target pairTest).Nodup := by
  unfold hedgeCoordinateSupportLatents
  apply Probability.ConstructivePermutation.nodup_map_of_injective_on
      (hedgeLatentOfCoordinatePair G) _
  · intro left _leftMem right _rightMem equal
    exact hedgeLatentOfCoordinatePair_injective G equal
  · exact Probability.ConstructivePermutation.pairList_nodup _ _
      (List.Sublist.nodup List.filter_sublist (hedgePairBitEnum_nodup G))
      (hedgePrivateSupportEnum_nodup outer target)

/--
Membership in coordinate support is exactly the conjunction of the pair-root
test and the outside-private constraint recovered from the assignment.
-/
theorem hedgeCoordinateSupportLatents_mem_iff (G : ObservedGraph S)
    (outer : NodeSet S) (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool)
    (u : (hedgeLatentExtension G).Assignment) :
    u ∈ hedgeCoordinateSupportLatents G outer target pairTest ↔
      pairTest (hedgePairBitsOf G u) = true ∧
        hedgePrivateCoordinatesFit outer target
          (hedgePrivateCoordinatesOf G u) = true := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨coordinates, coordinatesMem, equal⟩
    have parts :=
      (Probability.ConstructivePermutation.mem_pairList
        coordinates.1 coordinates.2
        ((hedgePairBitEnum G).filter pairTest)
        (hedgePrivateSupportEnum outer target)).mp coordinatesMem
    have pairParts := List.mem_filter.mp parts.1
    have privateParts := List.mem_filter.mp parts.2
    rw [← equal]
    constructor
    · simpa [hedgeLatentOfCoordinatePair,
        hedgePairBitsOf_latentOfCoordinates] using pairParts.2
    · simpa [hedgeLatentOfCoordinatePair,
        hedgePrivateCoordinatesOf_latentOfCoordinates] using privateParts.2
  · intro parts
    apply List.mem_map.mpr
    refine ⟨(hedgePairBitsOf G u, hedgePrivateCoordinatesOf G u), ?_, ?_⟩
    · apply (Probability.ConstructivePermutation.mem_pairList
        (hedgePairBitsOf G u) (hedgePrivateCoordinatesOf G u)
        ((hedgePairBitEnum G).filter pairTest)
        (hedgePrivateSupportEnum outer target)).mpr
      constructor
      · exact List.mem_filter.mpr
          ⟨hedgePairBitEnum_complete G (hedgePairBitsOf G u), parts.1⟩
      · exact hedgePrivateSupportEnum_complete outer target _ parts.2
    · exact hedgeLatentOfCoordinates_recover G u

/--
The full support length is the pair-fiber length times the common number of
admissible private-coordinate vectors.  No closed cardinality formula for the
dependent private product is needed by the later comparison.
-/
theorem hedgeCoordinateSupportLatents_length (G : ObservedGraph S)
    (outer : NodeSet S) (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool) :
    (hedgeCoordinateSupportLatents G outer target pairTest).length =
      ((hedgePairBitEnum G).filter pairTest).length *
        (hedgePrivateSupportEnum outer target).length := by
  unfold hedgeCoordinateSupportLatents
  rw [List.length_map,
    Probability.ConstructivePermutation.pairList_length]

/-! ### Semantic support of the forest-parity models -/

/--
Boolean test that every selected node of `target` uses one of the two values
which encode parity.  A Boolean test is intentional: later empty-support
branches can be split constructively without invoking excluded middle on a
proposition.
-/
def hedgeParityTargetValid (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (target : S.Assignment) : Bool :=
  (NodeSet.members nodes).all fun child =>
    decide (target child = rich.first child) ||
      decide (target child = rich.second child)

theorem hedgeParityTargetValid_of (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (target : S.Assignment)
    (valid : ∀ child, nodes child = true →
      target child = rich.first child ∨
        target child = rich.second child) :
    hedgeParityTargetValid rich nodes target = true := by
  unfold hedgeParityTargetValid
  apply List.all_eq_true.mpr
  intro child member
  have inside := (NodeSet.mem_members_iff nodes child).mp member
  rcases valid child inside with first | second
  · simp [first]
  · simp [second]

theorem hedgeParityTargetValid_spec (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (target : S.Assignment)
    (valid : hedgeParityTargetValid rich nodes target = true)
    (child : Fin S.count) (inside : nodes child = true) :
    target child = rich.first child ∨
      target child = rich.second child := by
  have member := (NodeSet.mem_members_iff nodes child).mpr inside
  have tested := (List.all_eq_true.mp valid) child member
  simp only [Bool.or_eq_true, decide_eq_true_eq] at tested
  exact tested

/-- A valid distinguished value is recovered from its encoded second-bit. -/
theorem hedgeParityValue_isSecond_of_valid
    (rich : ObservedSignature.ValueRich S) (child : Fin S.count)
    (value : S.Value child)
    (valid : value = rich.first child ∨ value = rich.second child) :
    hedgeParityValue rich child (hedgeIsSecond rich child value) = value := by
  rcases valid with first | second
  · subst value
    simp [hedgeIsSecond, hedgeParityValue, rich.different]
  · subst value
    simp [hedgeIsSecond, hedgeParityValue]

/-- Every output of a forest-parity circuit is valid on its selected nodes. -/
theorem hedgeForestParityModel_eval_valid
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (kept : ForestChild S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeParityTargetValid rich nodes
        ((hedgeForestParityModel G rich nodes kept).eval u) = true := by
  apply hedgeParityTargetValid_of
  intro child inside
  change
    (hedgeForestParityModel G rich nodes kept).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child = rich.first child ∨
      (hedgeForestParityModel G rich nodes kept).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child = rich.second child
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  change
    hedgeForestParityOutput G rich nodes kept child
        (fun parent _ =>
          (hedgeForestParityModel G rich nodes kept).evalNodeUnder
            (FiniteLatentSCM.noIntervention S) u parent)
        (fun latent _ => u latent) = rich.first child ∨
      hedgeForestParityOutput G rich nodes kept child
        (fun parent _ =>
          (hedgeForestParityModel G rich nodes kept).evalNodeUnder
            (FiniteLatentSCM.noIntervention S) u parent)
        (fun latent _ => u latent) = rich.second child
  rw [hedgeForestParityOutput, if_pos inside]
  generalize
    Bool.xor
      (hedgeXorPairBitsWithin G nodes child fun latent _ => u latent)
      (hedgeForestParentBitsFrom rich kept child fun parent _ =>
        (hedgeForestParityModel G rich nodes kept).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u parent) = bit
  cases bit with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

/--
Outside the selected forest, the private coordinate is exactly the index of
the observed output.  Selected private coordinates remain unrestricted.
-/
theorem hedgeForestParityModel_privateCoordinatesFit_eval
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (kept : ForestChild S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgePrivateCoordinatesFit nodes
        ((hedgeForestParityModel G rich nodes kept).eval u)
        (hedgePrivateCoordinatesOf G u) = true := by
  apply hedgePrivateCoordinatesFit_of
  intro child outside
  change hedgePrivateIndex G child (fun root _ => u root) =
    hedgeIndexOfValue S child
      ((hedgeForestParityModel G rich nodes kept).eval u child)
  have outputEq :
      (hedgeForestParityModel G rich nodes kept).eval u child =
        hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun root _ => u root)) := by
    change
      (hedgeForestParityModel G rich nodes kept).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child = _
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    simp [hedgeForestParityModel, hedgeForestParityOutput, outside]
  have indexed := congrArg (hedgeIndexOfValue S child) outputEq
  rw [hedgeIndexOf_decode] at indexed
  exact indexed.symm

/--
One node of a forest-parity circuit evaluates to a valid target whenever the
recovered pair bits realize the target incidence and the outside private
coordinates fit.  Recursive calls are only made at directed parents, whose
indices are earlier in the observed signature.
-/
theorem hedgeForestParityModel_evalNode_eq_of_support
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (kept : ForestChild S)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich nodes target = true)
    (u : (hedgeLatentExtension G).Assignment)
    (realizes : hedgePairBitsRealizes G nodes
      (hedgeForestRequiredIncidence rich kept target)
      (hedgePairBitsOf G u) = true)
    (privateFits : hedgePrivateCoordinatesFit nodes target
      (hedgePrivateCoordinatesOf G u) = true)
    (child : Fin S.count) :
    (hedgeForestParityModel G rich nodes kept).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child = target child := by
  cases inside : nodes child
  · rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    simp only [hedgeForestParityModel, hedgeForestParityOutput, inside,
      Bool.false_eq_true, ↓reduceIte]
    have privateAt := hedgePrivateCoordinatesFit_spec nodes target
      (hedgePrivateCoordinatesOf G u) privateFits child inside
    change hedgePrivateIndex G child (fun root _ => u root) =
      hedgeIndexOfValue S child (target child) at privateAt
    rw [privateAt, hedgePrivateDecode_index]
  · have incidence := hedgePairBitsRealizes_spec G nodes
      (hedgeForestRequiredIncidence rich kept target)
      (hedgePairBitsOf G u) realizes child inside
    have parents :
        hedgeForestParentBitsFrom rich kept child
            (fun parent _ =>
              (hedgeForestParityModel G rich nodes kept).evalNodeUnder
                (FiniteLatentSCM.noIntervention S) u parent) =
          hedgeForestParentBitsFrom rich kept child
            (fun parent _ => target parent) := by
      apply hedgeForestParentBitsFrom_congr rich child
      · intro _parent
        rfl
      · intro parent edge
        exact hedgeForestParityModel_evalNode_eq_of_support G rich nodes kept
          target valid u realizes privateFits parent
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    change
      hedgeForestParityOutput G rich nodes kept child
          (fun parent _ =>
            (hedgeForestParityModel G rich nodes kept).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u parent)
          (fun latent _ => u latent) = target child
    rw [hedgeForestParityOutput, if_pos inside]
    rw [hedgeXorPairBitsWithin_pairBitsOf, incidence, parents]
    unfold hedgeForestRequiredIncidence
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    exact hedgeParityValue_isSecond_of_valid rich child (target child)
      (hedgeParityTargetValid_spec rich nodes target valid child inside)
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

/-- Complete evaluation of a supported forest-parity latent assignment. -/
theorem hedgeForestParityModel_eval_eq_of_support
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (kept : ForestChild S)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich nodes target = true)
    (u : (hedgeLatentExtension G).Assignment)
    (realizes : hedgePairBitsRealizes G nodes
      (hedgeForestRequiredIncidence rich kept target)
      (hedgePairBitsOf G u) = true)
    (privateFits : hedgePrivateCoordinatesFit nodes target
      (hedgePrivateCoordinatesOf G u) = true) :
    (hedgeForestParityModel G rich nodes kept).eval u = target := by
  funext child
  exact hedgeForestParityModel_evalNode_eq_of_support G rich nodes kept target
    valid u realizes privateFits child

/--
For a valid target, evaluation by the ordinary forest-parity model is exactly
membership in the factored coordinate support.
-/
theorem hedgeForestParityModel_eval_mem_coordinateSupport_iff
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (kept : ForestChild S)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich nodes target = true)
    (u : (hedgeLatentExtension G).Assignment) :
    (hedgeForestParityModel G rich nodes kept).eval u = target ↔
      u ∈ hedgeCoordinateSupportLatents G nodes target
        (hedgePairBitsRealizes G nodes
          (hedgeForestRequiredIncidence rich kept target)) := by
  rw [hedgeCoordinateSupportLatents_mem_iff]
  constructor
  · intro evaluates
    subst target
    exact ⟨hedgeForestParityModel_pairBitsRealizes_eval
        G rich nodes kept u,
      hedgeForestParityModel_privateCoordinatesFit_eval
        G rich nodes kept u⟩
  · intro support
    exact hedgeForestParityModel_eval_eq_of_support G rich nodes kept target
      valid u support.1 support.2

/--
Incidence demanded by a target in the piecewise nested parity model.  Inner
vertices use the restricted forest equation; the remaining outer vertices
use the original large-forest equation.
-/
def hedgeNestedForestRequiredIncidence
    (rich : ObservedSignature.ValueRich S) (inner : NodeSet S)
    (outerKept innerKept : ForestChild S) (target : S.Assignment)
    (child : Fin S.count) : Bool :=
  if inner child then
    hedgeForestRequiredIncidence rich innerKept target child
  else
    hedgeForestRequiredIncidence rich outerKept target child

/--
Recovered pair bits of a nested-model output realize its complete piecewise
incidence target on the outer forest.
-/
theorem hedgeNestedForestParityModel_pairBitsRealizes_eval
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (outer inner : NodeSet S) (outerKept innerKept : ForestChild S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeNestedPairBitsRealizes G outer inner
        (hedgeNestedForestRequiredIncidence rich inner outerKept innerKept
          ((hedgeNestedForestParityModel G rich outer inner
            outerKept innerKept).eval u))
        (hedgePairBitsOf G u) = true := by
  apply hedgeNestedPairBitsRealizes_of
  intro child inOuter
  cases inInner : inner child
  · simp only [hedgeNestedXorPairBitsWithinFrom, inInner,
      hedgeNestedForestRequiredIncidence]
    rw [← hedgeXorPairBitsWithin_pairBitsOf G outer u child]
    have equation :
        hedgeIsSecond rich child
            ((hedgeNestedForestParityModel G rich outer inner
              outerKept innerKept).eval u child) =
          Bool.xor
            (hedgeXorPairBitsWithin G outer child
              (fun latent _ => u latent))
            (hedgeForestParentBitsFrom rich outerKept child
              (fun parent _ =>
                (hedgeNestedForestParityModel G rich outer inner
                  outerKept innerKept).eval u parent)) := by
      change hedgeIsSecond rich child
          ((hedgeNestedForestParityModel G rich outer inner
            outerKept innerKept).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u child) = _
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      change hedgeIsSecond rich child
          (if inner child then
            hedgeForestParityOutput G rich inner innerKept child _ _
          else
            hedgeForestParityOutput G rich outer outerKept child _ _) = _
      simp only [inInner, Bool.false_eq_true, ↓reduceIte]
      exact hedgeForestParityOutput_bit_of_mem G rich outer outerKept
        child _ _ inOuter
    unfold hedgeForestRequiredIncidence
    rw [equation]
    generalize hedgeXorPairBitsWithin G outer child
      (fun latent _ => u latent) = pair
    generalize hedgeForestParentBitsFrom rich outerKept child
      (fun parent _ =>
        (hedgeNestedForestParityModel G rich outer inner
          outerKept innerKept).eval u parent) = parents
    cases pair <;> cases parents <;> rfl
  · simp only [hedgeNestedXorPairBitsWithinFrom, inInner,
      hedgeNestedForestRequiredIncidence, ↓reduceIte]
    rw [← hedgeXorPairBitsWithin_pairBitsOf G inner u child]
    have equation :
        hedgeIsSecond rich child
            ((hedgeNestedForestParityModel G rich outer inner
              outerKept innerKept).eval u child) =
          Bool.xor
            (hedgeXorPairBitsWithin G inner child
              (fun latent _ => u latent))
            (hedgeForestParentBitsFrom rich innerKept child
              (fun parent _ =>
                (hedgeNestedForestParityModel G rich outer inner
                  outerKept innerKept).eval u parent)) := by
      change hedgeIsSecond rich child
          ((hedgeNestedForestParityModel G rich outer inner
            outerKept innerKept).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u child) = _
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      change hedgeIsSecond rich child
          (if inner child then
            hedgeForestParityOutput G rich inner innerKept child _ _
          else
            hedgeForestParityOutput G rich outer outerKept child _ _) = _
      rw [if_pos inInner]
      exact hedgeForestParityOutput_bit_of_mem G rich inner innerKept
        child _ _ inInner
    unfold hedgeForestRequiredIncidence
    rw [equation]
    generalize hedgeXorPairBitsWithin G inner child
      (fun latent _ => u latent) = pair
    generalize hedgeForestParentBitsFrom rich innerKept child
      (fun parent _ =>
        (hedgeNestedForestParityModel G rich outer inner
          outerKept innerKept).eval u parent) = parents
    cases pair <;> cases parents <;> rfl

/-- Every nested-model output is parity-valid on the complete outer forest. -/
theorem hedgeNestedForestParityModel_eval_valid
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (outer inner : NodeSet S) (outerKept innerKept : ForestChild S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeParityTargetValid rich outer
        ((hedgeNestedForestParityModel G rich outer inner
          outerKept innerKept).eval u) = true := by
  apply hedgeParityTargetValid_of
  intro child inOuter
  change
    (hedgeNestedForestParityModel G rich outer inner
        outerKept innerKept).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child = rich.first child ∨
      (hedgeNestedForestParityModel G rich outer inner
        outerKept innerKept).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child = rich.second child
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  change
    (if inner child then
      hedgeForestParityOutput G rich inner innerKept child _ _
    else
      hedgeForestParityOutput G rich outer outerKept child _ _) =
        rich.first child ∨
      (if inner child then
        hedgeForestParityOutput G rich inner innerKept child _ _
      else
        hedgeForestParityOutput G rich outer outerKept child _ _) =
          rich.second child
  cases inInner : inner child
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hedgeForestParityOutput, if_pos inOuter]
    change hedgeParityValue rich child
        (Bool.xor
          (hedgeXorPairBitsWithin G outer child (fun root _ => u root))
          (hedgeForestParentBitsFrom rich outerKept child
            (fun parent _ =>
              (hedgeNestedForestParityModel G rich outer inner
                outerKept innerKept).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent))) =
          rich.first child ∨
      hedgeParityValue rich child
        (Bool.xor
          (hedgeXorPairBitsWithin G outer child (fun root _ => u root))
          (hedgeForestParentBitsFrom rich outerKept child
            (fun parent _ =>
              (hedgeNestedForestParityModel G rich outer inner
                outerKept innerKept).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent))) =
          rich.second child
    generalize
      Bool.xor
        (hedgeXorPairBitsWithin G outer child fun root _ => u root)
        (hedgeForestParentBitsFrom rich outerKept child fun parent _ =>
          (hedgeNestedForestParityModel G rich outer inner
            outerKept innerKept).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u parent) = bit
    cases bit with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl
  · simp only [↓reduceIte]
    rw [hedgeForestParityOutput, if_pos inInner]
    change hedgeParityValue rich child
        (Bool.xor
          (hedgeXorPairBitsWithin G inner child (fun root _ => u root))
          (hedgeForestParentBitsFrom rich innerKept child
            (fun parent _ =>
              (hedgeNestedForestParityModel G rich outer inner
                outerKept innerKept).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent))) =
          rich.first child ∨
      hedgeParityValue rich child
        (Bool.xor
          (hedgeXorPairBitsWithin G inner child (fun root _ => u root))
          (hedgeForestParentBitsFrom rich innerKept child
            (fun parent _ =>
              (hedgeNestedForestParityModel G rich outer inner
                outerKept innerKept).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent))) =
          rich.second child
    generalize
      Bool.xor
        (hedgeXorPairBitsWithin G inner child fun root _ => u root)
        (hedgeForestParentBitsFrom rich innerKept child fun parent _ =>
          (hedgeNestedForestParityModel G rich outer inner
            outerKept innerKept).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u parent) = bit
    cases bit with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl

/-- Outside the outer forest, nested-model outputs are fixed by private noise. -/
theorem hedgeNestedForestParityModel_privateCoordinatesFit_eval
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (outer inner : NodeSet S) (outerKept innerKept : ForestChild S)
    (subset : NodeSet.Subset inner outer)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgePrivateCoordinatesFit outer
        ((hedgeNestedForestParityModel G rich outer inner
          outerKept innerKept).eval u)
        (hedgePrivateCoordinatesOf G u) = true := by
  apply hedgePrivateCoordinatesFit_of
  intro child outside
  have innerOutside : inner child = false := by
    cases inside : inner child
    · rfl
    · exact False.elim
        (Bool.false_ne_true (outside.symm.trans (subset child inside)))
  change hedgePrivateIndex G child (fun root _ => u root) =
    hedgeIndexOfValue S child
      ((hedgeNestedForestParityModel G rich outer inner
        outerKept innerKept).eval u child)
  have outputEq :
      (hedgeNestedForestParityModel G rich outer inner
          outerKept innerKept).eval u child =
        hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun root _ => u root)) := by
    change
      (hedgeNestedForestParityModel G rich outer inner
        outerKept innerKept).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child = _
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    change
      (if inner child then
        hedgeForestParityOutput G rich inner innerKept child _ _
      else
        hedgeForestParityOutput G rich outer outerKept child _ _) = _
    simp only [innerOutside, Bool.false_eq_true, ↓reduceIte]
    simp only [hedgeForestParityOutput, outside, Bool.false_eq_true,
      ↓reduceIte]
    rfl
  have indexed := congrArg (hedgeIndexOfValue S child) outputEq
  rw [hedgeIndexOf_decode] at indexed
  exact indexed.symm

/-- Recursive evaluation of one node from nested coordinate support. -/
theorem hedgeNestedForestParityModel_evalNode_eq_of_support
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (outer inner : NodeSet S) (outerKept innerKept : ForestChild S)
    (subset : NodeSet.Subset inner outer)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich outer target = true)
    (u : (hedgeLatentExtension G).Assignment)
    (realizes : hedgeNestedPairBitsRealizes G outer inner
      (hedgeNestedForestRequiredIncidence rich inner outerKept innerKept target)
      (hedgePairBitsOf G u) = true)
    (privateFits : hedgePrivateCoordinatesFit outer target
      (hedgePrivateCoordinatesOf G u) = true)
    (child : Fin S.count) :
    (hedgeNestedForestParityModel G rich outer inner
      outerKept innerKept).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child = target child := by
  cases inOuter : outer child
  · have inInner : inner child = false := by
      cases inside : inner child
      · rfl
      · exact False.elim
          (Bool.false_ne_true (inOuter.symm.trans (subset child inside)))
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    change
      (if inner child then
        hedgeForestParityOutput G rich inner innerKept child _ _
      else
        hedgeForestParityOutput G rich outer outerKept child _ _) = _
    simp only [inInner, Bool.false_eq_true, ↓reduceIte]
    simp only [hedgeForestParityOutput, inOuter, Bool.false_eq_true,
      ↓reduceIte]
    change hedgePrivateDecode S child
      (hedgePrivateIndex G child (fun root _ => u root)) = target child
    have privateAt := hedgePrivateCoordinatesFit_spec outer target
      (hedgePrivateCoordinatesOf G u) privateFits child inOuter
    change hedgePrivateIndex G child (fun root _ => u root) =
      hedgeIndexOfValue S child (target child) at privateAt
    rw [privateAt, hedgePrivateDecode_index]
  · have incidence := hedgeNestedPairBitsRealizes_spec G outer inner
      (hedgeNestedForestRequiredIncidence rich inner outerKept innerKept target)
      (hedgePairBitsOf G u) realizes child inOuter
    cases inInner : inner child
    · have parents :
          hedgeForestParentBitsFrom rich outerKept child
              (fun parent _ =>
                (hedgeNestedForestParityModel G rich outer inner
                  outerKept innerKept).evalNodeUnder
                    (FiniteLatentSCM.noIntervention S) u parent) =
            hedgeForestParentBitsFrom rich outerKept child
              (fun parent _ => target parent) := by
        apply hedgeForestParentBitsFrom_congr rich child
        · intro _parent
          rfl
        · intro parent edge
          exact hedgeNestedForestParityModel_evalNode_eq_of_support G rich
            outer inner outerKept innerKept subset target valid u realizes
            privateFits parent
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      change
        (if inner child then
          hedgeForestParityOutput G rich inner innerKept child _ _
        else
          hedgeForestParityOutput G rich outer outerKept child _ _) = _
      simp only [inInner, Bool.false_eq_true, ↓reduceIte]
      rw [hedgeForestParityOutput, if_pos inOuter]
      change hedgeParityValue rich child
        (Bool.xor
          (hedgeXorPairBitsWithin G outer child (fun root _ => u root))
          (hedgeForestParentBitsFrom rich outerKept child
            (fun parent _ =>
              (hedgeNestedForestParityModel G rich outer inner
                outerKept innerKept).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent))) = target child
      rw [hedgeXorPairBitsWithin_pairBitsOf]
      unfold hedgeNestedXorPairBitsWithinFrom at incidence
      rw [if_neg (by simp [inInner])] at incidence
      rw [incidence, parents]
      unfold hedgeNestedForestRequiredIncidence
      simp only [inInner, Bool.false_eq_true, ↓reduceIte]
      unfold hedgeForestRequiredIncidence
      rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      exact hedgeParityValue_isSecond_of_valid rich child (target child)
        (hedgeParityTargetValid_spec rich outer target valid child inOuter)
    · have parents :
          hedgeForestParentBitsFrom rich innerKept child
              (fun parent _ =>
                (hedgeNestedForestParityModel G rich outer inner
                  outerKept innerKept).evalNodeUnder
                    (FiniteLatentSCM.noIntervention S) u parent) =
            hedgeForestParentBitsFrom rich innerKept child
              (fun parent _ => target parent) := by
        apply hedgeForestParentBitsFrom_congr rich child
        · intro _parent
          rfl
        · intro parent edge
          exact hedgeNestedForestParityModel_evalNode_eq_of_support G rich
            outer inner outerKept innerKept subset target valid u realizes
            privateFits parent
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      change
        (if inner child then
          hedgeForestParityOutput G rich inner innerKept child _ _
        else
          hedgeForestParityOutput G rich outer outerKept child _ _) = _
      rw [if_pos inInner]
      rw [hedgeForestParityOutput, if_pos inInner]
      change hedgeParityValue rich child
        (Bool.xor
          (hedgeXorPairBitsWithin G inner child (fun root _ => u root))
          (hedgeForestParentBitsFrom rich innerKept child
            (fun parent _ =>
              (hedgeNestedForestParityModel G rich outer inner
                outerKept innerKept).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent))) = target child
      rw [hedgeXorPairBitsWithin_pairBitsOf]
      unfold hedgeNestedXorPairBitsWithinFrom at incidence
      rw [if_pos inInner] at incidence
      rw [incidence, parents]
      unfold hedgeNestedForestRequiredIncidence
      rw [if_pos inInner]
      unfold hedgeForestRequiredIncidence
      rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      exact hedgeParityValue_isSecond_of_valid rich child (target child)
        (hedgeParityTargetValid_spec rich outer target valid child inOuter)
termination_by child.val
decreasing_by
  all_goals exact S.directed_earlier edge

/-- Complete evaluation of a supported nested-parity latent assignment. -/
theorem hedgeNestedForestParityModel_eval_eq_of_support
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (outer inner : NodeSet S) (outerKept innerKept : ForestChild S)
    (subset : NodeSet.Subset inner outer)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich outer target = true)
    (u : (hedgeLatentExtension G).Assignment)
    (realizes : hedgeNestedPairBitsRealizes G outer inner
      (hedgeNestedForestRequiredIncidence rich inner outerKept innerKept target)
      (hedgePairBitsOf G u) = true)
    (privateFits : hedgePrivateCoordinatesFit outer target
      (hedgePrivateCoordinatesOf G u) = true) :
    (hedgeNestedForestParityModel G rich outer inner
      outerKept innerKept).eval u = target := by
  funext child
  exact hedgeNestedForestParityModel_evalNode_eq_of_support G rich outer inner
    outerKept innerKept subset target valid u realizes privateFits child

/-- Valid nested evaluation is exactly membership in its coordinate support. -/
theorem hedgeNestedForestParityModel_eval_mem_coordinateSupport_iff
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (outer inner : NodeSet S) (outerKept innerKept : ForestChild S)
    (subset : NodeSet.Subset inner outer)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich outer target = true)
    (u : (hedgeLatentExtension G).Assignment) :
    (hedgeNestedForestParityModel G rich outer inner
      outerKept innerKept).eval u = target ↔
      u ∈ hedgeCoordinateSupportLatents G outer target
        (hedgeNestedPairBitsRealizes G outer inner
          (hedgeNestedForestRequiredIncidence rich inner
            outerKept innerKept target)) := by
  rw [hedgeCoordinateSupportLatents_mem_iff]
  constructor
  · intro evaluates
    subst target
    exact ⟨hedgeNestedForestParityModel_pairBitsRealizes_eval G rich outer
        inner outerKept innerKept u,
      hedgeNestedForestParityModel_privateCoordinatesFit_eval G rich outer
        inner outerKept innerKept subset u⟩
  · intro support
    exact hedgeNestedForestParityModel_eval_eq_of_support G rich outer inner
      outerKept innerKept subset target valid u support.1 support.2

/--
Lift the ordinary/nested pair-root fiber equality to complete latent support.
Both sides use the identical private-coordinate list, so its dependent-product
multiplicity is a common right factor and no closed cardinality calculation is
required.
-/
theorem HedgeWitness.parityCoordinateSupport_length_eq_of_even
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (largeEven :
      (hedgeTrueVertices w.large
        (hedgeForestRequiredIncidence rich w.child target)).length % 2 = 0)
    (smallEven :
      (hedgeTrueVertices w.small
        (hedgeNestedForestRequiredIncidence rich w.small w.child
          (restrictChild w.small w.child) target)).length % 2 = 0) :
    (hedgeCoordinateSupportLatents G w.large target
        (hedgePairBitsRealizes G w.large
          (hedgeForestRequiredIncidence rich w.child target))).length =
      (hedgeCoordinateSupportLatents G w.large target
        (hedgeNestedPairBitsRealizes G w.large w.small
          (hedgeNestedForestRequiredIncidence rich w.small w.child
            (restrictChild w.small w.child) target))).length := by
  rw [hedgeCoordinateSupportLatents_length,
    hedgeCoordinateSupportLatents_length]
  rw [w.large_forest.component.pairBitRealizers_length_eq_nested
    G w.large w.small w.small_forest.component w.small_subset_large
    (hedgeForestRequiredIncidence rich w.child target)
    (hedgeNestedForestRequiredIncidence rich w.small w.child
      (restrictChild w.small w.child) target)
    largeEven smallEven]

/-! ### Parity compatibility of nested c-forests -/

/-- Contribution of one kept parent to one prospective child coordinate. -/
def hedgeForestParentEntry (rich : ObservedSignature.ValueRich S)
    (kept : ForestChild S) (target : S.Assignment)
    (child parent : Fin S.count) : Bool :=
  if _edge : S.directed parent child = true then
    if kept parent = some child then
      hedgeIsSecond rich parent (target parent)
    else
      false
  else
    false

/-- Rewrite the kept-parent fold as an XOR of explicit parent entries. -/
theorem hedgeForestParentBitsFrom_eq_entryFold
    (rich : ObservedSignature.ValueRich S) (kept : ForestChild S)
    (target : S.Assignment) (child : Fin S.count) :
    hedgeForestParentBitsFrom rich kept child (fun parent _ => target parent) =
      (List.finRange S.count).foldl
        (fun total parent => Bool.xor total
          (hedgeForestParentEntry rich kept target child parent)) false := by
  unfold hedgeForestParentBitsFrom hedgeForestParentEntry
  apply foldl_congr
  intro total parent
  if edge : S.directed parent child = true then
    if selected : kept parent = some child then
      simp [edge, selected]
    else
      simp [edge, selected]
  else
    simp [edge]

/-- Bit contributed by a selected non-root parent after transposing the folds. -/
def hedgeForestNonRootBit (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (kept : ForestChild S) (target : S.Assignment)
    (parent : Fin S.count) : Bool :=
  if nodes parent then
    match kept parent with
    | none => false
    | some _child => hedgeIsSecond rich parent (target parent)
  else
    false

/--
For a fixed parent, XORing its entries over all selected children returns its
observed bit exactly when it is a selected non-root.  A well-formed c-forest
gives one selected child and the corresponding directed edge.
-/
theorem CForest.fold_parentEntry
    {G : ObservedGraph S} {nodes roots : NodeSet S}
    {kept : ForestChild S} (forest : CForest G nodes roots kept)
    (rich : ObservedSignature.ValueRich S) (target : S.Assignment)
    (parent : Fin S.count) :
    (NodeSet.members nodes).foldl
        (fun total child => Bool.xor total
          (hedgeForestParentEntry rich kept target child parent)) false =
      hedgeForestNonRootBit rich nodes kept target parent := by
  cases parentInside : nodes parent
  · have parentNone := forest.child_off_set parent parentInside
    unfold hedgeForestNonRootBit
    rw [if_neg (by simp [parentInside])]
    exact foldl_unchanged _ false (NodeSet.members nodes) (fun total child => by
      simp [hedgeForestParentEntry, parentNone])
  · cases parentChild : kept parent with
    | none =>
        unfold hedgeForestNonRootBit
        rw [if_pos parentInside, parentChild]
        exact foldl_unchanged _ false (NodeSet.members nodes)
          (fun total child => by
            if edge : S.directed parent child = true then
              simp [hedgeForestParentEntry, edge, parentChild]
            else
              simp [hedgeForestParentEntry, edge])
    | some selectedChild =>
        have edgeData := forest.child_edge parent selectedChild parentChild
        have childMember : selectedChild ∈ NodeSet.members nodes :=
          (NodeSet.mem_members_iff nodes selectedChild).mpr edgeData.2.1
        have rowEq :
            (NodeSet.members nodes).foldl
                (fun total child => Bool.xor total
                  (hedgeForestParentEntry rich kept target child parent)) false =
              (NodeSet.members nodes).foldl
                (fun total child =>
                  if child = selectedChild then
                    Bool.xor total
                      (hedgeIsSecond rich parent (target parent))
                  else
                    total) false := by
          apply foldl_congr
          intro total child
          by_cases same : child = selectedChild
          · subst child
            simp [hedgeForestParentEntry, edgeData.2.2, parentChild]
          · if edge : S.directed parent child = true then
              have reverse : selectedChild ≠ child := fun equal => same equal.symm
              simp [hedgeForestParentEntry, edge, parentChild, same, reverse]
            else
              simp [hedgeForestParentEntry, edge, same]
        rw [rowEq, foldl_xor_bit_of_mem_nodup
          (NodeSet.members nodes) childMember (NodeSet.nodup_members nodes)]
        simp [hedgeForestNonRootBit, parentInside, parentChild]

/--
XORing all kept-parent parities by child equals XORing the observed bits of
all selected non-roots.  `foldl_xor_swap` performs the finite row/column
interchange; `fold_parentEntry` evaluates each resulting parent column.
-/
theorem CForest.nodeXor_parentBits
    {G : ObservedGraph S} {nodes roots : NodeSet S}
    {kept : ForestChild S} (forest : CForest G nodes roots kept)
    (rich : ObservedSignature.ValueRich S) (target : S.Assignment) :
    hedgeNodeXor nodes
        (fun child => hedgeForestParentBitsFrom rich kept child
          (fun parent _ => target parent)) =
      (List.finRange S.count).foldl
        (fun total parent => Bool.xor total
          (hedgeForestNonRootBit rich nodes kept target parent)) false := by
  unfold hedgeNodeXor
  have expanded := foldl_congr
    (fun total child => Bool.xor total
      (hedgeForestParentBitsFrom rich kept child
        (fun parent _ => target parent)))
    (fun total child => Bool.xor total
      ((List.finRange S.count).foldl
        (fun parentTotal parent => Bool.xor parentTotal
          (hedgeForestParentEntry rich kept target child parent)) false))
    false (NodeSet.members nodes) (fun total child => by
      change Bool.xor total _ = Bool.xor total _
      rw [hedgeForestParentBitsFrom_eq_entryFold])
  rw [expanded, foldl_xor_swap]
  apply foldl_congr
  intro total parent
  rw [forest.fold_parentEntry rich target parent]

/-- The selected non-root fold may equivalently be taken over set members. -/
theorem CForest.nodeXor_nonRootBits_members
    {G : ObservedGraph S} {nodes roots : NodeSet S}
    {kept : ForestChild S} (_forest : CForest G nodes roots kept)
    (rich : ObservedSignature.ValueRich S) (target : S.Assignment) :
    (List.finRange S.count).foldl
        (fun total parent => Bool.xor total
          (hedgeForestNonRootBit rich nodes kept target parent)) false =
      (NodeSet.members nodes).foldl
        (fun total parent => Bool.xor total
          (match kept parent with
          | none => false
          | some _child => hedgeIsSecond rich parent (target parent))) false := by
  unfold NodeSet.members NodeSet.enumerated
  rw [List.foldl_filter]
  apply foldl_congr
  intro total parent
  cases inside : nodes parent <;>
    simp [hedgeForestNonRootBit, inside]

/-- Root members are precisely selected vertices with no kept child. -/
theorem CForest.members_roots
    {G : ObservedGraph S} {nodes roots : NodeSet S}
    {kept : ForestChild S} (forest : CForest G nodes roots kept) :
    NodeSet.members roots =
      (NodeSet.members nodes).filter fun node => decide (kept node = none) := by
  unfold NodeSet.members NodeSet.enumerated
  rw [List.filter_filter]
  apply List.filter_congr
  intro node _member
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro root
    have parts := (forest.roots_exact node).mp root
    exact ⟨parts.2, parts.1⟩
  · intro parts
    exact (forest.roots_exact node).mpr ⟨parts.2, parts.1⟩

/--
The XOR of required incidence over a c-forest is the XOR of target bits at
its roots.  Every selected non-root bit occurs once directly and once through
its unique kept edge, hence cancels; root bits occur only directly.
-/
theorem CForest.nodeXor_requiredIncidence
    {G : ObservedGraph S} {nodes roots : NodeSet S}
    {kept : ForestChild S} (forest : CForest G nodes roots kept)
    (rich : ObservedSignature.ValueRich S) (target : S.Assignment) :
    hedgeNodeXor nodes (hedgeForestRequiredIncidence rich kept target) =
      hedgeNodeXor roots
        (fun node => hedgeIsSecond rich node (target node)) := by
  let observedBit : Fin S.count → Bool := fun node =>
    hedgeIsSecond rich node (target node)
  let parentBit : Fin S.count → Bool := fun child =>
    hedgeForestParentBitsFrom rich kept child (fun parent _ => target parent)
  have split :
      hedgeNodeXor nodes (hedgeForestRequiredIncidence rich kept target) =
        Bool.xor (hedgeNodeXor nodes observedBit)
          (hedgeNodeXor nodes parentBit) := by
    unfold hedgeNodeXor hedgeForestRequiredIncidence observedBit parentBit
    exact foldl_xor_pointwise _ _ (NodeSet.members nodes)
  rw [split, forest.nodeXor_parentBits rich target,
    forest.nodeXor_nonRootBits_members rich target]
  unfold hedgeNodeXor
  rw [← foldl_xor_pointwise]
  have pointwise :
      (NodeSet.members nodes).foldl
          (fun total node => Bool.xor total
            (Bool.xor (observedBit node)
              (match kept node with
              | none => false
              | some _child => observedBit node))) false =
        (NodeSet.members nodes).foldl
          (fun total node => Bool.xor total
            (if kept node = none then observedBit node else false)) false := by
    apply foldl_congr
    intro total node
    cases childEq : kept node with
    | none =>
        cases observedBit node <;> simp
    | some child =>
        cases observedBit node <;> rfl
  rw [pointwise]
  have filtered := List.foldl_filter
    (p := fun node : Fin S.count => decide (kept node = none))
    (f := fun total node => Bool.xor total (observedBit node))
    (l := NodeSet.members nodes) (init := false)
  have rootFold :
      (NodeSet.members nodes).foldl
          (fun total node => Bool.xor total
            (if kept node = none then observedBit node else false)) false =
        ((NodeSet.members nodes).filter
          fun node => decide (kept node = none)).foldl
            (fun total node => Bool.xor total (observedBit node)) false := by
    rw [filtered]
    apply foldl_congr
    intro total node
    by_cases root : kept node = none <;> simp [root]
  rw [rootFold, ← forest.members_roots]

/-!
### Structural-equation defects and the action boundary

The faithful large model satisfies its intended XOR equation at every free
large-forest vertex.  Intervened vertices need not satisfy that equation, so
the useful conserved quantity is the XOR of the *defects* between required
and actual latent incidence.  C-forest cancellation identifies total root
parity with total defect parity, and restriction to the query intervention
then removes every defect outside `F \cap X`.  This cleanly isolates the
remaining separation argument at the finite action boundary.
-/

/-- The local discrepancy between the bit required by a forest equation and
the bit supplied by the pair-root coordinates internal to `nodes`. -/
def hedgeForestEquationDefect (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (nodes : NodeSet S)
    (kept : ForestChild S) (target : S.Assignment)
    (pairBits : Fin (pairRootCount G) → Bool)
    (child : Fin S.count) : Bool :=
  Bool.xor (hedgeForestRequiredIncidence rich kept target child)
    (hedgeXorPairBitsWithinFrom G nodes child pairBits)

/-- Total output parity at the roots of a c-forest is exactly the XOR of its
local equation defects.  The actual incidence contribution disappears by
the finite handshaking identity, leaving only required incidence, which the
c-forest cancellation theorem moves to the roots. -/
theorem CForest.rootBits_eq_nodeXor_equationDefect
    {G : ObservedGraph S} {nodes roots : NodeSet S}
    {kept : ForestChild S} (forest : CForest G nodes roots kept)
    (rich : ObservedSignature.ValueRich S) (target : S.Assignment)
    (pairBits : Fin (pairRootCount G) → Bool) :
    hedgeNodeXor roots
        (fun node => hedgeIsSecond rich node (target node)) =
      hedgeNodeXor nodes
        (hedgeForestEquationDefect G rich nodes kept target pairBits) := by
  rw [← forest.nodeXor_requiredIncidence rich target]
  unfold hedgeForestEquationDefect hedgeNodeXor
  rw [foldl_xor_pointwise]
  have incidence := hedgeNodeXor_incidence G nodes pairBits
  unfold hedgeNodeXor at incidence
  rw [incidence]
  simp

/-- If a bit is false outside `selected`, restricting an XOR fold over
`nodes` to `nodes ∩ selected` does not change its value. -/
theorem hedgeNodeXor_eq_inter_of_false_right
    (nodes selected : NodeSet S) (bits : Fin S.count → Bool)
    (zeroOutside : forall node, nodes node = true → selected node = false →
      bits node = false) :
    hedgeNodeXor nodes bits =
      hedgeNodeXor (NodeSet.inter nodes selected) bits := by
  unfold hedgeNodeXor NodeSet.members NodeSet.enumerated
  rw [List.foldl_filter, List.foldl_filter]
  apply foldl_congr
  intro total node
  cases inside : nodes node with
  | false => simp [inside, NodeSet.inter]
  | true =>
      cases chosen : selected node with
      | true => simp [inside, chosen, NodeSet.inter]
      | false => simp [inside, chosen, NodeSet.inter,
          zeroOutside node inside chosen]

/-- At a free large-forest vertex, the faithful large model has no local
equation defect: its observed bit is precisely the XOR of its kept-parent
bits and its internal pair-root incidence. -/
theorem HedgeWitness.largeParityModel_equationDefect_of_free
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeLatentExtension G).Assignment)
    (child : Fin S.count) (selected : w.large child = true)
    (free : intervention child = none) :
    hedgeForestEquationDefect G rich w.large w.child
        (fun node => (w.largeParityModel rich).evalNodeUnder
          intervention u node)
        (hedgePairBitsOf G u) child = false := by
  have equation := w.largeParityModel_evalNodeUnder_bit rich intervention u
    child free selected
  have actualEq := hedgeXorPairBitsWithin_pairBitsOf G w.large u child
  unfold hedgeForestEquationDefect hedgeForestRequiredIncidence
  rw [equation, actualEq]
  generalize
    hedgeXorPairBitsWithinFrom G w.large child (hedgePairBitsOf G u) = pair
  generalize hedgeForestParentBitsFrom rich w.child child
    (fun parent _ =>
      (w.largeParityModel rich).evalNodeUnder intervention u parent) = parents
  cases pair <;> cases parents <;> rfl

/-- Under the query intervention, every large-model equation defect outside
the action is false.  Consequently the common-root parity is governed
exactly by defects on the finite boundary `F ∩ X`; no claim about the
boundary parity itself is hidden in this reduction. -/
theorem HedgeWitness.largeParityModel_rootParity_eq_actionDefects_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    let target : S.Assignment := fun node =>
      (w.largeParityModel rich).evalNodeUnder
        (hedgeDoSecond rich q.action) u node
    let defect := hedgeForestEquationDefect G rich w.large w.child target
      (hedgePairBitsOf G u)
    hedgeNodeXor w.roots
        (fun node => hedgeIsSecond rich node (target node)) =
      hedgeNodeXor (NodeSet.inter w.large q.action) defect := by
  dsimp only
  let target : S.Assignment := fun node =>
    (w.largeParityModel rich).evalNodeUnder
      (hedgeDoSecond rich q.action) u node
  let defect := hedgeForestEquationDefect G rich w.large w.child target
    (hedgePairBitsOf G u)
  rw [w.large_forest.rootBits_eq_nodeXor_equationDefect rich target
    (hedgePairBitsOf G u)]
  apply hedgeNodeXor_eq_inter_of_false_right
  intro node selected notAction
  exact w.largeParityModel_equationDefect_of_free rich
    (hedgeDoSecond rich q.action) u node selected
    (hedgeDoSecond_of_false rich q.action notAction)

/-!
### A constructive odd large-root assignment

It is not true that the large circuit has odd root parity for every latent
assignment.  Instead, connect the stored action seed to its common-forest
root inside the large bidirected component.  The resulting pair-root vector
has incidence at exactly those two endpoints.  Under `do(X = second)`, the
action endpoint is blocked while the root endpoint remains free.  Toggling
from the zero vector to this endpoint vector therefore flips exactly that
root's output and leaves every other root unchanged.  One of the two explicit
latent assignments must consequently have odd total root parity.

The endpoint vector is recovered by exhaustive finite search through
`evenTargetPairBits`; the component path is used only to prove that the
two-endpoint target is even.  Thus no proposition-level witness is eliminated
into data and no choice principle is needed.
-/

/-- The selected common root lies in the action-avoiding small forest and is
therefore not intervened upon. -/
theorem HedgeWitness.actionRoot_not_in_action
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    q.action w.actionRoot = false :=
  w.small_avoids_intervention w.actionRoot w.actionRoot_in_small

/-- The stored action seed and its selected common root are distinct because
the former is in the action and the latter is not. -/
theorem HedgeWitness.actionSeed_ne_actionRoot
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    w.actionSeed ≠ w.actionRoot := by
  intro equal
  have actionFalse := w.actionRoot_not_in_action
  rw [← equal, w.actionSeed_in_action] at actionFalse
  exact Bool.noConfusion actionFalse

/-- Incidence target with one bit at the action seed and one at the selected
common root.  XOR makes the definition robust while the distinctness theorem
shows that both endpoint coordinates are true. -/
def HedgeWitness.actionRootToggleTarget
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (node : Fin S.count) : Bool :=
  Bool.xor (decide (node = w.actionSeed))
    (decide (node = w.actionRoot))

/-- The two-endpoint target has even support inside the large c-component. -/
theorem HedgeWitness.actionRootToggleTarget_even
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    (hedgeTrueVertices w.large w.actionRootToggleTarget).length % 2 = 0 := by
  apply (foldl_xor_eq_false_iff_filter_even w.actionRootToggleTarget
    (NodeSet.members w.large)).mp
  exact foldl_xor_two_indicators (NodeSet.members w.large)
    w.actionSeed w.actionRoot
    ((NodeSet.mem_members_iff w.large w.actionSeed).mpr
      w.actionSeed_in_large)
    ((NodeSet.mem_members_iff w.large w.actionRoot).mpr
      w.actionRoot_in_large)
    (NodeSet.nodup_members w.large)

/-- First exhaustively enumerated pair-root vector whose large-forest
incidence is the action-seed/root endpoint target. -/
def HedgeWitness.actionRootTogglePairBits
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    Fin (pairRootCount G) → Bool :=
  w.large_forest.component.evenTargetPairBits G w.large
    w.actionRootToggleTarget w.actionRootToggleTarget_even

/-- The computed toggle vector realizes the requested two-endpoint incidence
at every vertex of the large forest. -/
theorem HedgeWitness.actionRootTogglePairBits_spec
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) :
    forall node, w.large node = true →
      hedgeXorPairBitsWithinFrom G w.large node
          w.actionRootTogglePairBits =
        w.actionRootToggleTarget node :=
  w.large_forest.component.evenTargetPairBits_spec G w.large
    w.actionRootToggleTarget w.actionRootToggleTarget_even

/-- Concrete latent assignment with every pair-root bit false.  The private
coordinates are filled by an existing full-support enumerator; they are
ignored at every selected vertex of the large parity circuit. -/
def HedgeWitness.largeParityBaselineLatent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (_w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    (hedgeLatentExtension G).Assignment :=
  hedgeSupportLatentWithPairs G rich NodeSet.empty
    (hedgeActionReference rich q.action) (hedgeZeroPairBits G)

/-- Companion latent assignment carrying the action-seed/root toggle vector
on its pair-root coordinates. -/
def HedgeWitness.largeParityToggleLatent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    (hedgeLatentExtension G).Assignment :=
  hedgeSupportLatentWithPairs G rich NodeSet.empty
    (hedgeActionReference rich q.action) w.actionRootTogglePairBits

/-- Pair-root projection of the baseline latent is the zero vector. -/
theorem HedgeWitness.pairBitsOf_largeParityBaselineLatent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    hedgePairBitsOf G (w.largeParityBaselineLatent rich) =
      hedgeZeroPairBits G :=
  hedgePairBitsOf_supportWithPairs G rich NodeSet.empty
    (hedgeActionReference rich q.action) (hedgeZeroPairBits G)

/-- Pair-root projection of the companion latent is the computed toggle
vector. -/
theorem HedgeWitness.pairBitsOf_largeParityToggleLatent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    hedgePairBitsOf G (w.largeParityToggleLatent rich) =
      w.actionRootTogglePairBits :=
  hedgePairBitsOf_supportWithPairs G rich NodeSet.empty
    (hedgeActionReference rich q.action) w.actionRootTogglePairBits

/-- Baseline and toggle executions have the same encoded output at every
large-forest vertex except the selected common root.  At the action seed the
intervention masks the changed incidence.  At every other free vertex the
incidence is unchanged, and recursive equality of kept-parent bits follows
the strict observed topological order. -/
theorem HedgeWitness.largeParityModel_bit_eq_of_ne_actionRoot
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (selected : w.large child = true)
    (notRoot : child ≠ w.actionRoot) :
    hedgeIsSecond rich child
        ((w.largeParityModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action)
          (w.largeParityBaselineLatent rich) child) =
      hedgeIsSecond rich child
        ((w.largeParityModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action)
          (w.largeParityToggleLatent rich) child) := by
  cases freeEq : hedgeDoSecond rich q.action child with
  | some value =>
      rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder
      simp [freeEq]
  | none =>
      have notSeed : child ≠ w.actionSeed := by
        intro equal
        subst child
        rw [hedgeDoSecond_of_true rich q.action w.actionSeed_in_action] at freeEq
        contradiction
      have baselineEq := w.largeParityModel_evalNodeUnder_bit rich
        (hedgeDoSecond rich q.action) (w.largeParityBaselineLatent rich)
        child freeEq selected
      have toggleEq := w.largeParityModel_evalNodeUnder_bit rich
        (hedgeDoSecond rich q.action) (w.largeParityToggleLatent rich)
        child freeEq selected
      rw [baselineEq, toggleEq,
        hedgeXorPairBitsWithin_pairBitsOf,
        hedgeXorPairBitsWithin_pairBitsOf,
        w.pairBitsOf_largeParityBaselineLatent rich,
        w.pairBitsOf_largeParityToggleLatent rich,
        hedgeXorPairBitsWithinFrom_zero,
        w.actionRootTogglePairBits_spec child selected]
      have targetFalse : w.actionRootToggleTarget child = false := by
        simp [HedgeWitness.actionRootToggleTarget, notSeed, notRoot]
      rw [targetFalse]
      simp only [Bool.false_xor]
      apply hedgeForestParentBitsFrom_congr_of_kept
      intro parent edge kept
      exact w.largeParityModel_bit_eq_of_ne_actionRoot rich parent
        (w.large_forest.child_edge parent child kept).1
        (fun equal => by
          subst parent
          rw [w.actionRoot_child_none] at kept
          contradiction)
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

/-- The companion pair-root vector flips the selected common root's encoded
output bit.  Its kept parents are unaffected by the preceding recursive
comparison, while its own incidence changes from zero to one. -/
theorem HedgeWitness.largeParityModel_actionRoot_bit_toggle
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    hedgeIsSecond rich w.actionRoot
        ((w.largeParityModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action)
          (w.largeParityToggleLatent rich) w.actionRoot) =
      !hedgeIsSecond rich w.actionRoot
        ((w.largeParityModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action)
          (w.largeParityBaselineLatent rich) w.actionRoot) := by
  have free := hedgeDoSecond_of_false rich q.action w.actionRoot_not_in_action
  have baselineEq := w.largeParityModel_evalNodeUnder_bit rich
    (hedgeDoSecond rich q.action) (w.largeParityBaselineLatent rich)
    w.actionRoot free w.actionRoot_in_large
  have toggleEq := w.largeParityModel_evalNodeUnder_bit rich
    (hedgeDoSecond rich q.action) (w.largeParityToggleLatent rich)
    w.actionRoot free w.actionRoot_in_large
  rw [baselineEq, toggleEq,
    hedgeXorPairBitsWithin_pairBitsOf,
    hedgeXorPairBitsWithin_pairBitsOf,
    w.pairBitsOf_largeParityBaselineLatent rich,
    w.pairBitsOf_largeParityToggleLatent rich,
    hedgeXorPairBitsWithinFrom_zero,
    w.actionRootTogglePairBits_spec w.actionRoot w.actionRoot_in_large]
  have targetTrue : w.actionRootToggleTarget w.actionRoot = true := by
    have rootNeSeed : w.actionRoot ≠ w.actionSeed :=
      fun equal => w.actionSeed_ne_actionRoot (Eq.symm equal)
    simp [HedgeWitness.actionRootToggleTarget, rootNeSeed]
  rw [targetTrue]
  have parentBitsEq :
      hedgeForestParentBitsFrom rich w.child w.actionRoot
          (fun parent _ =>
            (w.largeParityModel rich).evalNodeUnder
              (hedgeDoSecond rich q.action)
              (w.largeParityBaselineLatent rich) parent) =
        hedgeForestParentBitsFrom rich w.child w.actionRoot
          (fun parent _ =>
            (w.largeParityModel rich).evalNodeUnder
              (hedgeDoSecond rich q.action)
              (w.largeParityToggleLatent rich) parent) := by
    apply hedgeForestParentBitsFrom_congr_of_kept
    intro parent edge kept
    exact w.largeParityModel_bit_eq_of_ne_actionRoot rich parent
      (w.large_forest.child_edge parent w.actionRoot kept).1
      (fun equal => by
        subst parent
        rw [w.actionRoot_child_none] at kept
        contradiction)
  rw [parentBitsEq]
  generalize
    hedgeForestParentBitsFrom rich w.child w.actionRoot
      (fun parent _ =>
        (w.largeParityModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action)
          (w.largeParityToggleLatent rich) parent) = parents
  cases parents <;> rfl

/-- Toggling the endpoint vector complements total parity over all common
roots: the selected action root flips and every other root stays fixed. -/
theorem HedgeWitness.largeParityModel_rootParity_toggle
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    hedgeNodeXor w.roots (fun node =>
        hedgeIsSecond rich node
          ((w.largeParityModel rich).evalNodeUnder
            (hedgeDoSecond rich q.action)
            (w.largeParityToggleLatent rich) node)) =
      !hedgeNodeXor w.roots (fun node =>
        hedgeIsSecond rich node
          ((w.largeParityModel rich).evalNodeUnder
            (hedgeDoSecond rich q.action)
            (w.largeParityBaselineLatent rich) node)) := by
  let baseline := fun node =>
    hedgeIsSecond rich node
      ((w.largeParityModel rich).evalNodeUnder
        (hedgeDoSecond rich q.action)
        (w.largeParityBaselineLatent rich) node)
  let toggled := fun node =>
    hedgeIsSecond rich node
      ((w.largeParityModel rich).evalNodeUnder
        (hedgeDoSecond rich q.action)
        (w.largeParityToggleLatent rich) node)
  have pointwise : forall node, w.roots node = true →
      toggled node = Bool.xor (baseline node)
        (decide (node = w.actionRoot)) := by
    intro node selected
    by_cases equal : node = w.actionRoot
    · subst node
      simpa [baseline, toggled, Bool.xor_true] using
        w.largeParityModel_actionRoot_bit_toggle rich
    · have inLarge := (w.large_forest.roots_exact node).mp selected |>.1
      have same := w.largeParityModel_bit_eq_of_ne_actionRoot rich node
        inLarge equal
      simpa [baseline, toggled, equal] using same.symm
  unfold hedgeNodeXor
  have rewritten :
      (NodeSet.members w.roots).foldl
          (fun total node => Bool.xor total (toggled node)) false =
        (NodeSet.members w.roots).foldl
          (fun total node => Bool.xor total
            (Bool.xor (baseline node)
              (decide (node = w.actionRoot)))) false := by
    apply foldl_congr_of_mem
    intro total node member
    rw [pointwise node ((NodeSet.mem_members_iff w.roots node).mp member)]
  rw [rewritten, foldl_xor_pointwise,
    foldl_xor_indicator_of_mem_nodup (NodeSet.members w.roots)
      w.actionRoot
      ((NodeSet.mem_members_iff w.roots w.actionRoot).mpr
        w.actionRoot_in_roots)
      (NodeSet.nodup_members w.roots)]
  simp [baseline]

/-- There is a concrete latent assignment for which the large parity model
has odd total common-root parity under the query intervention.  The proof
case-splits only on the computable baseline Boolean: if it is already odd,
use it; otherwise use the explicit endpoint toggle. -/
theorem HedgeWitness.exists_largeParityModel_rootParity_true_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Exists fun u : (hedgeLatentExtension G).Assignment =>
      hedgeNodeXor w.roots (fun node =>
        hedgeIsSecond rich node
          ((w.largeParityModel rich).evalNodeUnder
            (hedgeDoSecond rich q.action) u node)) = true := by
  let baselineParity := hedgeNodeXor w.roots (fun node =>
    hedgeIsSecond rich node
      ((w.largeParityModel rich).evalNodeUnder
        (hedgeDoSecond rich q.action)
        (w.largeParityBaselineLatent rich) node))
  cases parityEq : baselineParity with
  | true =>
      exact ⟨w.largeParityBaselineLatent rich, parityEq⟩
  | false =>
      refine ⟨w.largeParityToggleLatent rich, ?_⟩
      rw [w.largeParityModel_rootParity_toggle rich]
      simpa [baselineParity] using
        congrArg (fun bit : Bool => !bit) parityEq

/-!
### Transporting the large endpoint toggle to outcome sinks

The root-parity witness above changes pair-root incidence at the action seed
and one common root.  In the combined flow, the action endpoint is masked by
the intervention while the root endpoint remains active.  To make that
statement global, first compare the two executions recursively at every
large-forest vertex that has not yet entered a readout route.  Incoming bits
at an intervened vertex then agree, so its *effective* local source is also
unchanged.  At free vertices the effective source is their pair incidence,
which changes only at the selected common root.  Conservation therefore
turns the same one-bit toggle into a complement of total outcome-sink parity.

All recursion follows strict directed topological order.  The final witness
case-splits only on a computed `Bool`, never on an arbitrary proposition.
-/

/-- Before the composed route reaches its readout portion, the baseline and
endpoint-toggle executions have identical encoded bits.  An intervened node
is fixed in both runs; a free node has unchanged incidence and recursively
unchanged incoming parents. -/
theorem HedgeWitness.largeOutcomeFlowModel_bit_eq_of_not_readout
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (inLarge : w.large child = true)
    (notReadout : w.rootReadoutNodes child = false) :
    hedgeIsSecond rich child
        ((w.largeOutcomeFlowModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action)
          (w.largeParityBaselineLatent rich) child) =
      hedgeIsSecond rich child
        ((w.largeOutcomeFlowModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action)
          (w.largeParityToggleLatent rich) child) := by
  have selected : w.largeOutcomeFlowNodes child = true := by
    simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union, inLarge]
  cases freeEq : hedgeDoSecond rich q.action child with
  | some value =>
      rw [FiniteLatentSCM.evalNodeUnder, FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder
      simp [freeEq]
  | none =>
      have notSeed : child ≠ w.actionSeed := by
        intro equal
        subst child
        rw [hedgeDoSecond_of_true rich q.action w.actionSeed_in_action] at freeEq
        contradiction
      have notRoot : child ≠ w.actionRoot := by
        intro equal
        subst child
        have rootReadout := w.root_in_rootReadoutNodes w.actionRoot
          w.actionRoot_in_roots
        rw [notReadout] at rootReadout
        contradiction
      have baselineEq := hedgeFlowReadoutModel_evalNodeUnder_bit rich
        w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
        w.largeOutcomeFlowSuccessor_wellFormed (w.largeParityModel rich)
        (hedgeForestIncidenceSource G w.large)
        (hedgeDoSecond rich q.action) (w.largeParityBaselineLatent rich)
        child selected freeEq
      have toggleEq := hedgeFlowReadoutModel_evalNodeUnder_bit rich
        w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
        w.largeOutcomeFlowSuccessor_wellFormed (w.largeParityModel rich)
        (hedgeForestIncidenceSource G w.large)
        (hedgeDoSecond rich q.action) (w.largeParityToggleLatent rich)
        child selected freeEq
      simp only [hedgeForestIncidenceSource, inLarge, if_true] at baselineEq toggleEq
      have baselineIncidence := hedgeXorPairBitsWithin_pairBitsOf
        G w.large (w.largeParityBaselineLatent rich) child
      have toggleIncidence := hedgeXorPairBitsWithin_pairBitsOf
        G w.large (w.largeParityToggleLatent rich) child
      unfold HedgeWitness.largeOutcomeFlowModel
      simp only [HedgeWitness.largeParityModel, hedgeForestParityModel] at baselineEq toggleEq ⊢
      rw [baselineEq, toggleEq,
        baselineIncidence, toggleIncidence,
        w.pairBitsOf_largeParityBaselineLatent rich,
        w.pairBitsOf_largeParityToggleLatent rich,
        hedgeXorPairBitsWithinFrom_zero,
        w.actionRootTogglePairBits_spec child inLarge]
      have targetFalse : w.actionRootToggleTarget child = false := by
        simp [HedgeWitness.actionRootToggleTarget, notSeed, notRoot]
      rw [targetFalse]
      simp only [Bool.false_xor]
      apply hedgeRoutingIncomingBits_congr_of_kept
      intro parent found
      have parentNotReadout :=
        w.largeOutcomeFlowSuccessor_parent_not_readout notReadout found
      have parentSelected :=
        (childWellFormed_edge w.largeOutcomeFlowNodes
          w.largeOutcomeFlowSuccessor
          w.largeOutcomeFlowSuccessor_wellFormed found).1
      have parentLarge : w.large parent = true := by
        cases parentInLarge : w.large parent with
        | true => rfl
        | false =>
            simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
              parentNotReadout, parentInLarge] at parentSelected
      exact w.largeOutcomeFlowModel_bit_eq_of_not_readout rich parent
        parentLarge parentNotReadout
termination_by child.val
decreasing_by
  exact S.directed_earlier
    (childWellFormed_edge w.largeOutcomeFlowNodes
      w.largeOutcomeFlowSuccessor
      w.largeOutcomeFlowSuccessor_wellFormed found).2.2

/-- The effective local-source vectors of the two large executions differ at
exactly `actionRoot`.  Action vertices themselves have the same forced bit
and the same incoming parity; free vertices expose the explicit two-endpoint
incidence toggle, whose action-seed endpoint cannot occur in the free case. -/
theorem HedgeWitness.largeOutcomeFlowModel_localSource_toggle
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (node : Fin S.count) (selected : w.largeOutcomeFlowNodes node = true) :
    let baselineBits := fun child => hedgeIsSecond rich child
      ((w.largeOutcomeFlowModel rich).evalNodeUnder
        (hedgeDoSecond rich q.action)
        (w.largeParityBaselineLatent rich) child)
    let toggleBits := fun child => hedgeIsSecond rich child
      ((w.largeOutcomeFlowModel rich).evalNodeUnder
        (hedgeDoSecond rich q.action)
        (w.largeParityToggleLatent rich) child)
    hedgeRoutingLocalSource w.largeOutcomeFlowSuccessor toggleBits node =
      Bool.xor
        (hedgeRoutingLocalSource w.largeOutcomeFlowSuccessor baselineBits node)
        (decide (node = w.actionRoot)) := by
  dsimp only
  let baselineBits := fun child => hedgeIsSecond rich child
    ((w.largeOutcomeFlowModel rich).evalNodeUnder
      (hedgeDoSecond rich q.action)
      (w.largeParityBaselineLatent rich) child)
  let toggleBits := fun child => hedgeIsSecond rich child
    ((w.largeOutcomeFlowModel rich).evalNodeUnder
      (hedgeDoSecond rich q.action)
      (w.largeParityToggleLatent rich) child)
  cases inAction : q.action node with
  | true =>
      have notReadout : w.rootReadoutNodes node = false := by
        cases readout : w.rootReadoutNodes node with
        | false => rfl
        | true =>
            have avoids := w.rootReadoutNodes_avoids_action node readout
            rw [inAction] at avoids
            contradiction
      have notRoot : node ≠ w.actionRoot := by
        intro equal
        subst node
        rw [w.actionRoot_not_in_action] at inAction
        contradiction
      have baselineBit : baselineBits node = true := by
        unfold baselineBits
        rw [FiniteLatentSCM.evalNodeUnder]
        unfold FiniteLatentSCM.equationUnder
        rw [hedgeDoSecond_of_true rich q.action inAction]
        exact hedgeIsSecond_second rich node
      have toggleBit : toggleBits node = true := by
        unfold toggleBits
        rw [FiniteLatentSCM.evalNodeUnder]
        unfold FiniteLatentSCM.equationUnder
        rw [hedgeDoSecond_of_true rich q.action inAction]
        exact hedgeIsSecond_second rich node
      have incomingEq :
          hedgeRoutingIncomingBits w.largeOutcomeFlowSuccessor
              baselineBits node =
            hedgeRoutingIncomingBits w.largeOutcomeFlowSuccessor
              toggleBits node := by
        apply hedgeRoutingIncomingBits_congr_of_kept
        intro parent found
        have parentNotReadout :=
          w.largeOutcomeFlowSuccessor_parent_not_readout notReadout found
        have parentSelected :=
          (childWellFormed_edge w.largeOutcomeFlowNodes
            w.largeOutcomeFlowSuccessor
            w.largeOutcomeFlowSuccessor_wellFormed found).1
        have parentLarge : w.large parent = true := by
          cases parentInLarge : w.large parent with
          | true => rfl
          | false =>
              simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
                parentNotReadout, parentInLarge] at parentSelected
        exact w.largeOutcomeFlowModel_bit_eq_of_not_readout rich parent
          parentLarge parentNotReadout
      unfold hedgeRoutingLocalSource
      change Bool.xor (toggleBits node)
          (hedgeRoutingIncomingBits w.largeOutcomeFlowSuccessor
            toggleBits node) =
        Bool.xor
          (Bool.xor (baselineBits node)
            (hedgeRoutingIncomingBits w.largeOutcomeFlowSuccessor
              baselineBits node))
          (decide (node = w.actionRoot))
      rw [baselineBit, toggleBit, incomingEq]
      simp [notRoot]
  | false =>
      have free := hedgeDoSecond_of_false rich q.action inAction
      rw [w.largeOutcomeFlowModel_localSource_of_free rich
          (w.largeParityBaselineLatent rich) node selected free,
        w.largeOutcomeFlowModel_localSource_of_free rich
          (w.largeParityToggleLatent rich) node selected free]
      cases inLarge : w.large node with
      | false =>
          have notRoot : node ≠ w.actionRoot := by
            intro equal
            subst node
            have rootInLarge := w.actionRoot_in_large
            rw [inLarge] at rootInLarge
            contradiction
          simp [notRoot]
      | true =>
          have notSeed : node ≠ w.actionSeed := by
            intro equal
            subst node
            rw [w.actionSeed_in_action] at inAction
            contradiction
          rw [hedgeXorPairBitsWithin_pairBitsOf,
            hedgeXorPairBitsWithin_pairBitsOf,
            w.pairBitsOf_largeParityBaselineLatent rich,
            w.pairBitsOf_largeParityToggleLatent rich,
            hedgeXorPairBitsWithinFrom_zero,
            w.actionRootTogglePairBits_spec node inLarge]
          unfold HedgeWitness.actionRootToggleTarget
          simp [notSeed]

/-- The endpoint toggle complements total parity at the combined flow's
query-outcome sinks.  Conservation moves the pointwise local-source toggle
to the sinks, and the finite node list contains `actionRoot` exactly once. -/
theorem HedgeWitness.largeOutcomeFlowModel_sinkParity_toggle
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    let sinks := keptSinks w.largeOutcomeFlowNodes
      w.largeOutcomeFlowSuccessor
    hedgeNodeXor sinks (fun node => hedgeIsSecond rich node
        ((w.largeOutcomeFlowModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action)
          (w.largeParityToggleLatent rich) node)) =
      !hedgeNodeXor sinks (fun node => hedgeIsSecond rich node
        ((w.largeOutcomeFlowModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action)
          (w.largeParityBaselineLatent rich) node)) := by
  dsimp only
  let baselineBits := fun node => hedgeIsSecond rich node
    ((w.largeOutcomeFlowModel rich).evalNodeUnder
      (hedgeDoSecond rich q.action)
      (w.largeParityBaselineLatent rich) node)
  let toggleBits := fun node => hedgeIsSecond rich node
    ((w.largeOutcomeFlowModel rich).evalNodeUnder
      (hedgeDoSecond rich q.action)
      (w.largeParityToggleLatent rich) node)
  rw [hedgeRoutingFlow_conservation_localSource w.largeOutcomeFlowNodes
      w.largeOutcomeFlowSuccessor
      w.largeOutcomeFlowSuccessor_wellFormed toggleBits,
    hedgeRoutingFlow_conservation_localSource w.largeOutcomeFlowNodes
      w.largeOutcomeFlowSuccessor
      w.largeOutcomeFlowSuccessor_wellFormed baselineBits]
  unfold hedgeNodeXor
  have rewritten :
      (NodeSet.members w.largeOutcomeFlowNodes).foldl
          (fun total node => Bool.xor total
            (hedgeRoutingLocalSource w.largeOutcomeFlowSuccessor
              toggleBits node)) false =
        (NodeSet.members w.largeOutcomeFlowNodes).foldl
          (fun total node => Bool.xor total
            (Bool.xor
              (hedgeRoutingLocalSource w.largeOutcomeFlowSuccessor
                baselineBits node)
              (decide (node = w.actionRoot)))) false := by
    apply foldl_congr_of_mem
    intro total node member
    rw [w.largeOutcomeFlowModel_localSource_toggle rich node
      ((NodeSet.mem_members_iff w.largeOutcomeFlowNodes node).mp member)]
  rw [rewritten, foldl_xor_pointwise,
    foldl_xor_indicator_of_mem_nodup
      (NodeSet.members w.largeOutcomeFlowNodes) w.actionRoot
      ((NodeSet.mem_members_iff w.largeOutcomeFlowNodes w.actionRoot).mpr
        (by simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
          w.actionRoot_in_large]))
      (NodeSet.nodup_members w.largeOutcomeFlowNodes)]
  simp [baselineBits]

/-- One of the two explicit latent assignments has odd combined sink parity
in the large model.  This is the outcome-level counterpart of the earlier
common-root witness and is again obtained by a computable Boolean split. -/
theorem HedgeWitness.exists_largeOutcomeFlowModel_sinkParity_true_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Exists fun u : (hedgeLatentExtension G).Assignment =>
      hedgeNodeXor
        (keptSinks w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor)
        (fun node => hedgeIsSecond rich node
          ((w.largeOutcomeFlowModel rich).evalNodeUnder
            (hedgeDoSecond rich q.action) u node)) = true := by
  let baselineParity := hedgeNodeXor
    (keptSinks w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor)
    (fun node => hedgeIsSecond rich node
      ((w.largeOutcomeFlowModel rich).evalNodeUnder
        (hedgeDoSecond rich q.action)
        (w.largeParityBaselineLatent rich) node))
  cases parityEq : baselineParity with
  | true => exact ⟨w.largeParityBaselineLatent rich, parityEq⟩
  | false =>
      refine ⟨w.largeParityToggleLatent rich, ?_⟩
      rw [w.largeOutcomeFlowModel_sinkParity_toggle rich]
      simpa [baselineParity] using
        congrArg (fun bit : Bool => !bit) parityEq

/-!
### Root parity of the action-free small forest

The all-root transport layer needs a source invariant from the two original
hedge circuits.  On the small side, the invariant is exact: every small-forest
node remains free under the query action.  Its structural equation therefore
recovers the actual internal pair-root incidence, whose total XOR is even;
c-forest cancellation moves that evenness to the common root set.
-/

/-- Whenever an intervention leaves every small-forest node free, the total
encoded output bit at the common hedge roots is false for every latent
assignment. -/
theorem HedgeWitness.smallParityModel_rootParity_of_free
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeLatentExtension G).Assignment)
    (free : forall child, w.small child = true →
      intervention child = none) :
    hedgeNodeXor w.roots (fun child =>
      hedgeIsSecond rich child
        ((w.smallParityModel rich).evalNodeUnder intervention u child)) =
      false := by
  let target : S.Assignment := fun child =>
    (w.smallParityModel rich).evalNodeUnder intervention u child
  let required :=
    hedgeForestRequiredIncidence rich (restrictChild w.small w.child) target
  let actual := fun child =>
    hedgeXorPairBitsWithinFrom G w.small child (hedgePairBitsOf G u)
  have requiredAt : forall child, w.small child = true →
      required child = actual child := by
    intro child selected
    have equation := w.smallParityModel_evalNodeUnder_bit rich intervention u
      child (free child selected) selected
    have actualEq := hedgeXorPairBitsWithin_pairBitsOf G w.small u child
    dsimp only [required, actual, hedgeForestRequiredIncidence, target]
    rw [equation, actualEq]
    generalize
      hedgeXorPairBitsWithinFrom G w.small child (hedgePairBitsOf G u) = pair
    generalize hedgeForestParentBitsFrom rich
      (restrictChild w.small w.child) child
      (fun parent _ =>
        (w.smallParityModel rich).evalNodeUnder intervention u parent) = parents
    cases pair <;> cases parents <;> rfl
  have requiredXor :
      hedgeNodeXor w.small required = hedgeNodeXor w.small actual := by
    unfold hedgeNodeXor
    apply foldl_congr_of_mem
    intro total child member
    rw [requiredAt child
      ((NodeSet.mem_members_iff w.small child).mp member)]
  have requiredFalse : hedgeNodeXor w.small required = false := by
    rw [requiredXor]
    exact hedgeNodeXor_incidence G w.small (hedgePairBitsOf G u)
  rw [← w.small_forest.nodeXor_requiredIncidence rich target]
  exact requiredFalse

/-- In particular, the action-avoiding small forest has even root parity
under the canonical intervention that sets all action vertices to their
distinguished second values. -/
theorem HedgeWitness.smallParityModel_rootParity_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeNodeXor w.roots (fun child =>
      hedgeIsSecond rich child
        ((w.smallParityModel rich).evalNodeUnder
          (hedgeDoSecond rich q.action) u child)) = false := by
  apply w.smallParityModel_rootParity_of_free rich
  intro child selected
  exact hedgeDoSecond_of_false rich q.action
    (w.small_avoids_intervention child selected)

/-!
### Separation at the common-root parity event

The preceding pointwise invariants already separate the two unsoftened
interventional laws on the event that the common roots have odd parity.  The
small model gives this event zero mass.  The large model gives it positive
mass because the explicit odd latent atom has unit prior numerator.  This is
the exact probabilistic separation that the remaining readout construction
must transport from the common roots to a query-outcome event.
-/

/-- Boolean event that the distinguished-value bits on `roots` have odd XOR
parity. -/
def hedgeRootParityEvent (rich : ObservedSignature.ValueRich S)
    (roots : NodeSet S) : Event S.Assignment :=
  fun assignment => hedgeNodeXor roots (fun node =>
    hedgeIsSecond rich node (assignment node))


/-- Root parity depends only on the coordinates selected by `roots`. -/
theorem hedgeRootParityEvent_local
    (rich : ObservedSignature.ValueRich S) (roots : NodeSet S) :
    EventDependsOnlyOn roots (hedgeRootParityEvent rich roots) := by
  intro left right agree
  unfold hedgeRootParityEvent hedgeNodeXor
  apply foldl_congr_of_mem
  intro total node member
  change Bool.xor total (hedgeIsSecond rich node (left node)) =
    Bool.xor total (hedgeIsSecond rich node (right node))
  rw [agree node ((NodeSet.mem_members_iff roots node).mp member)]

/-- Hard intervention assigning the distinguished second value to every
selected action vertex. -/
def hedgeDoSecondIntervention (rich : ObservedSignature.ValueRich S)
    (action : NodeSet S) : HardIntervention S where
  value := hedgeDoSecond rich action

/-- The support of `hedgeDoSecondIntervention` is exactly its action set. -/
theorem hedgeDoSecondIntervention_targets
    (rich : ObservedSignature.ValueRich S) (action : NodeSet S) :
    (hedgeDoSecondIntervention rich action).targets = action := by
  funext node
  cases selected : action node <;>
    simp [hedgeDoSecondIntervention, HardIntervention.targets,
      hedgeDoSecond, selected]

/-!
### Separation on the original query outcome

The two composed flows share the canonical root-readout sink set, and that
set lies inside `q.outcome`.  Odd parity on those sinks is therefore a local
event for an interventional query whose kernel is exactly the original `q`.
The small combined model misses the event for every latent assignment; one
of the two explicit large assignments hits it.  Equal product denominators
then turn positive-versus-zero event mass into genuine kernel separation.

This closes the *interventional separation* part of the general hedge leaf.
It deliberately does not assert observational equivalence or positivity of
the combined models; those are separate obligations below the final
`CounterexampleIn` package.
-/

/-- Odd parity of the distinguished-value bits at the common canonical
readout sinks.  These sinks are query outcomes, even though the event ignores
any additional coordinates in `q.outcome`. -/
def HedgeWitness.outcomeSinkParityEvent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Event S.Assignment :=
  hedgeRootParityEvent rich
    (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)

/-- Sink parity is local to the original outcome set.  Locality first holds
on the smaller sink set and is then weakened along the proved subset. -/
theorem HedgeWitness.outcomeSinkParityEvent_local
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    EventDependsOnlyOn q.outcome (w.outcomeSinkParityEvent rich) := by
  intro left right agree
  apply hedgeRootParityEvent_local rich
    (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor) left right
  intro node inSinks
  exact agree node (w.rootReadoutSinks_subset_outcome node inSinks)

/-- Local event query for sink parity under the hedge's original action. -/
def HedgeWitness.outcomeSinkParityInterventionalQuery
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    InterventionalQuery S where
  intervention := hedgeDoSecondIntervention rich q.action
  outcomeNodes := q.outcome
  action_outcome_disjoint := by
    rw [hedgeDoSecondIntervention_targets rich q.action]
    exact q.action_outcome_disjoint
  event := w.outcomeSinkParityEvent rich
  event_local := w.outcomeSinkParityEvent_local rich

/-- Forgetting the fixed sink event recovers the original distributional
kernel query, including exactly the same action and outcome node sets. -/
theorem HedgeWitness.outcomeSinkParityInterventionalQuery_kernelQuery_eq
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    (w.outcomeSinkParityInterventionalQuery rich).kernelQuery = q := by
  cases q
  simp [HedgeWitness.outcomeSinkParityInterventionalQuery,
    InterventionalQuery.kernelQuery, hedgeDoSecondIntervention_targets]

/-- The fixed-event query evaluates as the ordinary interventional event
mass.  Hedge failure guarantees a nonempty action, so the query semantics
selects the interventional rather than observational branch. -/
theorem HedgeWitness.outcomeSinkParityInterventionalQuery_value
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (model : ExactModel S) :
    (w.outcomeSinkParityInterventionalQuery rich).value model =
      model.interventionalValue (hedgeDoSecond rich q.action)
        (w.outcomeSinkParityEvent rich) := by
  rcases w.large_meets_intervention with ⟨node, _inLarge, inAction⟩
  have actionNonempty : finAny S.count q.action = true :=
    finAny_eq_true_of q.action node inAction
  have targetNonempty :
      finAny S.count (hedgeDoSecondIntervention rich q.action).targets = true := by
    rw [hedgeDoSecondIntervention_targets rich q.action]
    exact actionNonempty
  unfold InterventionalQuery.value InterventionalQuery.distribution
  change
    (if finAny S.count (hedgeDoSecondIntervention rich q.action).targets then
        model.interventionalDist (hedgeDoSecond rich q.action)
      else model.observationalDist).probVal
        (w.outcomeSinkParityEvent rich) = _
  rw [if_pos targetNonempty]
  rfl

/-- Every small combined execution gives even parity on the common canonical
sink set.  The equality of sink sets converts the earlier small-flow theorem
to the event used by the original query. -/
theorem HedgeWitness.smallOutcomeFlowModel_outcomeSinkParityEvent_false
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    w.outcomeSinkParityEvent rich
        ((w.smallOutcomeFlowModel rich).evalUnder
          (hedgeDoSecond rich q.action) u) = false := by
  unfold HedgeWitness.outcomeSinkParityEvent hedgeRootParityEvent
  rw [← w.smallOutcomeFlowSinks_eq_rootReadoutSinks]
  exact w.smallOutcomeFlowModel_sinkParity_doSecond rich u

/-- The explicit large odd-sink witness hits the same canonical sink event. -/
theorem HedgeWitness.exists_largeOutcomeFlowModel_outcomeSinkParityEvent_true
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Exists fun u : (hedgeLatentExtension G).Assignment =>
      w.outcomeSinkParityEvent rich
        ((w.largeOutcomeFlowModel rich).evalUnder
          (hedgeDoSecond rich q.action) u) = true := by
  rcases w.exists_largeOutcomeFlowModel_sinkParity_true_doSecond rich with
    ⟨u, odd⟩
  refine ⟨u, ?_⟩
  unfold HedgeWitness.outcomeSinkParityEvent hedgeRootParityEvent
  rw [← w.largeOutcomeFlowSinks_eq_rootReadoutSinks]
  exact odd

/-- Both combined models retain definitionally the same finite product prior. -/
theorem HedgeWitness.outcomeFlowModel_prior_eq
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    (w.largeOutcomeFlowModel rich).prior =
      (w.smallOutcomeFlowModel rich).prior :=
  rfl

/-- The large sink-parity event has positive natural numerator.  The explicit
odd latent atom has unit uniform-product mass and embeds into the event. -/
theorem HedgeWitness.largeOutcomeFlowModel_outcomeSinkParityEventMass_pos
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    0 < FiniteProbRecord.eventMass
      (w.largeOutcomeFlowModel rich).prior.atoms
      (fun u => w.outcomeSinkParityEvent rich
        ((w.largeOutcomeFlowModel rich).evalUnder
          (hedgeDoSecond rich q.action) u)) := by
  rcases w.exists_largeOutcomeFlowModel_outcomeSinkParityEvent_true rich with
    ⟨u, odd⟩
  let sinkParity : Event ((hedgeLatentExtension G).Assignment) := fun v =>
    w.outcomeSinkParityEvent rich
      ((w.largeOutcomeFlowModel rich).evalUnder
        (hedgeDoSecond rich q.action) v)
  have singletonMass :
      FiniteProbRecord.eventMass
          (w.largeOutcomeFlowModel rich).prior.atoms
          (FiniteProbRecord.singletonEvent u) = 1 := by
    simpa [HedgeWitness.largeOutcomeFlowModel, hedgeFlowReadoutModel,
      HedgeWitness.largeParityModel, hedgeForestParityModel] using
      hedgePrior_eventMass_singleton G u
  have subset : forall v,
      FiniteProbRecord.singletonEvent u v = true → sinkParity v = true := by
    intro v member
    have equal : v = u := of_decide_eq_true (by
      simpa [FiniteProbRecord.singletonEvent] using member)
    simpa [sinkParity, equal] using odd
  have monotone := FiniteProbRecord.eventMass_mono
    (w.largeOutcomeFlowModel rich).prior.atoms
    (FiniteProbRecord.singletonEvent u) sinkParity subset
  change 0 < FiniteProbRecord.eventMass
    (w.largeOutcomeFlowModel rich).prior.atoms sinkParity
  exact Nat.lt_of_lt_of_le
    (Nat.lt_of_lt_of_eq Nat.zero_lt_one singletonMass.symm) monotone

/-- The corresponding small-model event numerator is zero pointwise. -/
theorem HedgeWitness.smallOutcomeFlowModel_outcomeSinkParityEventMass_zero
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    FiniteProbRecord.eventMass
      (w.smallOutcomeFlowModel rich).prior.atoms
      (fun u => w.outcomeSinkParityEvent rich
        ((w.smallOutcomeFlowModel rich).evalUnder
          (hedgeDoSecond rich q.action) u)) = 0 := by
  rw [FiniteProbRecord.eventMass_congr
    (w.smallOutcomeFlowModel rich).prior.atoms
    (fun u => w.outcomeSinkParityEvent rich
      ((w.smallOutcomeFlowModel rich).evalUnder
        (hedgeDoSecond rich q.action) u))
    (fun _ => false)
    (w.smallOutcomeFlowModel_outcomeSinkParityEvent_false rich)]
  exact FiniteProbRecord.eventMass_false _

/-- Positive large numerator versus zero small numerator, over equal positive
denominators, refutes equivalence of the two interventional event values. -/
theorem HedgeWitness.outcomeFlowModels_sinkParity_not_equiv_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Not (QProb.Equiv
      ((w.largeOutcomeFlowModel rich).interventionalValue
        (hedgeDoSecond rich q.action) (w.outcomeSinkParityEvent rich))
      ((w.smallOutcomeFlowModel rich).interventionalValue
        (hedgeDoSecond rich q.action) (w.outcomeSinkParityEvent rich))) := by
  intro equivalent
  have largeEq := FiniteLatentSCM.interventionalValue_eq
    (w.largeOutcomeFlowModel rich) (hedgeDoSecond rich q.action)
    (w.outcomeSinkParityEvent rich)
  have smallEq := FiniteLatentSCM.interventionalValue_eq
    (w.smallOutcomeFlowModel rich) (hedgeDoSecond rich q.action)
    (w.outcomeSinkParityEvent rich)
  have priorEquivalent : QProb.Equiv
      ((w.largeOutcomeFlowModel rich).prior.probVal (fun u =>
        w.outcomeSinkParityEvent rich
          ((w.largeOutcomeFlowModel rich).evalUnder
            (hedgeDoSecond rich q.action) u)))
      ((w.smallOutcomeFlowModel rich).prior.probVal (fun u =>
        w.outcomeSinkParityEvent rich
          ((w.smallOutcomeFlowModel rich).evalUnder
            (hedgeDoSecond rich q.action) u))) :=
    QProb.equiv_trans (QProb.equiv_symm largeEq)
      (QProb.equiv_trans equivalent smallEq)
  have massEqual :
      FiniteProbRecord.eventMass
          (w.largeOutcomeFlowModel rich).prior.atoms
          (fun u => w.outcomeSinkParityEvent rich
            ((w.largeOutcomeFlowModel rich).evalUnder
              (hedgeDoSecond rich q.action) u)) =
        FiniteProbRecord.eventMass
          (w.smallOutcomeFlowModel rich).prior.atoms
          (fun u => w.outcomeSinkParityEvent rich
            ((w.smallOutcomeFlowModel rich).evalUnder
              (hedgeDoSecond rich q.action) u)) := by
    have multiplied :
        FiniteProbRecord.eventMass
            (w.largeOutcomeFlowModel rich).prior.atoms
            (fun u => w.outcomeSinkParityEvent rich
              ((w.largeOutcomeFlowModel rich).evalUnder
                (hedgeDoSecond rich q.action) u)) *
          (w.smallOutcomeFlowModel rich).prior.den =
        FiniteProbRecord.eventMass
            (w.smallOutcomeFlowModel rich).prior.atoms
            (fun u => w.outcomeSinkParityEvent rich
              ((w.smallOutcomeFlowModel rich).evalUnder
                (hedgeDoSecond rich q.action) u)) *
          (w.largeOutcomeFlowModel rich).prior.den := by
      simpa [QProb.Equiv, FiniteProbRecord.probVal] using priorEquivalent
    have sameDenominator :
        (w.largeOutcomeFlowModel rich).prior.den =
          (w.smallOutcomeFlowModel rich).prior.den := by
      rw [w.outcomeFlowModel_prior_eq rich]
    rw [sameDenominator] at multiplied
    exact Nat.eq_of_mul_eq_mul_right
      (w.smallOutcomeFlowModel rich).prior.den_pos multiplied
  rw [w.smallOutcomeFlowModel_outcomeSinkParityEventMass_zero rich] at massEqual
  have positive :=
    w.largeOutcomeFlowModel_outcomeSinkParityEventMass_pos rich
  exact Nat.not_lt_zero 0 (massEqual ▸ positive)

/-- The packaged local event query inherits the sink-parity separation. -/
theorem HedgeWitness.outcomeSinkParityInterventionalQuery_not_equiv
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Not (QProb.Equiv
      ((w.outcomeSinkParityInterventionalQuery rich).value
        (w.largeOutcomeFlowModel rich))
      ((w.outcomeSinkParityInterventionalQuery rich).value
        (w.smallOutcomeFlowModel rich))) := by
  simpa [w.outcomeSinkParityInterventionalQuery_value rich] using
    w.outcomeFlowModels_sinkParity_not_equiv_doSecond rich

/-- The combined models disagree on the full original distributional kernel.
The fixed-event-to-kernel implication is constructive, and the final `simpa`
transports across the proved equality with `q` without rewriting the
query-indexed hedge witness itself. -/
theorem HedgeWitness.outcomeFlowModels_query_separated
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Not (q.ValueEquivalent (w.largeOutcomeFlowModel rich)
      (w.smallOutcomeFlowModel rich)) := by
  intro equivalent
  apply
    (w.outcomeSinkParityInterventionalQuery rich).not_kernelValueEquivalent_of_not_value
      (w.largeOutcomeFlowModel rich) (w.smallOutcomeFlowModel rich)
      (w.outcomeSinkParityInterventionalQuery_not_equiv rich)
  simpa only [w.outcomeSinkParityInterventionalQuery_kernelQuery_eq rich] using
    equivalent

/-- Event query that observes odd parity on the common roots under the
original hedge action.  Common roots belong to the small forest, so the
intervention and outcome selections are disjoint. -/
def HedgeWitness.rootParityInterventionalQuery
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    InterventionalQuery S where
  intervention := hedgeDoSecondIntervention rich q.action
  outcomeNodes := w.roots
  action_outcome_disjoint := by
    intro node inAction
    have inQueryAction : q.action node = true := by
      rw [← hedgeDoSecondIntervention_targets rich q.action]
      exact inAction
    cases inRoot : w.roots node with
    | false => rfl
    | true =>
        have inSmall := (w.small_forest.roots_exact node).mp inRoot |>.1
        have notAction := w.small_avoids_intervention node inSmall
        exact False.elim
          (Bool.false_ne_true (notAction.symm.trans inQueryAction))
  event := hedgeRootParityEvent rich w.roots
  event_local := hedgeRootParityEvent_local rich w.roots

/-- Distributional kernel underlying the common-root parity event query. -/
def HedgeWitness.rootParityQuery
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    JointKernelQuery S :=
  (w.rootParityInterventionalQuery rich).kernelQuery

/-- The event-query value unfolds to the parity models' ordinary
interventional value.  A hedge action is nonempty because its large forest
meets the action. -/
theorem HedgeWitness.rootParityInterventionalQuery_value
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (model : ExactModel S) :
    (w.rootParityInterventionalQuery rich).value model =
      model.interventionalValue (hedgeDoSecond rich q.action)
        (hedgeRootParityEvent rich w.roots) := by
  rcases w.large_meets_intervention with ⟨node, _inLarge, inAction⟩
  have actionNonempty : finAny S.count q.action = true :=
    finAny_eq_true_of q.action node inAction
  have targetNonempty :
      finAny S.count (hedgeDoSecondIntervention rich q.action).targets = true := by
    rw [hedgeDoSecondIntervention_targets rich q.action]
    exact actionNonempty
  unfold InterventionalQuery.value InterventionalQuery.distribution
  change
    (if finAny S.count (hedgeDoSecondIntervention rich q.action).targets then
        model.interventionalDist (hedgeDoSecond rich q.action)
      else model.observationalDist).probVal
        (hedgeRootParityEvent rich w.roots) = _
  rw [if_pos targetNonempty]
  rfl

/-- Every small-model latent assignment misses the odd common-root event
under the query intervention. -/
theorem HedgeWitness.smallParityModel_rootParityEvent_false_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeRootParityEvent rich w.roots
        ((w.smallParityModel rich).evalUnder
          (hedgeDoSecond rich q.action) u) = false :=
  w.smallParityModel_rootParity_doSecond rich u

/-- The odd common-root event has positive natural numerator in the large
model.  Monotonicity embeds the explicitly constructed odd singleton, whose
uniform product-prior mass is exactly one. -/
theorem HedgeWitness.largeParityModel_rootParityEventMass_pos_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    0 < FiniteProbRecord.eventMass
      (w.largeParityModel rich).prior.atoms
      (fun u => hedgeRootParityEvent rich w.roots
        ((w.largeParityModel rich).evalUnder
          (hedgeDoSecond rich q.action) u)) := by
  rcases w.exists_largeParityModel_rootParity_true_doSecond rich with
    ⟨u, odd⟩
  let rootParity : Event ((hedgeLatentExtension G).Assignment) := fun v =>
    hedgeRootParityEvent rich w.roots
      ((w.largeParityModel rich).evalUnder
        (hedgeDoSecond rich q.action) v)
  have singletonMass :
      FiniteProbRecord.eventMass
          (w.largeParityModel rich).prior.atoms
          (FiniteProbRecord.singletonEvent u) = 1 := by
    simpa [HedgeWitness.largeParityModel, hedgeForestParityModel] using
      hedgePrior_eventMass_singleton G u
  have subset : forall v,
      FiniteProbRecord.singletonEvent u v = true → rootParity v = true := by
    intro v member
    have equal : v = u := of_decide_eq_true (by
      simpa [FiniteProbRecord.singletonEvent] using member)
    simpa [rootParity, equal] using odd
  have monotone := FiniteProbRecord.eventMass_mono
    (w.largeParityModel rich).prior.atoms
    (FiniteProbRecord.singletonEvent u) rootParity subset
  change 0 < FiniteProbRecord.eventMass
    (w.largeParityModel rich).prior.atoms rootParity
  exact Nat.lt_of_lt_of_le
    (Nat.lt_of_lt_of_eq Nat.zero_lt_one singletonMass.symm) monotone

/-- The same odd common-root event has zero natural numerator in the small
model because its pointwise root parity is always false. -/
theorem HedgeWitness.smallParityModel_rootParityEventMass_zero_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    FiniteProbRecord.eventMass
      (w.smallParityModel rich).prior.atoms
      (fun u => hedgeRootParityEvent rich w.roots
        ((w.smallParityModel rich).evalUnder
          (hedgeDoSecond rich q.action) u)) = 0 := by
  rw [FiniteProbRecord.eventMass_congr
    (w.smallParityModel rich).prior.atoms
    (fun u => hedgeRootParityEvent rich w.roots
      ((w.smallParityModel rich).evalUnder
        (hedgeDoSecond rich q.action) u))
    (fun _ => false)
    (w.smallParityModel_rootParityEvent_false_doSecond rich)]
  exact FiniteProbRecord.eventMass_false _

/-- The unsoftened large and small hedge models therefore disagree on the
odd common-root event under `do(X = second)`.  Their denominators are equal
definitionally; positive versus zero numerator rules out rational
equivalence. -/
theorem HedgeWitness.parityModels_rootParity_not_equiv_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Not (QProb.Equiv
      ((w.largeParityModel rich).interventionalValue
        (hedgeDoSecond rich q.action)
        (hedgeRootParityEvent rich w.roots))
      ((w.smallParityModel rich).interventionalValue
        (hedgeDoSecond rich q.action)
        (hedgeRootParityEvent rich w.roots))) := by
  intro equivalent
  have largeEq := FiniteLatentSCM.interventionalValue_eq
    (w.largeParityModel rich) (hedgeDoSecond rich q.action)
    (hedgeRootParityEvent rich w.roots)
  have smallEq := FiniteLatentSCM.interventionalValue_eq
    (w.smallParityModel rich) (hedgeDoSecond rich q.action)
    (hedgeRootParityEvent rich w.roots)
  have priorEquivalent : QProb.Equiv
      ((w.largeParityModel rich).prior.probVal (fun u =>
        hedgeRootParityEvent rich w.roots
          ((w.largeParityModel rich).evalUnder
            (hedgeDoSecond rich q.action) u)))
      ((w.smallParityModel rich).prior.probVal (fun u =>
        hedgeRootParityEvent rich w.roots
          ((w.smallParityModel rich).evalUnder
            (hedgeDoSecond rich q.action) u))) :=
    QProb.equiv_trans (QProb.equiv_symm largeEq)
      (QProb.equiv_trans equivalent smallEq)
  have massEqual :
      FiniteProbRecord.eventMass
          (w.largeParityModel rich).prior.atoms
          (fun u => hedgeRootParityEvent rich w.roots
            ((w.largeParityModel rich).evalUnder
              (hedgeDoSecond rich q.action) u)) =
        FiniteProbRecord.eventMass
          (w.smallParityModel rich).prior.atoms
          (fun u => hedgeRootParityEvent rich w.roots
            ((w.smallParityModel rich).evalUnder
              (hedgeDoSecond rich q.action) u)) := by
    have multiplied :
        FiniteProbRecord.eventMass
            (w.largeParityModel rich).prior.atoms
            (fun u => hedgeRootParityEvent rich w.roots
              ((w.largeParityModel rich).evalUnder
                (hedgeDoSecond rich q.action) u)) *
          (w.smallParityModel rich).prior.den =
        FiniteProbRecord.eventMass
            (w.smallParityModel rich).prior.atoms
            (fun u => hedgeRootParityEvent rich w.roots
              ((w.smallParityModel rich).evalUnder
                (hedgeDoSecond rich q.action) u)) *
          (w.largeParityModel rich).prior.den := by
      simpa [QProb.Equiv, FiniteProbRecord.probVal] using priorEquivalent
    have sameDenominator :
        (w.largeParityModel rich).prior.den =
          (w.smallParityModel rich).prior.den := by
      rw [w.parityModel_prior_eq rich]
    rw [sameDenominator] at multiplied
    exact Nat.eq_of_mul_eq_mul_right
      (w.smallParityModel rich).prior.den_pos multiplied
  rw [w.smallParityModel_rootParityEventMass_zero_doSecond rich] at massEqual
  have positive := w.largeParityModel_rootParityEventMass_pos_doSecond rich
  exact Nat.not_lt_zero 0 (massEqual ▸ positive)

/-- The packaged local event query inherits the same interventional
separation. -/
theorem HedgeWitness.rootParityInterventionalQuery_not_equiv
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Not (QProb.Equiv
      ((w.rootParityInterventionalQuery rich).value
        (w.largeParityModel rich))
      ((w.rootParityInterventionalQuery rich).value
        (w.smallParityModel rich))) := by
  simpa [w.rootParityInterventionalQuery_value rich] using
    w.parityModels_rootParity_not_equiv_doSecond rich

/-- The required-incidence evenness of a c-forest depends only on its roots. -/
theorem CForest.requiredIncidence_even_iff_rootBits_even
    {G : ObservedGraph S} {nodes roots : NodeSet S}
    {kept : ForestChild S} (forest : CForest G nodes roots kept)
    (rich : ObservedSignature.ValueRich S) (target : S.Assignment) :
    (hedgeTrueVertices nodes
      (hedgeForestRequiredIncidence rich kept target)).length % 2 = 0 ↔
      (hedgeTrueVertices roots
        (fun node => hedgeIsSecond rich node (target node))).length % 2 = 0 := by
  constructor
  · intro even
    have leftFalse :
        hedgeNodeXor nodes
            (hedgeForestRequiredIncidence rich kept target) = false :=
      (foldl_xor_eq_false_iff_filter_even
        (hedgeForestRequiredIncidence rich kept target)
        (NodeSet.members nodes)).mpr even
    have rightFalse :
        hedgeNodeXor roots
            (fun node => hedgeIsSecond rich node (target node)) = false := by
      rw [← forest.nodeXor_requiredIncidence rich target]
      exact leftFalse
    exact (foldl_xor_eq_false_iff_filter_even
      (fun node => hedgeIsSecond rich node (target node))
      (NodeSet.members roots)).mp rightFalse
  · intro even
    have rightFalse :
        hedgeNodeXor roots
            (fun node => hedgeIsSecond rich node (target node)) = false :=
      (foldl_xor_eq_false_iff_filter_even
        (fun node => hedgeIsSecond rich node (target node))
        (NodeSet.members roots)).mpr even
    have leftFalse :
        hedgeNodeXor nodes
            (hedgeForestRequiredIncidence rich kept target) = false := by
      rw [forest.nodeXor_requiredIncidence rich target]
      exact rightFalse
    exact (foldl_xor_eq_false_iff_filter_even
      (hedgeForestRequiredIncidence rich kept target)
      (NodeSet.members nodes)).mp leftFalse

/--
Large and small hedge forests have the same roots, so their required
incidence targets are even simultaneously.
-/
theorem HedgeWitness.largeRequiredEven_iff_smallRequiredEven
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (hedgeTrueVertices w.large
      (hedgeForestRequiredIncidence rich w.child target)).length % 2 = 0 ↔
      (hedgeTrueVertices w.small
        (hedgeNestedForestRequiredIncidence rich w.small w.child
          (restrictChild w.small w.child) target)).length % 2 = 0 := by
  have largeRoots := w.large_forest.requiredIncidence_even_iff_rootBits_even
    rich target
  have smallRoots := w.small_forest.requiredIncidence_even_iff_rootBits_even
    rich target
  have nestedEq :
      hedgeTrueVertices w.small
          (hedgeNestedForestRequiredIncidence rich w.small w.child
            (restrictChild w.small w.child) target) =
        hedgeTrueVertices w.small
          (hedgeForestRequiredIncidence rich
            (restrictChild w.small w.child) target) := by
    unfold hedgeTrueVertices
    apply List.filter_congr
    intro node member
    have inside := (NodeSet.mem_members_iff w.small node).mp member
    simp [hedgeNestedForestRequiredIncidence, inside]
  rw [nestedEq]
  exact largeRoots.trans smallRoots.symm

/-!
The preceding compatibility theorem removes the last parity premise from the
fiber comparison.  The even branch uses the explicit translations already
constructed above.  In the odd branch both fibers are empty: every incidence
vector generated by pair roots has even support.  The empty-fiber proofs
inspect the computed filtered lists directly, avoiding any classical
`list = []` characterization.
-/

/-- Any target realized by ordinary restricted pair-root incidence is even. -/
theorem hedgePairBitsRealizes_even
    (G : ObservedGraph S) (nodes : NodeSet S)
    (target : Fin S.count → Bool)
    (pairBits : Fin (pairRootCount G) → Bool)
    (realizes : hedgePairBitsRealizes G nodes target pairBits = true) :
    (hedgeTrueVertices nodes target).length % 2 = 0 := by
  let actual := fun node =>
    hedgeXorPairBitsWithinFrom G nodes node pairBits
  have agrees := hedgePairBitsRealizes_spec G nodes target pairBits realizes
  have trueVerticesEq :
      hedgeTrueVertices nodes target = hedgeTrueVertices nodes actual := by
    unfold hedgeTrueVertices
    apply List.filter_congr
    intro node member
    exact (agrees node
      ((NodeSet.mem_members_iff nodes node).mp member)).symm
  rw [trueVerticesEq]
  exact hedgeXorPairBitsWithinFrom_even G nodes pairBits

/-- Any nested target realized on `inner` has even inner support. -/
theorem hedgeNestedPairBitsRealizes_inner_even
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (subset : NodeSet.Subset inner outer)
    (target : Fin S.count → Bool)
    (pairBits : Fin (pairRootCount G) → Bool)
    (realizes :
      hedgeNestedPairBitsRealizes G outer inner target pairBits = true) :
    (hedgeTrueVertices inner target).length % 2 = 0 := by
  let actual := fun node =>
    hedgeXorPairBitsWithinFrom G inner node pairBits
  have agrees := hedgeNestedPairBitsRealizes_spec G outer inner target pairBits
    realizes
  have trueVerticesEq :
      hedgeTrueVertices inner target = hedgeTrueVertices inner actual := by
    unfold hedgeTrueVertices
    apply List.filter_congr
    intro node member
    have inside := (NodeSet.mem_members_iff inner node).mp member
    have atNode := agrees node (subset node inside)
    simpa [hedgeNestedXorPairBitsWithinFrom, inside] using atNode.symm
  rw [trueVerticesEq]
  exact hedgeXorPairBitsWithinFrom_even G inner pairBits

/-- An odd ordinary target has no pair-root realizer in the enumeration. -/
theorem hedgePairBitRealizers_length_eq_zero_of_not_even
    (G : ObservedGraph S) (nodes : NodeSet S)
    (target : Fin S.count → Bool)
    (notEven : (hedgeTrueVertices nodes target).length % 2 ≠ 0) :
    ((hedgePairBitEnum G).filter
      (hedgePairBitsRealizes G nodes target)).length = 0 := by
  cases filtered : (hedgePairBitEnum G).filter
      (hedgePairBitsRealizes G nodes target) with
  | nil => rfl
  | cons pairBits tail =>
      have member :
          pairBits ∈ (hedgePairBitEnum G).filter
            (hedgePairBitsRealizes G nodes target) := by
        rw [filtered]
        exact List.mem_cons_self
      exact False.elim (notEven (hedgePairBitsRealizes_even G nodes target
        pairBits (List.mem_filter.mp member).2))

/-- An odd inner target has no nested pair-root realizer in the enumeration. -/
theorem hedgeNestedPairBitRealizers_length_eq_zero_of_not_even
    (G : ObservedGraph S) (outer inner : NodeSet S)
    (subset : NodeSet.Subset inner outer)
    (target : Fin S.count → Bool)
    (notEven : (hedgeTrueVertices inner target).length % 2 ≠ 0) :
    ((hedgePairBitEnum G).filter
      (hedgeNestedPairBitsRealizes G outer inner target)).length = 0 := by
  cases filtered : (hedgePairBitEnum G).filter
      (hedgeNestedPairBitsRealizes G outer inner target) with
  | nil => rfl
  | cons pairBits tail =>
      have member :
          pairBits ∈ (hedgePairBitEnum G).filter
            (hedgeNestedPairBitsRealizes G outer inner target) := by
        rw [filtered]
        exact List.mem_cons_self
      exact False.elim
        (notEven (hedgeNestedPairBitsRealizes_inner_even G outer inner subset
          target pairBits (List.mem_filter.mp member).2))

/--
The ordinary large-forest and nested small-forest pair-root fibers have equal
cardinality for every observed target, including the common empty odd case.
-/
theorem HedgeWitness.parityPairBitRealizers_length_eq
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    ((hedgePairBitEnum G).filter
      (hedgePairBitsRealizes G w.large
        (hedgeForestRequiredIncidence rich w.child target))).length =
      ((hedgePairBitEnum G).filter
        (hedgeNestedPairBitsRealizes G w.large w.small
          (hedgeNestedForestRequiredIncidence rich w.small w.child
            (restrictChild w.small w.child) target))).length := by
  by_cases largeEven :
      (hedgeTrueVertices w.large
        (hedgeForestRequiredIncidence rich w.child target)).length % 2 = 0
  · exact w.large_forest.component.pairBitRealizers_length_eq_nested
      G w.large w.small w.small_forest.component w.small_subset_large
      (hedgeForestRequiredIncidence rich w.child target)
      (hedgeNestedForestRequiredIncidence rich w.small w.child
        (restrictChild w.small w.child) target)
      largeEven ((w.largeRequiredEven_iff_smallRequiredEven rich target).mp
        largeEven)
  · have smallNotEven :
        (hedgeTrueVertices w.small
          (hedgeNestedForestRequiredIncidence rich w.small w.child
            (restrictChild w.small w.child) target)).length % 2 ≠ 0 :=
        fun smallEven => largeEven
          ((w.largeRequiredEven_iff_smallRequiredEven rich target).mpr
            smallEven)
    rw [hedgePairBitRealizers_length_eq_zero_of_not_even G w.large
      (hedgeForestRequiredIncidence rich w.child target) largeEven,
      hedgeNestedPairBitRealizers_length_eq_zero_of_not_even G w.large
        w.small w.small_subset_large
        (hedgeNestedForestRequiredIncidence rich w.small w.child
          (restrictChild w.small w.child) target) smallNotEven]

/--
The complete latent supports of the two parity models have equal cardinality
for every target.  Their private-coordinate factor is literally shared; the
preceding theorem supplies equality of the only model-dependent factor.
-/
theorem HedgeWitness.parityCoordinateSupport_length_eq
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (hedgeCoordinateSupportLatents G w.large target
      (hedgePairBitsRealizes G w.large
        (hedgeForestRequiredIncidence rich w.child target))).length =
      (hedgeCoordinateSupportLatents G w.large target
        (hedgeNestedPairBitsRealizes G w.large w.small
          (hedgeNestedForestRequiredIncidence rich w.small w.child
            (restrictChild w.small w.child) target))).length := by
  rw [hedgeCoordinateSupportLatents_length,
    hedgeCoordinateSupportLatents_length,
    w.parityPairBitRealizers_length_eq rich target]


end Causality
end Thesis
