import Thesis.CausalTransport.HiddenDAGRelayValues

namespace Thesis
namespace Causality

open Probability

/-!
# A canonical projected model realized by original-DAG relay equations

Every original observed node retains its original value domain and equation.
The equation's projected parent inputs and canonical root inputs are delivered
along actual hidden-internal paths.  Hidden nodes carry separate finite signal
vectors, forwarding each coordinate from the final declared predecessor of
its computed route.  They do not evaluate an observed ancestor's old equation
through a hard intervention.

Each canonical root's independent random channel is installed at its already
proved original-DAG source.  A relay node never receives a fresh copy of that
channel.  The noise factors and full prior are the actual nested independent
records from `HiddenDAGPlacedNoise`, not supplied semantic laws.

The constructor below gives a genuine finite hidden-DAG SCM for every
compatible canonical projected model.  No relay-readiness predicate or fixed
hidden-alphabet restriction is an additional premise.  Construction alone is
not the reverse completeness theorem.  `HiddenDAGEvaluation` now proves
unit-level evaluation preservation under every hard intervention.
`HiddenDAGNoiseLaw` relates the full grouped prior to the encoded original
prior, and `HiddenDAGProbability` proves complete event-probability and partial
kernel preservation.  Lifting counterexamples remains the next application.
-/

namespace HiddenDAGRelay

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- Read one observed signal from the actual final incoming path edge.
Observed predecessors supply only their own value; hidden predecessors
supply their carried signal vector. -/
def signalAlong (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count)
    (parents : projection.hiddenDAG.ParentValues (NodeValue model projection) node)
    (index : Fin S.count) {source : Fin projection.hiddenDAG.count}
    (path : projection.hiddenDAG.HiddenInternalPathData source node) : S.Value index :=
  readSignal model projection path.lastParent.val (parents _ path.lastParent.property) index

/-- Read a root coordinate from the final incoming edge of its actual relay
path.  Sound delivery uses a hidden source, hence a hidden predecessor;
the total reader also defines irrelevant off-route inputs. -/
def rootAlong (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count)
    (parents : projection.hiddenDAG.ParentValues (NodeValue model projection) node)
    (root : Fin model.latent.count) {source : Fin projection.hiddenDAG.count}
    (path : projection.hiddenDAG.HiddenInternalPathData source node) : model.latent.Value root :=
  readRoot model projection path.lastParent.val (parents _ path.lastParent.property) root

/-- A hidden node copies each projected observed ancestor's current signal
through a computed path.  No-path coordinates retain the signature default;
no zero-length projected path or unproved parent access is introduced. -/
def hiddenSignals (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count)
    (parents : projection.hiddenDAG.ParentValues (NodeValue model projection) node) : S.Assignment :=
  fun index =>
    match projection.hiddenDAG.hiddenInternalPath? (projection.hiddenDAG.observedNode index) node with
    | some path => signalAlong model projection node parents index path
    | none => S.defaultValue index

/-- Root channels are sampled only at their allocated source.  Everywhere
else they are copied through a hidden path from that source.  A private root
at an observed node is not exposed to hidden relays; only its own observed
recipient uses that noise coordinate. -/
def hiddenRoots (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (node : Fin P.hiddenDAG.count)
    (parents : P.hiddenDAG.ParentValues (NodeValue model P) node)
    (noise : HiddenDAGPlacedNoise.Row model) : model.latent.Assignment :=
  fun root =>
    match (model.hiddenDAGRootPlacements compatible root).source? with
    | none => defaultRoots model root
    | some source =>
        if source = node then (noise root).getD (defaultRoots model root)
        else if P.hiddenDAG.hidden source then
          match P.hiddenDAG.hiddenInternalPath? source node with
          | some path => rootAlong model P node parents root path
          | none => defaultRoots model root
        else defaultRoots model root

/-- Deliver the exact declared parent family of the original observed
equation.  Its signature edge is translated to internally computed full-DAG
path data; only the corresponding final declared parent value is read. -/
def observedParents (model : ExactModel S) (projection : FiniteLatentProjection S)
    (child : Fin S.count)
    (parents : projection.hiddenDAG.ParentValues (NodeValue model projection)
      (projection.hiddenDAG.observedNode child)) : S.ParentValues child :=
  fun parent edge => signalAlong model projection _ parents parent
    (projection.directedPathData parent child edge)

/-- Interpret one explicit delivery route.  Its source and dependent path
are kept together as parameters of this single total reader, so mechanism
construction and its later proof use the very same dependent match.  A local
route reads noise; a nonempty route reads the final declared parent value. -/
def rootAlongRoute (model : ExactModel S) (projection : FiniteLatentProjection S)
    (node : Fin projection.hiddenDAG.count)
    (parents : projection.hiddenDAG.ParentValues (NodeValue model projection) node)
    (noise : HiddenDAGPlacedNoise.Row model) (root : Fin model.latent.count)
    (source : Fin projection.hiddenDAG.count)
    (route : HiddenDAGInputRoute projection.hiddenDAG source node) : model.latent.Value root :=
  match route with
  | .localInput _same => (noise root).getD (defaultRoots model root)
  | .hiddenRelay path => rootAlong model projection node parents root path

/-- Private input noise is read locally; a shared input is read along its
allocated hidden relay.  The placement's delivery record certifies the source
and every declared incidence, including arbitrary canonical root numbering. -/
def observedRoots (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (child : Fin S.count)
    (parents : P.hiddenDAG.ParentValues (NodeValue model P) (P.hiddenDAG.observedNode child))
    (noise : HiddenDAGPlacedNoise.Row model) : model.latent.Inputs child :=
  fun root incident =>
    let delivery := (model.hiddenDAGRootPlacements compatible root).delivery child incident
    rootAlongRoute model P _ parents noise root delivery.source delivery.route

/-- The unchanged observed equation consumes only its proved reconstructed
parent and root inputs.  Incoming interventions will be handled by the full
SCM evaluator, not by reevaluating old factual observed equations here. -/
def observedMechanism (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (child : Fin S.count)
    (parents : P.hiddenDAG.ParentValues (NodeValue model P) (P.hiddenDAG.observedNode child))
    (noise : HiddenDAGPlacedNoise.Row model) : S.Value child :=
  model.mechanism child (observedParents model P child parents)
    (observedRoots model compatible child parents noise)

/-- The total full-DAG equation chooses the node's already computed observed
presentation.  Hidden nodes pack a relay payload; observed nodes keep their
original equation and are transported through the explicit observed embedding. -/
def mechanism (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (node : Fin P.hiddenDAG.count)
    (parents : P.hiddenDAG.ParentValues (NodeValue model P) node)
    (noise : HiddenDAGPlacedNoise.Row model) : NodeValue model P node :=
  match found : P.hiddenDAG.observedIndex node with
  | none =>
      (nodeValue_of_none model node found).mpr
        ⟨hiddenSignals model P node parents, hiddenRoots model compatible node parents noise⟩
  | some index =>
      (P.hiddenDAG.observedIndex_sound node index found) ▸
        (observedEquivalence model P index).backward
          (observedMechanism model compatible index
            ((P.hiddenDAG.observedIndex_sound node index found).symm ▸ parents) noise)

end HiddenDAGRelay

namespace FiniteLatentSCM

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- Realize a canonical projected model as an actual finite SCM over the
original hidden graph, with unrestricted finite hidden/noise vector sizes.
Its noise independence is proved by construction.  Evaluation and probability
equivalence to the input model are proved separately in `HiddenDAGEvaluation`
and `HiddenDAGProbability`, rather than supplied as constructor fields. -/
def toHiddenDAGSCM (model : ExactModel S) (compatible : Compatible model P.observedGraph) :
    FiniteHiddenDAGSCM S P where
  NodeValue := HiddenDAGRelay.NodeValue model P
  nodeEnumeration := HiddenDAGRelay.nodeEnumeration model P
  node_complete := HiddenDAGRelay.node_complete model P
  nodeDecidableEq := HiddenDAGRelay.nodeDecidableEq model P
  observedEquiv := HiddenDAGRelay.observedEquivalence model P
  observedIndex := P.hiddenDAG.observedIndex
  observedIndex_observed := P.hiddenDAG.observedIndex_observed
  observedIndex_sound := P.hiddenDAG.observedIndex_sound
  hidden_has_no_observed_index := P.hiddenDAG.observedIndex_hidden
  Noise := fun _ => HiddenDAGPlacedNoise.Row model
  noiseEnumeration := fun _ => HiddenDAGPlacedNoise.rowEnumeration model
  noise_complete := fun _ => HiddenDAGPlacedNoise.rowEnumeration_complete model
  noiseDecidableEq := fun _ => HiddenDAGPlacedNoise.rowDecidableEq model
  factor := HiddenDAGPlacedNoise.factor model compatible
  prior := HiddenDAGPlacedNoise.prior model compatible
  product_law := HiddenDAGPlacedNoise.product_law model compatible
  mechanism := HiddenDAGRelay.mechanism model compatible

end FiniteLatentSCM
end Causality
end Thesis
