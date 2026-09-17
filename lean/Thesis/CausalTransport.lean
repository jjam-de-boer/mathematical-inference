import Thesis.CausalTransport.DSeparation
import Thesis.CausalTransport.DSeparationCorrectness
import Thesis.CausalTransport.Certificates
import Thesis.CausalTransport.Correspondence
import Thesis.CausalTransport.FiniteSource
import Thesis.CausalTransport.Soundness
import Thesis.CausalTransport.Completeness
import Thesis.CausalTransport.Counterfactual
import Thesis.CausalTransport.HiddenDAGModel
import Thesis.CausalTransport.HiddenDAG
import Thesis.CausalTransport.Construction
import Thesis.CausalTransport.Modal
import Thesis.CausalTransport.ModalRealization
import Thesis.CausalTransport.ConservativeLearningTransport
import Thesis.CausalTransport.ModalCounterfactual

/-!
Stable facade for external-theorem interfaces and their finite transports.

`Certificates` gives the shared certificate shapes, while `Correspondence`
states the graph-indexed external boundary. `FiniteSource` supplies an
independently executable finite-table semantics, proves its preservation by
the intrinsic semantics, and exposes its own published source interfaces.
`DSeparationCorrectness` proves the finite-search, shortest-walk, ancestry,
and moral-reachability foundations, and inhabits the algorithm–active-path
correspondence (`ObservedGraph.dSeparationCorrectness`).
`Soundness` proves the graph-independent probability primitives, reduces the
three graph-dependent leaves to denominator-free cylinder cross-products, and
supplies the source/target adapters needed by a constructive implementation.
`Completeness` hosts the executable ID engine's transport toward a
class-indexed `PublishedCompleteness` inhabitant on
`GraphModelClass.positive`.  The finite hedge extractor is complete for
enumerated selections: any candidate inside an ID failure whose Boolean
tests pass is found.  The remaining failure leaf is inhabiting those tests
for a concrete selection (the thinned forest is the intended one).
`Counterfactual` separately records the source-native multiworld boundary, and
`HiddenDAG` records the latent-projection boundary for a selected model family.
The remaining modules transport these ordinary, modal, learning, hidden-DAG,
and counterfactual certificates. Importing this facade introduces no
identification theorem as an axiom: a caller must supply the relevant
`Published...` package before applying a completeness transport.
-/
