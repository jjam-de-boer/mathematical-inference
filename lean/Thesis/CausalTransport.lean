import Thesis.CausalTransport.DSeparation
import Thesis.CausalTransport.Certificates
import Thesis.CausalTransport.Correspondence
import Thesis.CausalTransport.FiniteSource
import Thesis.CausalTransport.Counterfactual
import Thesis.CausalTransport.HiddenDAGModel
import Thesis.CausalTransport.HiddenDAG
import Thesis.CausalTransport.Construction
import Thesis.CausalTransport.Modal
import Thesis.CausalTransport.ModalRealization
import Thesis.CausalTransport.Learning
import Thesis.CausalTransport.ModalCounterfactual

/-!
Stable facade for external-theorem interfaces and their finite transports.

`Certificates` gives the shared certificate shapes, while `Correspondence`
states the graph-indexed external boundary. `FiniteSource` supplies an
independently executable finite-table semantics, proves its preservation by
the intrinsic semantics, and exposes its own published source interfaces.
`Counterfactual` separately records the source-native multiworld boundary, and
`HiddenDAG` records the latent-projection boundary for a selected model family.
The remaining modules transport these ordinary, modal, learning, hidden-DAG,
and counterfactual certificates. Importing this facade introduces no
identification theorem as an axiom: a caller must supply the relevant
`Published...` package before applying a completeness transport.
-/
