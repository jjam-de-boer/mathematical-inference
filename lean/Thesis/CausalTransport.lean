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

`Correspondence` defines the explicit boundary to published results.
`FiniteSource` then gives an independently executable finite-table source
semantics and proves its preservation by the intrinsic causal semantics.
The remaining modules transport ordinary, modal, learning, hidden-DAG, and
counterfactual certificates across that boundary.  Thus importing this facade
does not assert an identification theorem as an axiom: users must supply the
relevant `Published...` package to invoke a completeness transport.
-/
