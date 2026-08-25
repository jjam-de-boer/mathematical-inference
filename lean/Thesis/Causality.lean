import Thesis.Causality.Graph
import Thesis.Causality.Derivation
import Thesis.Causality.Model
import Thesis.Causality.Core
import Thesis.Causality.Identification
import Thesis.Causality.Reductions
import Thesis.Causality.CompactHiddenDAG
import Thesis.Causality.PairRoot
import Thesis.Causality.Semantics
import Thesis.Causality.Counterfactual
import Thesis.Causality.ModalDerivation
import Thesis.Causality.Modalities
import Thesis.Causality.Learning
import Thesis.Causality.Forgetting
import Thesis.Causality.Structural
import Thesis.Causality.EndpointSemantics
import Thesis.Causality.Multiworld
import Thesis.Causality.ExecutedMultiworld
import Thesis.Causality.ModalRealization
import Thesis.Causality.ModalCounterfactual
import Thesis.Causality.EndpointAgreement

/-!
Stable facade for the finite causal, modal, and counterfactual development.

Suggested reading order for a reader familiar with the thesis but new to the
source is `Graph`, `Derivation`, `Model`, `Core`, `Reductions`,
`CompactHiddenDAG`, `PairRoot`, `Semantics`, and `Identification`; then
`Modalities` and `Structural`; then
`Counterfactual`, `Multiworld`, and the modules below `ExecutedMultiworld`.
`ModalRealization` and `ModalCounterfactual` connect the executable edit paths
back to query semantics. The facade excludes the external completeness
interfaces; those begin in `Thesis.CausalTransport`.
-/
