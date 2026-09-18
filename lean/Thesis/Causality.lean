import Thesis.Causality.Graph
import Thesis.Causality.Derivation
import Thesis.Causality.Model
import Thesis.Causality.HardIntervention
import Thesis.Causality.Identification
import Thesis.Causality.IdentificationSearch
import Thesis.Causality.IdentificationInduction
import Thesis.Causality.Reductions
import Thesis.Causality.CompactHiddenDAG
import Thesis.Causality.PairRoot
import Thesis.Causality.Semantics
import Thesis.Causality.ModalDerivation
import Thesis.Causality.Modalities
import Thesis.Causality.ConservativeLearning
import Thesis.Causality.Forgetting
import Thesis.Causality.Structural
import Thesis.Causality.EndpointSemantics
import Thesis.Causality.Counterfactual
import Thesis.Causality.Multiworld
import Thesis.Causality.ExecutedMultiworld
import Thesis.Causality.ModalRealization
import Thesis.Causality.ModalCounterfactual
import Thesis.Causality.EndpointAgreement
import Thesis.Causality.ModeTheory

/-!
Stable facade for the finite causal, modal, and counterfactual development.

Suggested reading order for a reader familiar with the thesis but new to the
source is `Graph`, `Derivation`, `Model`, `HardIntervention`, `Reductions`,
`CompactHiddenDAG`, `PairRoot`, `Semantics`, `Identification`, and
`IdentificationSearch`; `IdentificationInduction` supplies exact structural
traces for failed, successful, and unfinished arbitrary nested ID runs; then
`Modalities` and `Structural`; then
`Counterfactual`, `Multiworld`, and the modules below `ExecutedMultiworld`.
`ModalRealization` and `ModalCounterfactual` connect the executable edit paths
back to query semantics. `ModeTheory` names the existing one-shots as
morphisms and the edit paths as a 1-category of named states.
The facade excludes the external completeness
interfaces; those begin in `Thesis.CausalTransport`.
-/
