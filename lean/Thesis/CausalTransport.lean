import Thesis.CausalTransport.DSeparation
import Thesis.CausalTransport.DSeparationCorrectness
import Thesis.CausalTransport.Certificates
import Thesis.CausalTransport.Correspondence
import Thesis.CausalTransport.FiniteSource
import Thesis.CausalTransport.Soundness
import Thesis.CausalTransport.Completeness
import Thesis.CausalTransport.HedgeOutcomeFlow
import Thesis.CausalTransport.HedgePositive
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

`Certificates` defines the shared certificate shapes, while `Correspondence`
states the graph-indexed `PublishedSoundness` and `PublishedCompleteness`
boundaries.  These records make the remaining published-theorem obligations
explicit: importing this facade does not assume either theorem as an axiom.

`FiniteSource` supplies an independently executable finite-table semantics,
proves preservation into the intrinsic semantics, and exposes source-level
adapters.  `DSeparationCorrectness` connects the finite ancestry and moral
reachability searches to active-path separation.

`Soundness` develops the graph-independent probability algebra and the finite
latent factorization needed by the three do-calculus rules.  Its checked
adapters can assemble `PublishedSoundness` once the outstanding path-to-product
witnesses are supplied.  Several empty and one-sided cases are already
inhabited.  The general case must construct a residual cross-product witness;
the extra Boolean hypotheses accepted by `PathDoRulePartitionWitnesses.ofPath`
are not consequences of path d-separation in all configurations.

`Completeness` develops the executable ID side for the positive model class:
successful special cases compile to supported certificates, finite search
extracts hedge data from checked failures, and shared-switch hedge models
provide positive counterexamples for the covered queries.  `HedgePositive`
uses finite marginalization to reduce full-query separation to one suitable
outcome coordinate with a directed action parent.  A finite pivot assignment
removes both parent-uniqueness and odd-parity restrictions, without choosing
a family of pointwise equivalences.  A complete `PublishedCompleteness`
inhabitant still needs structural compilation of arbitrary successful traces
and a positive countermodel for an arbitrary hedge.  `HedgeOutcomeFlow`
proves exact finite support formulas for the general routed hedge models and
packages an unrestricted original-query counterexample when readout routing
does not re-enter `large \ small`; removing that geometric hypothesis and preserving
strict positivity remain the countermodel obligations.  `IdentificationInduction`
supplies exact success, failure, and unfinished traces so this work can proceed
by one lemma per recursive ID branch rather than by enumerating deeper
branch-name stacks.

The remaining modules transport ordinary, modal, learning, hidden-DAG, and
counterfactual certificates.  The project-wide axiom audit checks declarations
reachable through this facade and permits only the foundational `propext` and
`Quot.sound` axioms.
-/
