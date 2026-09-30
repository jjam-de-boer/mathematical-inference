import Thesis.CausalTransport.DSeparation
import Thesis.CausalTransport.DSeparationCorrectness
import Thesis.CausalTransport.Certificates
import Thesis.CausalTransport.Correspondence
import Thesis.CausalTransport.FiniteSource
import Thesis.CausalTransport.Soundness
import Thesis.CausalTransport.Completeness
import Thesis.CausalTransport.ChainCompilation
import Thesis.CausalTransport.KernelIdentification
import Thesis.CausalTransport.KernelCompilation
import Thesis.CausalTransport.ProductCompilation
import Thesis.CausalTransport.KernelSeparation
import Thesis.CausalTransport.KernelPartition
import Thesis.CausalTransport.ComponentCompilation
import Thesis.CausalTransport.KernelRecursionSeparation
import Thesis.CausalTransport.KernelRecursionCompilation
import Thesis.CausalTransport.KernelProductCompilation
import Thesis.CausalTransport.KernelSuccessCompilation
import Thesis.CausalTransport.HedgeOutcomeFlow
import Thesis.CausalTransport.HedgePositive
import Thesis.CausalTransport.CompletenessAssembly
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
boundaries.  These records make theorem ownership explicit: soundness is
inhabited constructively below, while importing this facade still does not
assume completeness as an axiom.

`FiniteSource` supplies an independently executable finite-table semantics,
proves preservation into the intrinsic semantics, and exposes source-level
adapters.  `DSeparationCorrectness` connects the finite ancestry and moral
reachability searches to active-path separation.

`Soundness` develops the graph-independent probability algebra and the finite
latent factorization needed by the three do-calculus rules.  The factorized
path arguments now construct every rule partition directly from projected
graph compatibility, and `ObservedGraph.publishedSoundness` assembles those
partitions with d-separation correctness into the complete published record.
The older hypothesis-bearing adapters remain useful as documented local
interfaces, but they are no longer obligations of the public theorem.

`Completeness` develops the executable ID side for the positive model class:
successful special cases compile to supported certificates, the two terminal
success-trace constructors compile to formula-aligned packages, finite search
extracts hedge data from checked failures, and shared-switch hedge models
provide positive counterexamples for the covered queries.  `HedgePositive`
uses finite marginalization to reduce full-query separation to one suitable
outcome coordinate.  Its strongest localized mix selects a directed-and-
bidirected action-parent bow and reads only that bow's pair-root.  This removes
parent-uniqueness, odd-parity, identical-neighbourhood assumptions, and all
restrictions on the pivot's other outgoing edges without choosing a family of
pointwise equivalences.  A complete `PublishedCompleteness`
inhabitant still needs replacement-engine failure transport, a positive
countermodel for an arbitrary original-query hedge, and general conditional
identification.  `ChainCompilation`
supplies the probability-algebra foundation of that compiler: an exact,
support-carrying observational chain certificate on any finite host, including
hosts with topological gaps.  It does not identify a recursive ID input with
the host's observational marginal.  The front-door regression in
`Thesis.Examples.IdentificationRegression` proves that a legacy successful
engine formula is incorrect in a positive compatible model: its exact-output
success compiler cannot exist.  A total, action-free engine result is not
itself a certificate.
`IdentificationKernel` now implements the replacement recursion with
current-input prefix quotients, uncut ancestral pruning, and the separate
action-augmentation branch.  `KernelIdentification` proves a quadratic
fuel bound for every invocation of that replacement.  `KernelSuccessCompilation`
now compiles every successful invocation of the changed program by fuel
induction.  Lifting its failures to the original-query hedge countermodel
remains a completeness obligation; old failure traces do not establish that
connection for a changed program.
`KernelCompilation` now certifies host marginals and the complete topological
chain product of an arbitrary certified current input, retaining external
intervention parameters and the engine's exact prefix-quotient syntax.  Its
positive-support invariant is propagated directly by finite SCM consistency
and probability algebra, without importing soundness.  Its shared finite
chain fold also assembles any family of certified component factors without
duplicating the prefix induction.  `KernelSeparation` proves the rule-3 later-
action and rule-2 outside-predecessor side conditions from topological order,
recursive host parent closure, and actual c-component membership.
`ComponentCompilation` uses those graph theorems to certify the exact
current-input product for every listed host component, retaining external
actions and supplying positive support for recursion.  It also compiles the
terminal complementary marginal; unions of entire components and empty
subsets are covered by its general closed-subset constructor.  The structural
success compiler applies it to arbitrary containing-component recursion.
`KernelRecursionSeparation` proves incoming-cut non-ancestor isolation and
connects full expanded ancestry to the engine's induced-host tests.  Its
pruning and augmentation side conditions retain their different uncut and
incoming-cut ancestry criteria.  `KernelRecursionCompilation` packages the
certified current-input, positive-support, and parent-closure invariants;
it transports arbitrary nested certificates through pruning, augmentation,
and containing-component restriction without resetting the current expression.
`KernelSuccessCompilation` now applies these constructors throughout the
complete recursion; the original-query hedge countermodel remains separate.
`ProductCompilation` supplies the product branch's graph-independent
regrouping step: inspectable rational associativity and commutativity turn
any indexed finite product into its nonempty partition blocks, including
interleaving components and repeated indices.  Its permutation compiler
uses explicit finite erasure with a constructive proof rather than the
library erasure theorem's choice dependency.  It also substitutes certified
factor reductions into products.  `KernelPartition` proves that the actual
collector is pairwise disjoint and its flattened component members are an
exact permutation of the host vertices.  Its component lookup uses Boolean
finite search, with success and uniqueness proved from the partition.
`KernelProductCompilation` combines arbitrary independently identified
components into their host joint, using reversed graph-derived factor rules,
the shared topological fold, exact regrouping, and support-sensitive formula
comparison.  Its complete split constructor retains the engine's exact
complementary marginal and positive target invariant.  It does not assume
the free joint's identification certificate, and covers arbitrary finite
partitions, external actions, and interleaving components.
`KernelSuccessCompilation` completes that induction over `identifyKernelFuel`.
Every successful invocation has an inspectable supported derivation whose
formula is the engine's literal returned term, with a positive target invariant.
Its public joint wrapper constructs the observational initial input internally;
it does not assume semantic identifiability or a hedge countermodel.
`HedgeOutcomeFlow`
proves exact finite support formulas for the general routed hedge models and
packages an unrestricted original-query counterexample when readout routing
does not re-enter `large \ small`; removing that geometric hypothesis and preserving
strict positivity remain the countermodel obligations.  `IdentificationInduction`
supplies exact legacy success, failure, and unfinished traces; the replacement
success compiler instead follows the changed program directly.  Remaining
failure proofs must likewise target that program, not deeper legacy branch-name
stacks.  `CompletenessAssembly` is the one-way integration layer:
it imports the completed soundness theorem without creating a dependency from
`Completeness` back to `Soundness`.  Its support-sensitive Bayes constructor
now combines arbitrary joint certificates into a conditional certificate,
requiring denominator positivity only where the source conditional is defined.
It also proves correctness and identifiability of every successful replacement
joint result.  The converse needed for `PublishedCompleteness` remains open.

The remaining modules transport ordinary, modal, learning, hidden-DAG, and
counterfactual certificates.  The project-wide axiom audit checks declarations
reachable through this facade and permits only the foundational `propext` and
`Quot.sound` axioms.
-/
