# Lean source structure and reading order

The library separates finite probability semantics, graph-indexed causal
programs, their mathematical verification, and applications. A broad facade
preserves convenient imports; focused implementation modules should use the
smallest mathematical layer that supplies their actual dependencies.

## Current reading order

| Start here | Mathematical responsibility | Continue with |
| --- | --- | --- |
| `Probability.Core`, `Urn`, `QualitativeUrn` | Finite rational probabilities, Boolean events and Clayton-style scale comparisons | `FiniteRecord`, finite products and support interfaces |
| `Probability.Distros.Basic`, `Distros.LawBasics` | Named distribution records, every-event law equality and almost-sure support | Specialized moment, concentration and entropy modules |
| `ExactLog*`, `EntropyValue`, `Distros.Entropy` | Exact symbolic logarithms and information quantities over rational records | `EntropyGibbs`, `EntropyGibbsEquality` and their examples |
| `Causality.Graph`, `Model`, `Semantics`, `Identification` | Finite graph/model semantics, causal query meanings and identification specifications | Graph search and derivation certificates |
| `Causality.IdentificationSearch`, `ComponentConnectivity`, `IdentificationRank` | Shared executable graph tests and constructive correctness/progress facts | The current `IdentificationKernel` and `ConditionalIdentificationKernel` programs |
| `Causality.TermSupport`, `InterventionalCounterexample`, `CForestConstruction`, `IdentificationOutcomeTraces` | Shared support, event-to-kernel separation, forest construction and ordered result witnesses | Focused success/failure compilers without legacy imports |
| `CausalTransport.DSeparation*`, `Certificates`, `Soundness*` | Checked graphical side conditions, inspectable derivations and soundness of their interpretation | Positive-class or support-aware compilation |
| `CausalTransport.ActionDeletion`, `ChainCompilation`, `Kernel*Compilation` | Rule constructors and exact formula-aligned current-engine success certificates | `KernelSuccessCompilation` and `CompletenessAssembly` |
| `CausalTransport.Hedge.ReadoutGeometry`, `Hedge.Models`, `Hedge.Parity` | Explicit graph routes, finite latent models and reusable parity/flow identities | Channel installation, integration and original-query countermodels |
| `HedgeChannelCompleteness`, `HiddenDAGCorrespondence` | Completed positive-class joint/conditional results and original hidden-DAG transfer | Public theorem coverage and modal applications |
| `HiddenDAGSupportedCorrespondence`, `PositiveModal`, `SupportedModal` | Supported-zero qualifications and actual mode-indexed executions | Support diagnostics and application examples |
| IV/bow, compression, polynomial certificates and bounded-search families | Additional finite-domain identification, bounds and checked representations | Their topic-named examples and coverage qualifications |

The model classes and support hypotheses are part of the results, not layout
details. [The coverage guide](../THEOREM_COVERAGE.md) states their application
boundaries; this reading order does not enlarge any theorem.

## Shared hedge foundations

`CausalTransport/Hedge` contains reusable geometry and model construction,
with declaration namespaces kept under `Thesis.Causality`. Its boundaries
follow mathematical responsibility rather than a uniform file-size target:

- `ReadoutGeometry` computes routes from finite reachability evidence and
  proves typed lookup and common-sink properties. It is not a countermodel
  or positivity theorem.
- `Models` builds actual finite latent/parity models and proves their local
  invariants. Readiness conditions on the older model families remain explicit;
  the unrestricted channel counterexample is assembled in its own modules.
- `Parity` supplies full and nested incidence solvers, exact support and
  forest-flow identities, plus the one-anchor parity correction shared by
  partial incidence and carrier models. It does not import positive-model
  counterexamples merely to obtain that Boolean correction.

None of these shared modules imports the historical identification recursion or
its branch-stack proofs. Some other current theorem paths still do; removing
those remaining dependencies requires further shared-mathematics extraction.

## Compatibility and historical material

`CompletenessHedgeModels` is an import-compatible facade for `Hedge.Models`.
It deliberately still exposes the preceding historical layers. Other original
completeness-layer paths likewise reexport the support, graph and derivation
declarations moved to their focused owners. Existing declaration names and
mathematical statements are unchanged.

`CompletenessHedgeParity` similarly reexports `Hedge.Parity` and retains the
older model facade. `HedgePartialIncidence` imports the focused parity layer
directly, so current channel integration no longer inherits the positive
carrier development or its historical engine imports for elementary parity.

`Causality/Legacy` quarantines the obsolete executable engine and its checked
control-flow proofs. `CausalTransport/Historical` retains the historical
finite-depth unpackers and legacy trace-compiler interfaces. They remain built and axiom-audited;
they are not a substitute for current-engine semantic completeness and must
not be exposed as an unsafe unqualified identification API.

| Original import | Retained implementation |
| --- | --- |
| `CausalTransport.CompletenessLegacyShrinkFailures` | `CausalTransport.Historical.LegacyShrinkFailures` |
| `CausalTransport.CompletenessLegacyProductFailures` | `CausalTransport.Historical.LegacyProductFailures` |
| `CausalTransport.CompletenessLegacyNestedFailures` | `CausalTransport.Historical.LegacyNestedFailures` |

Each old file is a compatibility facade. Exact-body preservation guards cover
the archived namespaces, declarations and proofs; import guards ensure that
the full audit still reaches both the old paths and the archived payloads.
Current positive, hidden-DAG, supported-zero and modal completeness paths do
not import those historical layers. Moving them does not claim that the
mandatory whole-project verification can skip their checking cost.

`ConditionalFailureCore` contains general IDC exchange/failure extraction and
terminal assembly. `ConditionalFailureCarrierCases` retains a qualified
carrier counterexample separately, and the old `ConditionalFailureExtraction`
path reexports both. `ConditionalBayes` supplies the original source-local
support argument without importing historical certificates.

The measured conditional-readout regression has a topic-grouped fixture in
`Examples/HedgeConditionalReadout`. `Graph` defines its original concrete query,
`Exchange` retains the finite no-exchange check, and `Failure` retains the actual
engine equations. The original `Examples.HedgeConditionalReadout` module still
constructs and checks the same routed countermodels. This split keeps each
local invocation within the existing limit and lets semantic edits reuse the
independent graph computations; it does not skip any regression.

`Examples/HedgeConditionalClosedReadout` applies the same boundary to its two
independent query calculations: `Graph` supplies the original fixture data,
`PrimaryEngine` and `EarlierEngine` retain all six engine assertions, and the
original entry point retains the actual semantic countermodels. Both example
families remain reachable from the full build and axiom audit.

The long earlier completeness development inventory is retained in
[historical documentation](history/completeness-development.md), not in the
current-status facade. Mathematical explanations and historical proved results
are preserved. A public end-result is not obsolete merely because no internal
module calls it, and qualified carrier countermodels are not historical junk
merely because a more general channel theorem exists.

## Verification and build interfaces

`Thesis` remains the broad proof-and-example facade. The executable's Lake
prerequisite checks that facade even though its runtime needs only IO.
`Thesis.AxiomAudit` checks the transitive imported project declarations,
including retained history and regressions; only `propext` and `Quot.sound`
are allowed. Source-dependency and preservation tests guard the extracted
boundaries but do not replace Lean's checks.

[Local checks](../LOCAL_CHECKS.md) documents ordinary native Lake builds and
the optional single-compiler resource-monitored route. The
[refactoring ledger](../REFACTORING.md) records exact checkpoint evidence,
remaining work and the bounded review passes.
