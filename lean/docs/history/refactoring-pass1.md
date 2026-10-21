# Historical Pass 1 refactoring ledger

This is the preserved development record, not the current completion status.
See the [current ledger](../../REFACTORING.md) for the bounded review passes
and exact verified checkpoints. Paths in the preserved text are relative to
the original `lean` directory. The text after the marker is retained verbatim.

<!-- BEGIN PRESERVED PASS 1 LEDGER -->
# Lean refactoring ledger

This refactor preserves the existing mathematical results while separating
shared foundations, current proofs and historical developments. The permitted
axiom dependencies remain exactly `propext` and `Quot.sound`. Rational atom
weights, null cells, explicit support conditions, original-query countermodels
and all existing computational guarantees are part of the preservation contract.

## Pass and acceptance rules

Pass 1 implements the eight stages below. Pass 2 reconsiders every stage after
the structural changes, even where the first pass found no necessary edit.
Pass 3 is read-only acceptance of a frozen checkpoint; normal build artifacts
may be produced, but no source or documentation repairs are allowed in that pass.
A material failure in Pass 3 leaves the goal incomplete and requires user
authorization for another working pass. The same validation problem gets at
most three repair attempts. Neither limit licenses marking an unresolved item
complete.

The stage statuses are **Pending**, **Implemented, awaiting review**,
**Verified for this revision**, and **Blocked or incomplete**. A green status
applies only to the cited source revision and evidence scope. Later edits
invalidate the affected evidence; a checkpoint is not acceptance of the whole
refactor.

| Stage | Pass 1 status | Evidence and remaining work |
| --- | --- | --- |
| 1. Combined baseline | Verified for this revision | Original combined baseline `f298629cf204a426687e05684703938325ed6c6d` passed all local and remote gates. Combined `a44aa4a` retains newer entropy, bounded selection and the first causal refactor, with complete CI passed. |
| 2. Mathematical and API inventory | Implemented, awaiting review | Result families and boundaries below; moved declarations also require exact preservation checks. |
| 3. Current documentation | Implemented, awaiting review | Historical completeness inventory moved verbatim to `docs/history/completeness-development.md`; the compatibility facade now identifies completed public results. One stale channel-gap claim is corrected; the full comment review remains pending. |
| 4. Lightweight foundations | Implemented, awaiting review | Distribution extraction passed complete gates at `340772f`; first causal extraction at `e2eee12` and combined `a44aa4a` also passed complete CI. Further parity, Bayes, conditional-core and witness-search boundaries remove historical imports from current public completeness paths; full local gates passed for the pending checkpoint. |
| 5. Historical separation | Implemented, awaiting review | Three finite-depth legacy proof collections moved unchanged to `CausalTransport/Historical`, with exact namespace-body guards, old-path facades and mandatory audit reachability. Full local archived-checkpoint gates passed; remote verification and classification review remain pending. |
| 6. Measured bottlenecks | Implemented, awaiting review | Two measured 30-second conditional-readout regression timeouts were removed by separating unchanged graph/engine checks from semantic routing. Comparable full-project speedup benchmarks and final review remain pending; no new universal twofold claim is made. |
| 7. Folder and module organization | Implemented, awaiting review | Shared hedge mathematics and historical failure stacks have separate `Hedge` and `Historical` homes; `docs/structure.md` gives reading order and compatibility maps. The broader layout review remains pending. |
| 8. Verified publication | Implemented, awaiting review | `340772f` and combined causal/entropy/selection checkpoint `a44aa4a` are on main after complete remote verification. The newer extraction/archive checkpoint and final acceptance, including Passes 2 and 3, remain pending. |

Pass 2 has not started. Pass 3 has not started. No historical mathematical
declaration has been approved for deletion.

## Baseline and concurrent work

The baseline combines finite entropy and exact-log arithmetic, constructive
finite weighted AM–GM, and the published bounded-search admission interfaces.
It is not the earlier entropy-free verification branch. Its full planned
Lean/audit traversal contains 905 modules; the smoke executable needs only
Main's native object because its separate Lake prerequisite still checks
the complete `Thesis` facade.

Local baseline evidence is retained in
`.lake/local-builds-v1/20261020-193828-k4pzy7ez/`: both actual final commands
passed with the committed configuration, one compiler family, the 5 GiB
aggregate watchdog and the unchanged 30-second per-invocation limit. The final
complete-build command took 0.563 seconds and the audit command 0.416 seconds
from the current normal cache. These are warm measurements, not cold proof
elaboration costs.

The pre-existing modified `latex/mathematical_inference.pdf` is excluded from
this task. The other agent's search-metadata work is committed in `f7204c7`
and passed complete CI run `39566237118`. That checkpoint includes the
distribution extraction and entropy revision `219cb99`. The other agent's
native formula/bounded selection work is now committed as `d104df6`, retained
in combined `a44aa4a`, and is no longer untracked work. Entropy and search
results are retained, not claimed as new mathematical results of refactoring.

The first foundation checkpoint was combined with the newer entropy results
without switching or resetting the shared checkout. Exact commit
`340772f6f4b1c3f72ddd15b9714737569f31adc2` passed CI run `39469288493`,
including the complete project, full kernel-axiom policy, distribution audit,
constructive-algebra audit and helper/regression gates. It was then published
to main. This is a verified intermediate checkpoint, not final refactor
acceptance.

First causal extraction `e2eee12fd1095eabf81b8691be53d044f9eaf75d`
passed complete CI run `39569394543`. Main advanced independently with further
entropy results, so the retained combined checkpoint is
`a44aa4ab2b098674862463e0d4f6d0ef41323e48`, verified by complete CI run
`39570398367`. It contains the causal extraction, entropy through the rational
zero-boundary threshold, and admitted bounded native formula selection. That
exact combined checkpoint is on main; no force push, checkout reset or PDF
staging was used.

The second causal boundary/archive checkpoint `47904c8` passed complete CI
run `39617171554`. Main had meanwhile gained entropy continuity and certified
rational moment approximation; these were retained by merge `dfdd3ae`, which
passed complete CI run `39657497397` before publication was attempted. These
are intermediate verified checkpoints, not acceptance of later local edits.

## Mathematical and public interface contract

The baseline Git tree is the complete source inventory, including helpers and
regressions, not just the named examples below. The table identifies the main
result families whose hypotheses and meanings must remain unchanged. Existing
full import facades and declared public namespaces remain compatibility entry
points. Moving source text is not permission to weaken a theorem statement,
change an algorithm's output or revive the removed unsafe identification API.

| Family | Existing implementation and representative interfaces | Preserved boundary |
| --- | --- | --- |
| Constructive probability | `Probability.Core`, `Urn`, `QualitativeUrn`; `ClaytonWaddington.QualitativeUrnScale.eqv_iff_sameRatio` and its rescaling results | Boolean events, supplied finite data, positive denominators and cross-multiplication equality; no general classical selection. |
| Finite records and distributions | `FiniteRecord`, `Distros.Basic`, `LawEquivalence` and the named-law/moment families exposed by `Probability.Distros` | Repeated atom labels, null weights, normalization, every-event law agreement and the exact support premises of conditioning. |
| Entropy | `ExactLog*`, `EntropyValue`, `Distros.Entropy`; `Distro.entropy_nonnegative`, `entropy_sameLaw`, `relativeEntropy_sameLaw`, `relativeEntropy_self` | Exact symbolic entropy values are not rational atom weights or an assumed real logarithm. Reference positivity and declared grid support remain explicit. |
| Gibbs inequality and equality | Newer retained `Distros.EntropyGibbs` and `EntropyGibbsEquality`; `Distro.sameLaw_of_relativeEntropy_zero`, `relativeEntropy_equiv_zero_iff` | The original finite-grid coverage and reference-positivity premises, symbolic exact logarithms and every-event equality of laws. |
| Further entropy results | Retained `CrossEntropy`, `EntropyUniform`, `EntropyConcavity`, `EntropyMomentConvex` and rational boundary estimates | Supplied finite grids, positive natural mixture coefficients, exact equality/strictness premises, closed rational moment intervals and the proved rational precision threshold; no assumed real-valued optimizer or irrational probabilities. |
| Weighted arithmetic–geometric mean | `FiniteAMGM.weighted_inequality`, `weighted_product_le_pow`, `weighted_product_lt_pow` | Supplied natural multiplicities, actual products, and the original non-strict/strict hypotheses. |
| Primitive causal soundness | `ObservedGraph.publishedSoundness` in `CausalTransport.Soundness`; native interpretation in `HiddenDAGSoundness` | The same three graph rules and derivation support; no external soundness premise is inserted. |
| Positive-class completeness | `ObservedGraph.publishedCompleteness` in `HedgeChannelCompleteness` | Joint, conditional and hedge fields; positive compatible models, supplied distinct observed labels, actual engine outputs and actual original-query countermodels. |
| Original hidden DAGs | `FiniteLatentProjection.publishedHiddenDAGCompleteness`; `HiddenDAGModelClass.identifyJointKernel_identifiable_iff` and `identifyConditionalKernel_identifiable_iff` | Fixed observed domains with value richness, arbitrary finite hidden/private-noise sizes and the unchanged original DAG and query. |
| Supported zeros | `HiddenDAGSupportedDomain.identifyGuardedJointKernel_identifiable_iff` and its conditional counterpart | Expression-qualified supported representation, original conditional-target support, and existing positive-model coverage; not unrestricted applicability of every chosen expression. |
| Modal integration | `PositiveModal`, `SupportedModal`, `ModalRealization`; positive/supported joint and conditional modal equivalences | Actual stored-model membership, executed endpoints, and the original positive/support-aware class distinction. |
| Counterfactual semantics and transport | `Causality.Counterfactual`, `CausalTransport.Counterfactual`; single-action/twin-network identities and finite source transport | Shared latent assignments across worlds and the existing explicit external multiworld-completeness interface; joint/conditional ID completeness is not silently enlarged to a proved unrestricted counterfactual identification theorem. |
| Fixed-law and IV results | `BinaryInstrumentalSharpBounds`, `BinaryInstrumentalIdentification`, `BinaryInstrumentalAttainable` | Explicit compatible-law premises, null instrument arms, exact risks and the injective signed-effect encoding, endpoint models and rational attainable values. |
| Representation and certificates | `HiddenDAGFiniteRepresentation`, `HiddenDAGNativeTemplateCoverage`, finite polynomial and source-compression families | Actual supplied finite presentations, retained events/interventions, independence and bounded/checked-certificate qualifications; no complete unrestricted optimizer is presumed. |
| Bounded proof search | `NativeProofEnumeration`, `CodeEnumerationCounts`, `CodeSearchPreflight`, `NativeSearchPreflight`, `NativeBoundedSelection` | The exact grammar and depth/resource budgets, certified domain-size metadata, source alignment, soundness/coverage of admitted catalogue selection, and the absence of an unrestricted stopping theorem. |
| Historical results | `CompletenessLegacy*`, qualified `Causality.Legacy` engines, historical carrier constructions and regressions | Preserve source and results, distinguish valid control-flow facts from the refuted general legacy formula compiler, and keep all retained history audited. |

Every extraction must record its source block and new owner, verify unchanged
declaration text or explicitly justified signature preservation, and then pass
Lean and the transitive axiom policy. Text/dependency guards support those gates;
they are not substitutes for kernel checking.

## First distribution foundation extraction

`Distros.LawBasics` now owns the unchanged `Distro.SameLaw` definition and its
four elementary lemmas, plus the unchanged `Distro.AlmostSurely` predicate.
`LawEquivalence` and `SignedConcentration` import it and retain all their
remaining declarations. The entropy implementation imports that smaller
interface directly. No probability value, support premise, theorem statement
or proof body in the moved blocks changed.

The original equality block has SHA-256
`7dc6fb1ddc57973895f61876b8d8040b466851aee523e942d90e8dc45e5fb4e0`;
the original support block has SHA-256
`ae724d2b7c6b8538a775adb440fc1be6096279e485e27dfe6e5d38403d6a9ec2`.
`test_probability_layers.py` checks those exact blocks, the old import paths,
the new dependency boundary and continued full-audit reachability.

The entropy import closure shrank from 19 modules at the baseline to 13,
while `LawBasics` has an eight-module closure. Its ordinary Lake target passed
in 0.49 seconds / 629.0 MiB sampled aggregate RSS; the unchanged entropy proofs
passed in 0.56 seconds / 636.7 MiB. These are targeted compilation results,
not a before/after elapsed-time speedup. After the shared compiler slot became
available, the 24-module law-equivalence, signed-concentration and entropy-example
compatibility cohort passed from the normal cache. Complete remote verification
of the combined extraction is recorded above; no competing compiler was launched.

## Shared causal foundations

The causal extraction starts from fully verified `f7204c7`. Exact source blocks,
including their proof bodies, are protected by `test_causal_foundations.py`.
The extracted interfaces retain their original declaration namespaces and
support/graph premises. No new soundness or completeness theorem is claimed.

| Shared owner | Preserved declarations and role | Compatibility path |
| --- | --- | --- |
| `Causality.TermSupport` | Unconditional and positive observational support, finite marginal support, product support and positive-denominator division support | `CompletenessCertificates` |
| `Causality.InterventionalCounterexample` | `InterventionalQuery.not_kernelValueEquivalent_of_not_value` for the unchanged query | `CompletenessHedgeParity` |
| `Causality.IdentificationOutcomeTraces` | Ordered first failure/sentinel witnesses and exact successful collector alignment | `Causality.Legacy.IdentificationInduction` |
| `Causality.CForestConstruction` | The three component/child-map-to-forest constructors | `CompletenessCertificates` |
| `CausalTransport.ActionDeletion` | Rule-3 query equalities, action restriction and inspectable deletion/shrink derivations | `CompletenessCertificates` |
| `CausalTransport.Hedge.ReadoutGeometry` | Finite ancestry reflection, explicit routes, typed lookups and common outcome-sink geometry | `CompletenessFailureExtraction` |
| `CausalTransport.Hedge.Models` | The unchanged finite latent, pair-root, incidence, parity and routing-model development | `CompletenessHedgeModels` |

Before extraction, `ChainCompilation`, `ValueRefinementCounterexample` and
`HedgeChannelCharacters` reached 36, 39 and 36 project modules respectively.
They now reach 21, 19 and 24. Each of those current clients is free of legacy
modules. The current structural success/failure compiler prerequisites also
compile against the focused interfaces. At first checkpoint `e2eee12`, the
complete public completeness path still reached history through other
parity/countermodel imports; the second boundary below removes those paths.

Targeted local checks passed for the new modules and selected current clients.
The unchanged 5,295-line model module compiled in 12.51 seconds with 851.2 MiB
sampled aggregate RSS; the initial 1,590-line readout extraction took 1.75 seconds
with 721.0 MiB. These single invocations measure feasibility, not speedup against
the original owner. Adding the remaining shared ancestry block subsequently
passed in 1.80 seconds with 744.4 MiB. Helper/regression tests currently pass
98 tests at the first causal checkpoint, whose complete remote build and axiom
audit subsequently passed as recorded above.

Two targeted checks exposed missing explicit dependencies after removing broad
imports: query types for `ActionDeletion`, and ancestry/forest constructors for
`KernelHedgeTransport`. These were repaired by importing or extracting their
original definitions, without changing proofs. A later full-cohort check likewise
required the explicit public-certificate import in `KernelSuccessCompilation`.
All three targeted repairs passed and the complete first-checkpoint CI passed.

## Current completeness and retained history boundary

`Hedge.Parity` now owns the unchanged incidence/support development plus the
three unchanged one-anchor correction declarations from `HedgePositive`.
`HedgePartialIncidence` imports that parity layer, rather than the entire
positive carrier development. The channel counterexample's 63-module closure
passed locally; parity itself compiled in 3.10 seconds with 819.1 MiB sampled
aggregate RSS.

`ConditionalBayes` owns the original six joint/conditional syntax, derivation
and source-support declarations. Completeness assembly imports this bridge and
proved soundness directly, rather than obtaining it through historical
countermodel imports. `ConditionalFailureCore` preserves general exchange
extraction and terminal assembly; the single geometrically qualified carrier
case is retained separately in `ConditionalFailureCarrierCases`. The original
`ConditionalFailureExtraction` path reexports both. `Hedge.WitnessSearch`
preserves the general Boolean-test-to-hedge construction; regression clients
now import it explicitly instead of inheriting historical failure machinery.

Targeted compilation passed both the complete current package and its retained
carrier-case compatibility path (192 modules before physical archiving).
Current positive-class, original-hidden-DAG, supported-zero and modal theorem
paths contain no `Causality.Legacy`, `CompletenessLegacy` or `Historical` module.
Before/after project closure counts against `f7204c7` are 181 to 177 for
`HedgeChannelCompleteness`, 210 to 206 for `HiddenDAGCorrespondence`, and 237 to
233 for `HiddenDAGSupportedCorrespondence`; the counterexample client shrinks
from 80 to 63. Soundness remains at 25. These counts describe dependencies,
not elapsed-time speedups.

The three finite-depth legacy collections are category 2 historical material,
including their retained legacy trace-compiler interfaces. Shared support,
graph, parity, derivation and collector mathematics was extracted first.
Their unchanged namespace bodies now live in `Historical.LegacyShrinkFailures`,
`Historical.LegacyProductFailures` and `Historical.LegacyNestedFailures`.
Every old path remains a facade, and every archived body is inside mandatory
full-audit reachability. Public current end-results and qualified carrier
theorems are not discarded or classified obsolete merely for lacking callers.

The structural reading guide records each old-to-new location. Preservation
guards check exact moved blocks and archive bodies; only surplus blank lines
are normalized for the conditional-core extraction check. The helper suite
currently passes 108 tests, including the other agent's three bounded-selection
tests. The complete new extraction/archive local build and axiom audit passed
with 961 planned modules and 43,563 imported project declarations checked.
Evidence is retained in `.lake/local-builds-v1/20261021-155013-3c4a4im7/`.
Both actual native final commands passed (0.489 seconds for the warm build,
0.540 seconds for the warm audit). This resumed traversal rebuilt 98 modules
and reused 864 valid facets; it is not a clean cold-build measurement. The
unmodified resource limits and all retained history/regressions remained active.
Remote verification of this exact forthcoming checkpoint remains pending.

The earlier full local attempt rebuilt through module 618 before the other
agent changed the shared import facades. The source-fingerprint safeguard
stopped it; that attempt is not a full local success. Compiler-slot contention
was handled by deferring checks, never by launching a competing compiler.

## Measured conditional readout bottleneck

The complete local traversal reached the original
`Examples.HedgeConditionalReadout` regression, then stopped at the unchanged
30-second wall limit with 2524.3 MiB sampled aggregate RSS. This was a time
stop, not a memory failure. The bounded import profile took about 1.1 seconds;
the remaining cost was not explained by import loading alone.

A first graph/semantic two-file extraction still timed out in its graph half.
The successful refinement separates graph definitions, the finite no-exchange
check, and exact engine-failure coordinates into
`Examples/HedgeConditionalReadout/{Graph,Exchange,Failure}.lean`. The original
entry point retains the unchanged routing and actual countermodels. Its graph
checks import only the intrinsic current engine, not semantic readout or carrier
machinery. No theorem statement, proof body, finite calculation or resource cap
was weakened or omitted.

The bounded ordinary Lake checks passed at 1.59 seconds / 638.4 MiB for graph
setup, 21.93 seconds / 2384.1 MiB for exchange, 8.34 seconds / 2502.0 MiB for
engine failure, and 1.29 seconds / 746.8 MiB for the semantic readout module.
Their aggregate 33.15 seconds is not a full-build speedup claim. The benefit is
bounded local invocations and dependency reuse: a readout-theory change no
longer invalidates the independent concrete graph computations. Exact source
guards reassemble the original graph block and protect the original complete
routing/countermodel tail.

The separate `HedgeConditionalClosedReadout` fixture subsequently hit the same
30-second limit at 2722.3 MiB. Its unchanged data and two independent query
computations now live in `HedgeConditionalClosedReadout/{Graph,PrimaryEngine,
EarlierEngine}.lean`; the original root retains all semantic countermodels.
The checks passed in 1.53, 16.25 and 16.45 seconds respectively, followed by
0.95 seconds for the semantic module. Exact-source guards retain all six engine
assertions, both identical private failure helpers and the semantic body. Again,
this establishes bounded local feasibility and reuse, not a cold speedup.
Full local verification then passed as recorded above.

## Remaining carrier dependency and status-comment review

The second review found two current, qualified end-results (`HedgePositive`
and `HedgeOutcomeFlow`) still inheriting `Completeness` for finite parity/mix
lemmas. The exact 3,223-line mathematical body of the former
`CompletenessHedgeCountermodels` now lives in `Hedge.Countermodels`; only its
imports and module-level explanation changed. The old path reexports it and
preserves the preceding historical interface. Its proof-body hash, old-path
compatibility, audit reachability and history-free current clients are guarded
by `test_causal_foundations.py`.

The new owner and the two clients passed bounded local checks in 3.79, 4.16
and 1.52 seconds, with sampled aggregate RSS below 867 MiB. Their current
closures contain 29, 38 and 30 project modules respectively; the qualified
conditional carrier path has 63. None reaches legacy/history. These are
targeted feasibility and dependency results, not a whole-project speedup.

The top-level supported-zero status was stale: recursive guarded ID/IDC and
the expression-qualified completeness package are implemented, while coverage
of every alternative formula's application domain remains unproved. Three
channel/environment module summaries now point to the completed downstream
original-outcome and terminal-countermodel theorems without erasing their
valid local restrictions. A historical trace comment now distinguishes its
fuel-exhaustion lemma from the current engine's separate termination proof.
Full local verification of these subsequent edits passed in
`.lake/local-builds-v1/20261021-210043-ppkvpaw1/`: 972 planned modules,
255 rebuilt targets, 718 reused facets, and 43,805 imported project declarations
passing the transitive axiom policy. Peak sampled aggregate RSS was
3801.9 MiB, below the unchanged 5120 MiB watchdog. The actual final native
build and audit commands passed with the committed configuration. This is a
resumed incremental verification, not a clean cold benchmark. Exact-checkpoint
remote verification remains pending.

An independent source-graph scan found no cycles and no production dependency
on regression examples. The old source paths from `f7204c7` all remain present.
The new global guards exclude only the named historical/compatibility layers;
current `CompletenessAssembly` and public end-results are not exempted merely
because their names contain "Completeness". The helper suite passes 110 tests.
The original defining-module paths remain compatible; narrowing a focused
client deliberately stops relying on its old incidental historical reexports.

The layout review retains the established topic-named bound, search, modal
and distribution paths. Renaming all those files would create more forwarding
modules and invalidate clients without a demonstrated semantic/dependency or
build benefit. The introduced subfolders instead mark actual shared/history
ownership or a measured regression boundary. The generic singleton-sum lemma
stays in the shared countermodel layer for now: its only clients are in that
family, and another tiny foundational file has no measured benefit here.

Three fully cached native build/audit pairs on this combined source took
1.585, 1.565 and 1.601 seconds (median 1.585 seconds), with a maximum sampled
aggregate RSS of 87.5 MiB. Each actual pair was preceded by separate no-build
freshness preflights; the reported pair times exclude those diagnostic
preflights. The actual commands used the committed configuration,
`LEAN_NUM_THREADS=1`, `--rehash` and `--no-cache`, under the unchanged external
watchdog. Logs: `.lake/refactor-native-warm-5dkvtvqn/`. This measures warm
workflow latency, not fresh proof elaboration or a cold-build speedup.

The three immediately following, fully cached monitored workflows passed in
16.560, 16.554 and 17.128 seconds (median 16.560 seconds), using the same
combined source, normal cache and approved profile. Logs:
`.lake/refactor-monitored-warm-zg0fkfh9/`. The monitored figure includes its
extra source fingerprints, per-target preflights, process sampling and
bookkeeping; the native pair does not claim to provide those extra safeguards.
This comparison concerns the two supported warm workflows, not a mathematical
elaboration speedup or evidence that a clean cold build is twice as fast.

## Measurement protocol

The carrier dependency checkpoint `9a98e7e` was saved after the complete local
build/audit and the paired warm measurements above. Its exact remote run is
`39659979565` (pending when this entry was written). Concurrent native rewrite
path/linearization work and its guide/workflow changes belong to the other
agent; they are not part of this checkpoint or evidence for this refactor.

The broader Pass 1 status-language scan then found additional developmental
"still open" wording in 21 transport modules. Those edits change comments
only: a nested-comment/string-aware source comparison confirms identical
non-comment Lean text for every affected file. The explanations now distinguish
locally supplied graph/parity/support premises from their completed downstream
constructors, and distinguish old qualified carrier families from general
channel completeness. No claim is added that the old carrier method itself
works outside its original geometric hypotheses. A malformed documentation
heading and a subject/verb mismatch are also corrected. The focused eight
foundation guards pass; complete verification of this comment-only batch is
pending. Pass 2 and frozen Pass 3 have not begun.

Fix the compared source snapshots, pinned toolchain, platform, resource profile
and benchmark category before an optimization. Keep one compiler family and
reuse genuine Lake traces. Do not clean the shared cache or fabricate freshness.

1. **Warm verification:** measure three sequential complete build/audit pairs
   and report the median with each individual result. Distinguish native Lake
   from the extra monitored workflow rather than attributing wrapper overhead
   to proof checking.
2. **Incremental changes:** choose a lightweight distribution client and a
   current completeness client before refactoring, record their dependency
   closures, and compare the same compilation/import checks before and after.
   Keep import costs separate from fresh proof elaboration. Any forced rebuild
   experiment must use an isolated benchmark location or otherwise approved
   recoverable artifacts, not changes to another agent's files.
3. **Cold verification:** use comparable isolated CI builds if needed; do not
   delete the laptop's shared cache. A single paired cold measurement is
   preliminary evidence, not a robust universal twofold-speedup claim.

Folder moves and lower job counts alone do not establish faster checking.
The full preserved historical audit remains mandatory, even when a current-only
dependency path becomes smaller. Remaining expensive modules should be split
only at a measured, mathematically coherent boundary.
