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
| 1. Combined baseline | Verified for this revision | `f298629cf204a426687e05684703938325ed6c6d`; local complete build and audit passed, 84 helper tests passed, and main CI run `39465544030` passed. |
| 2. Mathematical and API inventory | Implemented, awaiting review | Result families and boundaries below; moved declarations also require exact preservation checks. |
| 3. Current documentation | Implemented, awaiting review | Historical completeness inventory copied verbatim to `docs/history/completeness-development.md`; source-facade cleanup and final current-status cross-references remain pending. |
| 4. Lightweight foundations | Implemented, awaiting review | Unchanged law-equality and almost-sure-support declarations extracted to `Distros.LawBasics`; both targeted modules compile. Compatibility clients and full checkpoint gates still require verification. The causal dependency chain remains pending. |
| 5. Historical separation | Pending | Classify shared mathematics before moving historical proofs. Keep every retained declaration and mandatory audit coverage. |
| 6. Measured bottlenecks | Pending | Protocol below distinguishes warm, incremental and cold results. No further speedup has yet been established. |
| 7. Folder and module organization | Pending | Choose mathematical boundaries after dependency cleanup; preserve old import paths and namespaces where appropriate. |
| 8. Verified publication | Pending | Publish coherent verified checkpoints; final acceptance also requires Passes 2 and 3. |

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
this task. Concurrent search-metadata edits in `CodeSearchPreflight`,
`CodeSearchMetadata` and `NativeSearchMetadata` belong to the other agent and
are not part of the first extraction. New entropy results developed elsewhere
must not be overwritten or misreported as established by this refactor.

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
| Weighted arithmetic–geometric mean | `FiniteAMGM.weighted_inequality`, `weighted_product_le_pow`, `weighted_product_lt_pow` | Supplied natural multiplicities, actual products, and the original non-strict/strict hypotheses. |
| Primitive causal soundness | `ObservedGraph.publishedSoundness` in `CausalTransport.Soundness`; native interpretation in `HiddenDAGSoundness` | The same three graph rules and derivation support; no external soundness premise is inserted. |
| Positive-class completeness | `ObservedGraph.publishedCompleteness` in `HedgeChannelCompleteness` | Joint, conditional and hedge fields; positive compatible models, supplied distinct observed labels, actual engine outputs and actual original-query countermodels. |
| Original hidden DAGs | `FiniteLatentProjection.publishedHiddenDAGCompleteness`; `HiddenDAGModelClass.identifyJointKernel_identifiable_iff` and `identifyConditionalKernel_identifiable_iff` | Fixed observed domains with value richness, arbitrary finite hidden/private-noise sizes and the unchanged original DAG and query. |
| Supported zeros | `HiddenDAGSupportedDomain.identifyGuardedJointKernel_identifiable_iff` and its conditional counterpart | Expression-qualified supported representation, original conditional-target support, and existing positive-model coverage; not unrestricted applicability of every chosen expression. |
| Modal integration | `PositiveModal`, `SupportedModal`, `ModalRealization`; positive/supported joint and conditional modal equivalences | Actual stored-model membership, executed endpoints, and the original positive/support-aware class distinction. |
| Fixed-law and IV results | `BinaryInstrumentalSharpBounds`, `BinaryInstrumentalIdentification`, `BinaryInstrumentalAttainable` | Explicit compatible-law premises, null instrument arms, exact risks and the injective signed-effect encoding, endpoint models and rational attainable values. |
| Representation and certificates | `HiddenDAGFiniteRepresentation`, `HiddenDAGNativeTemplateCoverage`, finite polynomial and source-compression families | Actual supplied finite presentations, retained events/interventions, independence and bounded/checked-certificate qualifications; no complete unrestricted optimizer is presumed. |
| Bounded proof search | `NativeProofEnumeration`, `CodeEnumerationCounts`, `CodeSearchPreflight`, `NativeSearchPreflight` | The exact grammar and depth/resource budgets, original public dictionary, coverage of accepted supplied guards and the absence of an unrestricted stopping theorem. |
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
not evidence that the complete refactored tree or audit has passed, and not a
before/after elapsed-time speedup. The compatibility cohort was deferred once
because the other agent held the shared compiler slot; no competing compiler
was launched.

## Measurement protocol

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
