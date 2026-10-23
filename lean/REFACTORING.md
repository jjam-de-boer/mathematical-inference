# Lean refactoring: current ledger

The first working pass is published as `8a6ea5cbe30efe5559bd87d073ec8e5120445a14`.
Its [complete CI run](https://github.com/jjam-de-boer/mathematical-inference/actions/runs/39661212192)
passed before publication. **Both working passes are finished.** The combined
second-pass source checkpoint is `9fddbe71024f60db1492a60baccaf2cb305cd826`;
its [complete CI run](https://github.com/jjam-de-boer/mathematical-inference/actions/runs/39823389597)
and local full-build/axiom gates passed. This receipt's own commit is the final
acceptance candidate: verify its CI and publication before beginning the frozen
read-only pass. Acceptance is reported outside this file, not asserted in
advance. The detailed first-pass measurements, unsuccessful experiments,
source hashes and intermediate checkpoints are preserved in
[the historical ledger](docs/history/refactoring-pass1.md).

## Contract and stopping rules

- Preserve finite rational probabilities, null cells and explicit support.
- Preserve existing statements, constructive data, computational guarantees,
  public defining-module paths, qualified extensions and all historical results.
- Permit only transitive `propext` and `Quot.sound` dependencies. No choice,
  general excluded middle, `sorryAx`, `Lean.ofReduceBool` or new assumed axiom.
- Retain ordinary Lake builds and the optional monitored workflow. Keep one
  compiler, 4608 MiB Lean / 5120 MiB aggregate RSS and 30-second invocations;
  never delete the shared cache or raise limits without approval.
- Preserve unrelated work, especially the PDF and concurrent native-path work.
- Maximum: two working passes and one frozen read-only acceptance pass; at most
  three repair attempts for the same failing validation. A material failure in
  frozen acceptance requires reporting incomplete work, not a silent fourth pass.

Statuses are **Pending**, **Implemented, awaiting review**, **Verified for this
revision**, and **Blocked or incomplete**. Evidence belongs to its exact source
revision; an edit invalidates affected checks. No mathematical declaration has
been approved for deletion. This final receipt changes documentation only;
the Lean sources, build configuration and source guards equal the verified
combined second-pass checkpoint.

## Mathematical and interface inventory

The complete Git tree at original baseline `f298629cf204a426687e05684703938325ed6c6d`
is the preservation inventory, including helpers and examples. All its 906
`Thesis` module paths remain at the published first-pass checkpoint. The table
names representative public results; it is not permission to drop unnamed ones.

| Family / implementation | Preserved meaning and assumptions |
| --- | --- |
| `Probability.Core`, `Urn`, `QualitativeUrn` | Finite rational records, Boolean events, supplied finite data, positive denominators and Clayton-style scale comparisons. |
| `Distros.Basic`, `LawBasics`, `LawEquivalence`, named laws/moments | Every-event equality, repeated labels, null weights, normalization and exact conditioning support; no classical selection. |
| `ExactLog*`, `EntropyValue`, `Distros.Entropy`, `EntropyGibbsEquality` | Exact symbolic logarithms over rational probability records, declared grids/reference support, Gibbs equality and law invariance; not irrational atom weights. |
| `EntropyConcavity`, `EntropyMomentConvex`, `EntropyContinuity`, `EntropyOptimize`, `LogLinearEntropy` | Existing finite-grid, moment, mixture and positivity hypotheses; rational approximation certificates and proved log-linear optimality, not an assumed real optimizer. Newer published entropy work is retained, not attributed to this refactor. |
| `Distros.UncertaintyMeasure`, `UncertaintyUniform`, `UncertaintyUniformUniqueness`, `EntropyGrouping` | The newer published rational uncertainty/grouping results and uniform-law uniqueness are retained from main, without changing probability weights or attributing new mathematics to this refactor. |
| `FiniteAMGM` | Existing strict/non-strict weighted inequalities for supplied natural multiplicities. |
| `ObservedGraph.publishedSoundness`, `HiddenDAGSoundness` | The same three graphical do rules and derivation-local support, with proved interpretation rather than an external soundness axiom. |
| `ObservedGraph.publishedCompleteness`, `HiddenDAGCorrespondence` | Joint/conditional/hedge results in the positive class; original queries, actual engine outputs and countermodels, with supplied distinct observed labels. |
| `FiniteLatentProjection.publishedHiddenDAGCompleteness` | Original finite hidden DAG, fixed value-rich observed domains, arbitrary finite hidden/private-noise alphabets. |
| `HiddenDAGSupportedCorrespondence`, guarded certificates | Expression-qualified supported-zero representation, positive-model coverage and original conditional-target support; no universal alternative-formula-domain coverage. |
| `PositiveModal`, `SupportedModal`, `ModalRealization` | Actual stored-model membership and executed endpoints, preserving the positive/support-aware distinction. |
| `Causality.Counterfactual`, `CausalTransport.Counterfactual` | Shared latent worlds, existing twin-network/single-action identities and explicit external multiworld-completeness interface; no new unrestricted counterfactual identification claim. |
| Binary bow/IV bounds, identification and attainable-set modules | Compatible-law premises, null arms, exact risks/signed effects, endpoint witnesses and rational attainable values. |
| Finite representation, compression, polynomial certificates, bounded search | Supplied presentations, independence, certified finite templates and explicit grammar/resource bounds; no unrestricted feasibility or stopping theorem is inferred. |
| `Causality.Legacy`, `CausalTransport.Historical` and old facades | Every retained result remains verified; obsolete engine facts do not restore the unsafe unqualified API or substitute for current semantic completeness. |

The [causal coverage guide](THEOREM_COVERAGE.md), [entropy guide](ENTROPY.md),
and actual Lean statements specify the detailed hypotheses. The
[structure guide](docs/structure.md) gives reading order and old-to-new paths.

## Pass 2: every stage reconsidered

Pass 1 implemented all eight stages and passed the complete first-pass gates.
The second pass rechecks them after the moves, not just their original order.

| Stage | Second-pass review / decision | Status |
| --- | --- | --- |
| 1. Combined baseline | Reconfirmed published `8a6ea5c`, then retained the native-path extension and main's newer entropy through `1a01f3d` in combined checkpoint `9fddbe7`. Its complete local and remote gates passed; only the pre-existing PDF remains dirty. | Verified for this revision (`9fddbe7`). |
| 2. Mathematical/API inventory | Rechecked source preservation, support/model-class boundaries, public names/compatibility and counterfactual qualification. The inventory includes the newer entropy results. No theorem removal or assumption change is justified. | Verified for this revision (`9fddbe7`). |
| 3. Documentation | Moved the verbatim running diary out of this current ledger. Corrected one remaining root-parity progress claim: the unrestricted pair is not itself positive or an original-outcome counterexample; completed channel completeness is separate. | Verified for this revision (`9fddbe7`). |
| 4. Foundations | Rechecked law/support and causal dependency guards, including all current causal implementations. Convenience/compatibility facades intentionally retain history, not current implementations. Keep the generic singleton-sum lemma in its shared family: another tiny file has no demonstrated benefit. | Verified for this revision (`9fddbe7`). |
| 5. History | Rechecked all three exact archived namespace bodies, compatibility facades and mandatory audit reachability. Valid current carrier end-results remain current even without callers. No additional relocation/deletion is justified. | Verified for this revision (`9fddbe7`). |
| 6. Performance | Rechecked measurement logs and scope: bounded incremental feasibility and warm workflow latency are established, not a universal twofold cold-build improvement. No new unmeasured optimization is justified. | Verified for this revision (`9fddbe7`). |
| 7. Layout | Rechecked coherent `Hedge`/`Historical`/example boundaries, acyclicity, old paths, and absence of production imports of examples. Keep established topic paths instead of a wholesale forwarding-file rename. | Verified for this revision (`9fddbe7`). |
| 8. Verification/publication | The comment/guard/history checkpoint `9622bd6` passed complete CI, then `9fddbe7` retained newer main and passed all combined gates before publication. Verify this documentation-only receipt's exact CI/publication before freezing acceptance. | Verified for source revision `9fddbe7`; receipt gates precede Pass 3. |

The countermodel source guard permits only the precisely specified comment
correction before comparing the original whole-body hash. Proof text is still
compared exactly; the historical and other moved-source guards are unchanged.
The original first-pass ledger body has SHA-256
`bc0f06b5018e9ef3654502e64d63006388b4de2365cb67bb8684a99dd4f6959d`.

Independent second-pass comparisons found identical non-comment code (imports
excluded) in 23 central baseline probability, soundness, completeness, modal,
IV and representation modules. Moved blocks and archive bodies retain their
separate exact-source guards. All 111 helper/source tests pass, including the
new historical-ledger guard. Retained JSON/logs independently confirm every
warm timing, the 43,805-declaration core audit and the 3801.9 MiB sampled peak.

The shared branch retained `16c9ec9` (the other agent's elementary path/support
extension), merged published main as `7a86f99`, and then retained main's entropy
work through `1a01f3d` in `9fddbe7`. That concurrent work is preserved, not claimed
as new results of this refactor. Combined verification includes it, rather than
inferring correctness from targeted checks. The shared compiler window was
coordinated; no competing build or higher resource limit was introduced.

## Evidence and performance boundaries

- First-pass combined complete remote gates: `8a6ea5c`, run `39661212192`.
  Core `9a98e7e` independently passed run `39659979565`.
- Second-pass comment/guard/history checkpoint: `9622bd6`, complete CI run
  `39663411847`. Final combined source: `9fddbe7`, complete CI run `39823389597`,
  including constructive-arithmetic, distribution and full axiom gates.
- Combined local traversal: 989 planned modules, 16 rebuilt targets, complete
  native project build and 44,490-declaration transitive audit passed using the
  committed configuration. Maximum sampled aggregate RSS was 1113.2 MiB;
  longest invocation 5.07 seconds. These are cache-reusing incremental results,
  not a cold benchmark. Logs: `.lake/local-builds-v1/20261022-193121-17cinc87/`.
- All 111 helper/source tests pass on the combined source. All 906 baseline
  module paths remain (including the root facade); all 253 example modules
  are audit-reachable. The 990-module source graph is acyclic. Only the two
  separately enforced audit modules lie outside the general audit's imports.
- Complete core local traversal: 972 modules, 43,805 imported project declarations
  under the axiom policy; sampled peak 3801.9 MiB. Logs:
  `.lake/local-builds-v1/20261021-210043-ppkvpaw1/`.
- Three actual cached native build/audit pairs: 1.585, 1.565, 1.601 seconds;
  median 1.585, sampled peak 87.5 MiB. Separate diagnostic preflights are not
  included. Logs: `.lake/refactor-native-warm-5dkvtvqn/`.
- Three cached monitored workflows: 16.560, 16.554, 17.128 seconds; median
  16.560. Logs: `.lake/refactor-monitored-warm-zg0fkfh9/`. This includes extra
  fingerprints, process sampling and per-target preflights; native commands
  do not claim those additional safeguards.
- Two regression files formerly exceeded 30 seconds. The preserved graph/engine
  computations now check in independent modules below that limit. This establishes
  bounded local feasibility/reuse, not a cold-build speedup.
- Representative closures: entropy 19→13; chain compilation 36→21;
  value refinement 39→19; channel counterexample 80→63; current positive
  completeness 181→177. Counts are not elapsed-time speedups.

Comparisons must name the revision, platform, toolchain and benchmark category.
No shared-cache cleaning or fabricated artifact freshness is allowed. Cold
verification and incremental proof elaboration are not inferred from warm
measurements. Further cold speedups are deliberately deferred, not claimed.

## Final receipt and frozen acceptance

The source checkpoint passed the complete helper/regression suite, ordinary
Lake build, full transitive axiom audit and both specialized remote audits.
All current, historical and example modules remain covered. This receipt's
commit must also pass exact CI before publication; a documentation-only change
does not authorize assuming that a different CI revision passed. The ordinary
native and monitored routes remain documented in [LOCAL_CHECKS.md](LOCAL_CHECKS.md).

After those receipt gates, freeze its exact commit and perform Pass 3 without
changing source, layout or documentation. Recheck the contract, complete coverage/policy,
documentation, native local builds, measurement claims and unrelated-work
preservation. Report acceptance in the final response and goal status rather
than editing this ledger during the read-only pass. A material failure leaves
the goal incomplete and requires explicit authorization for another working pass.

## New targeted maintenance goal, 2026-10-23

This is a separately authorized follow-up, not a fourth pass of the preceding
refactor. Its limits are two working passes plus frozen read-only acceptance,
two performance pilots, one optional large-module split, and three repairs per
validation failure. The user also requested consolidation of scattered Markdown.
This temporary ledger will join the consolidated operating guide; no permanent
additional progress document is intended.

| Stage | Evidence / affected contract | Status |
| --- | --- | --- |
| 1. Baseline | `4a29a2c2b6cb92e70e7be5a031b15d3718df83fe`, complete CI run `39929974016`; complete 1010-module local/native build and general audit passed in `.lake/local-builds-v1/20261023-112903-8oi3hufx/`. Both specialized audits passed separately in `.lake/local-builds-v1/20261023-113031-mc9mmv2q/`; all 111 helper tests passed. Newer published analytic-value work is retained, not changed or attributed to maintenance. Only the pre-existing PDF was dirty. | Verified for this revision (`4a29a2c`). |
| 2. Documentation | All five requested guides read. Proposed canonical layout: root README, `lean/AGENTS.md`, `lean/REFERENCE.md`, `lean/HISTORY.md`. The user authorized coordination with both ongoing agents; their documentation updates must be retained. | Pending. |
| 3A. Walk foundation | Moved only `Consecutive.mono` beside `Consecutive`, preserving its exact original statement/proof hash. Readout geometry imports that owner directly; its closure is 20→18 project modules, not a timing claim. All five affected prerequisite/target rebuilds passed locally (generic owner 1.16 s / 675.2 MiB; d-separation correctness 5.87 s / 979.0 MiB; readout 1.24 s / 712.9 MiB). All 112 helper tests pass. Complete changed-source CI/audits remain required. | Implemented, awaiting review. |
| 3B. Sampling helpers | Generic mass/count helpers in specialized reinforced-urn modules remain to be investigated and checked. | Pending. |
| 4. Performance | The two approved example pilots remain unstarted; historical times are not a new controlled benchmark. | Pending. |
| 5. Structure/sharing | No additional large-module split has been attempted. | Pending. |
| 6. Comments/navigation | Reconcile after the selected changes; preserve mathematical explanations and exact proof guards. | Pending. |
| 7. Verification/publication | Full changed-source gates and exact-commit CI remain required before publication. | Pending. |
