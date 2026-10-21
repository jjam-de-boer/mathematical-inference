# Lean refactoring: current ledger

The first working pass is published as `8a6ea5cbe30efe5559bd87d073ec8e5120445a14`.
Its [complete CI run](https://github.com/jjam-de-boer/mathematical-inference/actions/runs/39661212192)
passed before publication. **Pass 2 is in progress; final acceptance is not yet
established.** The detailed first-pass measurements, unsuccessful experiments,
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
been approved for deletion. The preceding goal turn made progress: it published
the verified combined checkpoint, rather than merely restating the plan.

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
| 1. Combined baseline | Reconfirmed published `8a6ea5c`, complete CI and concurrent modifications. The published merge retains newer entropy without changing the other agent's working files. | Verified for this revision (`8a6ea5c`). |
| 2. Mathematical/API inventory | Rechecked source preservation, support/model-class boundaries, public names/compatibility and counterfactual qualification. The current inventory explicitly includes newer entropy approximation/optimality results. No theorem removal or assumption change is justified. | Implemented, awaiting review. |
| 3. Documentation | Moved the verbatim running diary out of this current ledger. Corrected one remaining root-parity progress claim: the unrestricted pair is not itself positive or an original-outcome counterexample; completed channel completeness is separate. | Implemented, awaiting review. |
| 4. Foundations | Rechecked law/support and causal dependency guards, including all current causal implementations. Convenience/compatibility facades intentionally retain history, not current implementations. Keep the generic singleton-sum lemma in its shared family: another tiny file has no demonstrated benefit. | Implemented, awaiting review. |
| 5. History | Rechecked all three exact archived namespace bodies, compatibility facades and mandatory audit reachability. Valid current carrier end-results remain current even without callers. No additional relocation/deletion is justified. | Implemented, awaiting review. |
| 6. Performance | Rechecked measurement logs and scope: bounded incremental feasibility and warm workflow latency are established, not a universal twofold cold-build improvement. No new unmeasured optimization is justified. | Implemented, awaiting review. |
| 7. Layout | Rechecked coherent `Hedge`/`Historical`/example boundaries, acyclicity, old paths, and absence of production imports of examples. Keep established topic paths instead of a wholesale forwarding-file rename. | Implemented, awaiting review. |
| 8. Verification/publication | Reverify the comment/guard/ledger corrections, retain newer published main, publish only after exact combined gates pass, then freeze for acceptance. | Pending. |

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

The shared branch subsequently retained `16c9ec9` (the other agent's elementary
path/support extension) and merged published main as `7a86f99`. That concurrent
work is preserved, not claimed as a new result of this refactor. Final combined
verification must include it; this goal does not certify unpublished work from
targeted checks alone. No new local compiler is started while its existing full
verification owns the shared slot.

## Evidence and performance boundaries

- First-pass combined complete remote gates: `8a6ea5c`, run `39661212192`.
  Core `9a98e7e` independently passed run `39659979565`.
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

## Remaining gates and freeze

Run the complete helper/regression suite, ordinary Lake build, full transitive
axiom audit and the two specialized audits for the exact final checkpoint.
All current, historical and example modules must remain covered. The ordinary
native and monitored routes remain documented in [LOCAL_CHECKS.md](LOCAL_CHECKS.md).

After Pass 2, freeze an exact commit and perform Pass 3 without changing source,
layout or documentation. Recheck the contract, complete coverage/policy,
documentation, native local builds, measurement claims and unrelated-work
preservation. Report acceptance in the final response and goal status rather
than editing this ledger during the read-only pass. A material failure leaves
the goal incomplete and requires explicit authorization for another working pass.
