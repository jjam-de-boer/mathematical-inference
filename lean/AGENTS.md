# Lean project instructions

These instructions apply to `lean/`. Respect the user's instructions and any
more specific applicable instructions. Read the relevant source before editing;
do not infer correctness from a theorem name or an old green checkpoint.

## Mathematical contract

- Probability laws are finite rational records. Preserve zero masses, repeated
  labels, unreduced presentations and explicit support requirements.
- Preserve public theorem statements, assumptions, computational guarantees,
  declaration namespaces and original defining-module import compatibility.
- Permitted transitive kernel axioms are only `propext` and `Quot.sound`.
  No choice, general excluded middle, `sorryAx`, `Lean.ofReduceBool` or new
  assumed axiom is allowed. Finite supplied decidability and Boolean/Nat case
  analysis are not general propositional excluded middle.
- Preserve distributions/entropy, joint and conditional causal results, original
  hidden-DAG transfer, modal integration and established extensions with their
  precise qualifications. A result without callers is not thereby obsolete.
- Historical results and regression assertions remain built and audited.
  Never weaken or skip them to make a build faster.
- Existing auxiliary analytic-value work remains separate from rational atom
  weights. Preserve it; maintenance does not authorize extending its mathematics.
  Separately authorized research tasks keep their own mathematical scope.

## Documentation and source navigation

Keep documentation consolidated in three files here:

- `AGENTS.md`: operating policy, current commands and maintenance ledger.
- [REFERENCE.md](REFERENCE.md): current mathematical coverage and reading order.
- [HISTORY.md](HISTORY.md): preserved historical evidence and old guide snapshots.

The repository-root README is the short entry point. Do not recreate the old
scattered guides or add another progress Markdown without a concrete user need.
Update the relevant canonical section rather than duplicating a status report.
History is evidence, not current instructions or authorization for new work.

Current production modules should import focused mathematical owners, not broad
compatibility facades. Keep graph/probability foundations below semantic proof
assemblies; do not import examples as production foundations. Preserve old
public import paths when moving an implementation. Historical facades may
retain their deliberate broader surface without becoming current dependencies.

Comments should explain mathematical role, hypotheses, invariants, constructive
data and the relationship to completed results. Preserve substantive reasoning.
Replace stale progress or positional references; verbosity alone is not clarity.

## Builds and checks

Use the pinned installed toolchain. From the repository root:

```sh
python3 -B -m unittest discover -s lean/tools -p 'test_*.py'
```

Ordinary native commands need no Python prerequisite:

```sh
cd lean
export LEAN_NUM_THREADS=1
lake build
lake build Thesis.AxiomAudit
lake build Thesis.ConstructiveAlgebraAudit
lake build Thesis.DistroAxiomAudit
```

`LEAN_NUM_THREADS=1` serializes Lake workers. The committed `-j1` separately
limits each Lean compiler; it does not by itself serialize Lake jobs.
The committed `-M4608` is a Lean memory threshold, not an OS reservation.
Native Lake does not provide a whole-process-group watchdog or wall-time stop.

The optional monitored complete route, from the repository root, is:

```sh
python3 -B lean/tools/build_local_sequential.py --profile extended --check
```

For a targeted, prerequisite-first check:

```sh
python3 -B lean/tools/build_local_sequential.py --profile extended --phase lean --target Thesis.CausalTransport.Soundness --check
```

The approved full-builder profile retains one compiler family, a 4608 MiB Lean
threshold, a 5120 MiB sampled aggregate-RSS watchdog, low priority and 30 seconds
per invocation. Smaller helper profiles are not sufficient for every module.
No automatic promotion after a refusal is allowed. Acquire the shared compiler
slot and avoid competing manual or editor builds. Do not raise limits, delete
the shared cache, or terminate another agent's compiler without authorization.

Lake's genuine source/dependency traces determine reuse. Never relabel a pilot
artifact as a successful ordinary Lake result. A target or intermediate phase
success is not a complete-project result. The full-builder success banner
confirms its actual native build and full audit gates; the two specialized
audits remain explicit verification targets as well.

Before publication, run the complete build, full transitive audit, specialized
audits and helper tests for the exact checkpoint. Inspect the final diff.
Publish a verified checkpoint from the verification branch to main without
force-pushing over newer work. Preserve concurrent changes and unrelated PDFs.

## Measurements and preservation

Name the source revision, toolchain, platform, cache state and benchmark category.
Distinguish warm verification, fresh selected-module checking, representative
incremental rebuilds and cold builds. Dependency/job counts are not timings.
A split's per-invocation headroom is not automatically a total speedup.
Sampled RSS can miss a short peak and does not guarantee machine responsiveness.

Source/dependency guards supplement Lean checking; they do not replace it.
For hash-protected comment changes, establish that only the exact documented
comment changed. Do not normalize proof text or weaken a policy gate to pass.
Preserved guide snapshots and original body hashes are in `HISTORY.md`.

## Targeted maintenance ledger

This section concerns the separately authorized goal begun on 2026-10-23,
not other agents' separately authorized mathematical work. Limits: two working
passes plus frozen read-only acceptance; at most two performance pilots, one
optional additional large-module split and three repair attempts per failing
validation. A material failure during frozen acceptance requires reporting
incomplete work and requesting authorization before another editing pass.

Statuses: Pending; Implemented, awaiting review; Verified for this revision;
Blocked or incomplete. Checks belong to their exact source revision.

| Stage | Evidence and affected contract | Status |
| --- | --- | --- |
| 1. Baseline | `4a29a2c2b6cb92e70e7be5a031b15d3718df83fe`: complete CI run `39929974016`; complete 1010-module local/native traversal and 44,917-declaration audit passed in `.lake/local-builds-v1/20261023-112903-8oi3hufx/`. Both specialized audits passed in `.lake/local-builds-v1/20261023-113031-mc9mmv2q/`; all 111 baseline helper tests passed. Only the pre-existing PDF was dirty. | Verified for this revision (`4a29a2c`). |
| 2. Documentation | Eight previous Markdown files become the root README and three co-located guides. Nine original/version snapshots retain exact hashes; live links resolve. Newer published auxiliary-value results through `22fd3b9` are reconciled. Both agents were contacted with authorization. | Verified for source release `cac0a69`; pass-2 heading/ledger corrections are documentation only. |
| 3A. Walk foundation | Eleven original bodies retain exact hashes and old defining-import compatibility. Two downstream ownership repairs and one test-boundary repair are recorded; the original hash was never replaced to hide changed proof text. ReadoutGeometry's closure is 20→18 with no d-separation-correctness dependency. Complete release gates pass. | Verified for `cac0a69`. |
| 3B. Sampling helpers | `FiniteRecordSums`, `Distros.CategoricalSampling` and categorical aggregation own the general helpers; nine original bodies are hash-preserved. Positive witnesses reuse the existing support theorem, retaining old wrappers. Repair 1 supplies direct categorical aggregation. DepletingUrn's closure is 54→49; legitimate reinforced moments remain. | Verified for `cac0a69`, including the specialized audit and all direct clients. |
| 4. Performance | Both bounded pilots completed. LatentCollider gave no improvement and was restored exactly. CompensatedReadout fresh checks improved from 20.5–20.9s to 10.6–11.5s; pass 2 confirms 10.297s at 2860 MiB. Assertions remain hash-preserved. Detailed categories and source evidence are in history; no overall cold-build speedup is claimed. | Verified for `cac0a69`; one retained optimization and one documented negative result. |
| 5. Structure/sharing | No optional large split: small computational fixtures dominated the retained measurements; SoundnessRules historically took about 4.4s and private Boolean helpers cross rule boundaries. Pass 2 reconfirms the focused generic owners and reading map are useful; another Models split has no demonstrated current-client benefit. | Verified decision for `cac0a69`; zero additional large splits attempted. |
| 6. Comments/navigation | Root-flow ownership, historical facade links and helper ownership are corrected. New headers explain assumptions, computational data and reading order. Pass 2 checks direct clients and standardizes reference heading capitalization; exact protected source-comment substitutions remain explicit. | Verified source review for `cac0a69`; heading corrections are documentation only. |
| 7. Verification/publication | Release `cac0a69` is on main after a complete 1048-module local/native traversal, 45,404-declaration audit, both specialized audits, 122 helper tests and successful full CI `39971865646`. Local receipts: `.lake/local-builds-v1/20261023-164205-m1bcj247/` and `20261023-164331-s8vko2kg/`. | Verified for `cac0a69`; the documentation-only acceptance candidate must pass the same final gates. |

## Mandatory second-pass reconsideration

Every stage was revisited once after the verified first-pass release:

| Stage | Reconsideration and result |
| --- | --- |
| 1 | Combined newer main rather than reset it. Exact release gates above pass; the pre-existing PDF digest is unchanged. |
| 2 | Rechecked all nine archived versions, live links and theorem qualifications. Corrected only stale ledger status and heading capitalization. |
| 3 | Rechecked import closures, old defining imports, twenty exact moved bodies and the simpler support wrapper. No further proof or ownership edit is needed. |
| 4 | Remeasured the same retained pilot against final validated dependencies: 10.297s / 2860 MiB. The failed pilot remains restored; no third optimization pilot was started. |
| 5 | Reconsidered private cross-rule helpers, responsibility boundaries and recorded costs. No further module/folder split is justified. |
| 6 | Reread touched foundations and direct clients. Source comments remain accurate; current/reference/history roles remain separate. |
| 7 | Rechecked all 122 helpers and preserved current, historical and example coverage. Diagnostic comparison retains 599 original theorem headers and 157 computational/structure blocks; no mathematical source changed in pass 2. |

The commit containing this second-pass ledger is the frozen acceptance
candidate. Its only changes from `cac0a69` are these consolidated documents.
Run final acceptance read-only: complete native build, all audits, regressions,
link/history guards and exact remote CI, then publish that verified revision.
Record the acceptance outcome in Git/CI receipts and the user report rather
than editing this ledger during acceptance. A material failure requires explicit
authorization for another working pass; do not silently begin a third pass.
