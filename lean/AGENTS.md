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
| 2. Documentation | Eight previous Markdown files become the root README and three co-located guides. Complete snapshots retain their original hashes; live links resolve. Source references and exact historical body guards are updated. Both agents were contacted with authorization. Newer published auxiliary-value documentation must be reconciled when combining main. | Implemented, awaiting combined-checkpoint review. |
| 3A. Walk foundation | Original lemma bodies retained by exact hashes. Full local/native build and 44,917-declaration audit passed for repaired Lean source `1ab81d2` in `.lake/local-builds-v1/20261023-114435-rk5ikvpv/`. CI `39966131088` caught an old test parser including newly adjacent declarations; its exact original lemma hash is retained with a precise block boundary. Later comment changes require refreshed complete gates. | Implemented, awaiting review of combined checkpoint. |
| 3B. Sampling helpers | `FiniteRecordSums`, `Distros.CategoricalSampling` and categorical aggregation own the general helpers; nine original bodies are hash-preserved. Positive witnesses reuse the existing support theorem, with old public wrappers retained. Repair 1 supplies the direct categorical-aggregation owner. The complete 214-module distro closure and specialized audit passed in `.lake/local-builds-v1/20261023-161413-lzmvl8o5/`. DepletingUrn's closure falls 54→49; legitimate reinforced moments remain. | Implemented, awaiting complete combined gates. |
| 4. Performance | Both bounded pilots completed. LatentCollider proof reuse gave no improvement and was restored exactly. CompensatedReadout fresh checks improved from 20.5–20.9s to 10.6–11.5s, with similar memory; assertions are hash-preserved. Detailed source/cache/category evidence is in history. No overall cold-build speedup is claimed. | Implemented, awaiting complete combined gates. |
| 5. Structure/sharing | No optional large split: measured cost lay in small computational fixtures, not the 9,674-line SoundnessRules module (historically about 4.4s). Its private Boolean helpers cross rule boundaries. D-separation's demonstrated generic extraction and the two narrowly owned sampling modules supply concrete boundaries; an additional Models split has no demonstrated current-client dependency benefit. | Implemented, awaiting pass-2 reconsideration. |
| 6. Comments/navigation | Corrected the root-flow owner, historical facade links and helper ownership. New foundation headers explain zero/support requirements and reading order. Exact comment substitutions retain the original protected proof hashes. Recheck after combining newer main. | Implemented, awaiting pass-2 review. |
| 7. Verification/publication | Walk extraction `5a0803f` and repaired source `1ab81d2` are on the verification branch, not main. The subsequent consolidation/sampling/pilot checkpoint passes 121 helper tests and targeted checks; complete exact-revision local and remote gates remain required before publication. | Implemented, awaiting complete gates. |

Working pass 1 is in progress. Working pass 2 must revisit every stage once;
then freeze an exact verified checkpoint for read-only acceptance. Do not mark
the goal complete merely because the first useful extraction or doc move passed.
