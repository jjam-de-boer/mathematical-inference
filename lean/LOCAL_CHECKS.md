# Resource-capped local checks

Full project builds and the transitive axiom audit currently remain remote.
The previous laptop freeze has not been diagnosed; faster endpoint arithmetic
does not establish that full proof elaboration fits local memory.

## Cache-aware pilot

The cache-aware helper requires Python 3.11 or newer. Its default operation
only prints a plan; compilation requires the explicit `--check` option:

```sh
python3 -B lean/tools/check_module_cached.py Thesis.Probability.FourLabelTransportation
python3 -B lean/tools/check_module_cached.py Thesis.Probability.FourLabelTransportation --check
```

The helper snapshots the bounded source closure, the reviewed declarative
package configuration and the required local dependency artifacts into a
disposable directory. Lake checks those copied dependencies with `--no-build`,
`--rehash` and `--no-cache`. An outdated or missing dependency is a failure,
not permission to rebuild it. Only explicitly selected source modules are
then compiled, sequentially, using the pinned installed toolchain. The shared
source tree and `.lake` cache are never overwritten, and a source change
during the pilot invalidates its final result.

The default limits remain 384 MB of Lean allocation and 30 seconds per child.
An additional watchdog samples the child's RSS, stopping above 768 MiB.
Sampling permission is checked before a compiler or Lake child is launched;
if the sandbox denies that inspection, the helper stops. This is a sampled
watchdog, not a hard OS memory reservation or a guarantee against all system
pressure. No allocation-limit increase is automatic. The accepted maximum is
512 MB, but the recorded second trial below was separately authorized.

The closure is limited to six modules by default, at most 128 KiB per source,
512 KiB combined source and 64 MiB of copied cache artifacts. One module is
selected for compilation by default. Up to three must be explicitly enabled
and named for a sequential multi-module experiment. The helper deliberately
rejects external packages, package hooks, ambient Lean search paths and
unsupported module/header formats. It does not install toolchains or fetch
dependencies. Successful pilot output certifies only the selected elaboration,
not the full build or project-wide axiom audit.

### Measured cache-aware results, 2026-10-16

The existing macOS/ARM probability-core artifacts passed Lake's freshness
check in the disposable workspace: approximately 0.3–0.6 seconds and 52 MiB
child peak. Thus that dependency really can be reused; it was not rebuilt.

The selected `FourLabelTransportation` module then stopped at Lean's memory
limit in `label_cases`, before later transportation proofs were checked:

| Lean allocation setting | Selected-module wall time | Reported child peak | Result |
| --- | --- | --- | --- |
| 384 MB | 1.21 s | 579.8 MiB | Allocation limit reached |
| 512 MB, separately authorized | 1.22 s | 581.0 MiB | Allocation limit reached |

Both used the same 768 MiB sampled-RSS watchdog and 30-second wall timeout.
Neither is a successful module check. The measurements show that validated
cache reuse works, but do not establish that this module fits the approved
allocation range, that a full build fits the laptop, or that splitting the
large soundness/completeness files would solve this much earlier boundary.
There was no further limit increase or unrestricted local build.

The separate `Thesis.Examples.LocalCheckBaseline` fixture then passed at the
original 384 MB setting: 1.40 seconds and approximately 579.6 MiB child peak.
It only imports the same validated core and applies probability reflexivity;
it does not decide a finite quantified proposition or check transportation.
This is a genuine small local success, but must not be reported as a successful
transportation check. Similar process RSS does not imply identical Lean
allocation behaviour or proof-checking demands.

A subsequent sequential attempt to check the new presentation adapter could
reuse the cached core, permutation, finite-cell-product and urn dependencies
(about 0.37 seconds and 53.8 MiB). It stopped in the first selected prerequisite,
`FiniteRecord`, at the unchanged 384 MB allocation cap: 1.47 seconds and
approximately 592.1 MiB child peak. Neither `Construction` nor the new adapter
was reached. This is a resource-limit result, not an adapter proof result;
those proofs are checked remotely. No further 512 MB trial was made.

The helper safety regressions can be run without invoking Lean:

```sh
python3 -B -m unittest discover -s lean/tools -p 'test_*.py'
```

## Import narrowing and the proof-module split decision

`Causality.Model` now imports `Probability.Construction`, not the complete
`Probability` facade. Consumers that need further probability theorems import
their owning modules directly; finite-function regression decisions declare
their own constructive equality instances. This preserves the public theorem
names without making basic causal models import every named distribution.

For the source graph at checkpoint `8a976d0`, the following counts include
the target and its transitive `Thesis` dependencies, not Lean/Std modules.
The comparison restores only Model's former facade import in that same graph;
it is a reproducible dependency comparison, not a historical runtime benchmark.

| Target | Former facade edge | Narrow imports |
| --- | --- | --- |
| `Causality.Model` | 149 | 8 |
| `CausalTransport.HiddenDAGModel` | 156 | 15 |
| `CausalTransport.HiddenDAGSoundness` | 169 | 29 |
| `CausalTransport.HiddenDAGCorrespondence` | 313 | 195 |
| `CausalTransport.HiddenDAGPolynomialEvidence` | 160 | 51 |

Each inspected path loses 72 distribution modules. These counts do not imply
the same reduction in compiled memory or elapsed build time.

All 191 example modules at that checkpoint are reachable from the full
`Thesis.AxiomAudit` import closure, including the three formerly orphaned
regressions. `tools/test_example_coverage.py` guards this source-level coverage
in CI without launching Lean. It does not replace actual elaboration or the
transitive axiom audit.

No broad soundness/completeness split is performed in this stage. Their source
files remain large (roughly 20k and 42k lines), but the approved local pilot
stops much earlier in the small `FiniteRecord` prerequisite. Splitting later
files therefore has no demonstrated ability to make that pilot pass. The
remote cold/import-change build recorded completeness at 37 seconds; the
18-second soundness attempt failed on a missing import, so it is not a valid
successful-build timing. Once cached dependencies were available, checkpoint
`733b5f3` completed its full-build step in 7 seconds and its separate axiom
gate in 25 seconds. These are CI wall times, not local peak-memory measurements.

A future targeted extraction could separate graph-only c-component geometry
and recursion-rank lemmas from `Completeness`, then retarget current-kernel
clients to the small module while retaining the old public facade. Probability
algebra in `Soundness` is another candidate. Either needs its own dependency
and resource measurements, private-helper review, complete build and axiom
audit. Neither is needed to repair a mathematical theorem or justified as a
local-memory cure by the present measurements. Keeping this conditional work
deferred avoids a high-churn reorganization unsupported by the pilot.

## Fresh-closure pilot

For an explicitly small source closure, an opt-in pilot is available:

```sh
python3 lean/tools/check_module_capped.py Thesis.Probability.FourLabelTransportation
```

It uses the installed toolchain pinned in `lean/lean-toolchain`, never installs
anything, never launches Lake, and checks project dependencies sequentially
into a disposable directory. It does not reuse possibly stale project caches.
Default per-child limits are one compiler thread, Lean's 384 MB memory setting,
30 seconds wall time, and a separate CPU-time limit. Source size and closure
size are also bounded. Low-priority scheduling is requested where permitted.
The helper's accepted import-header syntax is intentionally restricted.

Lean's memory setting is **not an OS-wide RSS limit**. Imported runtime/library
memory can make the reported process peak exceed it. The helper reports the
maximum child peak seen during the invocation; it is not a system-memory or
swap monitor. Lean's `-T` option counts allocations, not wall-clock seconds;
the actual wall-clock watchdog is supplied by the helper instead.

The initial macOS pilot on 2026-10-15 stopped in the existing probability core
at the memory limit, before transportation was checked. Reported child peak
was approximately 609 MiB and elapsed time less than a second. The sandbox
denied low-priority scheduling. No cap increase or full local build followed.
This is evidence that these conservative settings do not suffice even for
this closure, **not** evidence of a source proof error or a safe full build.

Remote CI reuses dependency artifacts but still runs the targeted build,
complete `lake build`, and `lake build Thesis.AxiomAudit`. Only successful
checks for the exact source commit establish those gates. A cap failure is
never a successful verification or permission to bypass the audit.
