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

### Separating import cost from new kernel work

Five small fixtures were checked sequentially on 2026-10-16 under the
unchanged one-thread, 384 MB allocation, 768 MiB sampled-RSS and 30-second
limits. Each core-based check first validated its copied dependency trace;
no prerequisite was rebuilt and all trial outputs remained disposable.

| Fixture | New work after imports | Selected wall time | Child peak | Result |
| --- | --- | --- | --- | --- |
| `LocalCheckImports` | None, `Std` only | 1.51 s | 572.6 MiB | Passed |
| `LocalCheckCoreImports` | None, cached probability core | 0.55 s | 573.3 MiB | Passed |
| `LocalCheckBaseline` | Apply the existing reflexivity theorem | 0.44 s | 580.4 MiB | Passed |
| `LocalCheckDefinition` | A tiny natural-number recursive definition | 0.44 s | 575.9 MiB | Kernel allocation limit |
| `LocalCheckFiniteDecision` | Exhaustive proof on `Fin 4` | 0.44 s | 574.7 MiB | Kernel allocation limit |

The core cache checks took 0.19--0.45 seconds and about 52 MiB child peak.
The table's peaks are the helper's cumulative child-peak measurements within
each invocation; sampled RSS is a distinct measurement. No sampled-RSS or
wall-time stop occurred, no children overlapped, and no limit was increased.

These results distinguish importing from checking new terms: the imported
environment is loadable, and a reused proof term can pass, while ordinary
small new definitions or finite kernel decisions already fail. The installed
compiler source confirms that the forwarded `-M` argument sets its internal
runtime memory threshold in units of 1024 squared bytes. It is not an OS RSS
reservation or a separate fresh allowance for each declaration. Similar RSS
figures alone do not identify the kernel's precise allocation accounting.

Thus neither module source size nor finite proof-search size explains the
whole observed boundary. A targeted graph extraction can still reduce
dependency scope, but is not established as a way past this earlier limit.
Import-only and reused-proof checks are feasible at these settings; larger
new proof work and the full project remain remote. The fixtures themselves
are included in CI and the full axiom gate so a local resource refusal never
stands in for mathematical verification.

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

### Targeted graph extraction, not a local-memory claim

`Causality.ComponentConnectivity` now contains the shared connectivity and
partition facts; `Causality.IdentificationRank` contains the shared structural
rank. Their shared finite-walk foundation has also moved from the start of
`DSeparationCorrectness` into intrinsic `Causality.ReachabilityCorrectness`.
The generic relation-list predicate retains its historical
`PathSpecification.Consecutive` name, without importing the graph-specific
active-path layer. This extra prerequisite was exposed by the first targeted
remote check; importing the old transport module would defeat the boundary.

The component/rank extraction retains 579 original lines, with unchanged theorem
statements and proof bodies, apart from moving their enclosing module and
documenting the new dependency boundary. The additional generic-walk extraction
retains 823 original lines on the same basis. `Completeness` imports the new
layer, so its existing consumers still see the same public names. Forest
constructors and historical trace inductions remain in their original module.
Two further shared empty-conditioner rule-3 graph identities (36 original
lines) now live with the path specification in `DSeparation`, not in the
historical completeness development. Their statements and proof bodies are
unchanged as well; a downstream current-recursion client exposed that need.

Retargeting the two current-engine clients gives the following source-graph
comparison (target included; Lean/Std modules excluded):

| Client | Before extraction | After extraction |
| --- | --- | --- |
| `CausalTransport.KernelIdentification` | 26 | 20 |
| `CausalTransport.KernelSeparation` | 25 | 20 |

Both clients lose the direct dependency on the approximately 42k-line module
and its legacy trace imports. The separation client still explicitly imports
`DSeparationCorrectness`: its ancestry and moral-path arguments genuinely need
that graph-specific theorem layer, not just bidirected connectivity. Two
source-graph regression tests protect this
boundary and ensure the intrinsic layers do not import causal transport.
CI checks the extracted modules and both clients early, then still runs the
complete project and the unchanged transitive axiom gate.

No broad soundness/completeness split is performed. The approved local pilot
stops much earlier in the small `FiniteRecord` prerequisite, and even a tiny
new definition after the cached core reaches the allocation boundary. This
targeted dependency improvement has no demonstrated ability to cure that
earlier limit. The
remote cold/import-change build recorded completeness at 37 seconds; the
18-second soundness attempt failed on a missing import, so it is not a valid
successful-build timing. Once cached dependencies were available, checkpoint
`733b5f3` completed its full-build step in 7 seconds and its separate axiom
gate in 25 seconds. These are CI wall times, not local peak-memory measurements.

Probability algebra in `Soundness` remains a possible later extraction. It
would need separate dependency/resource measurements, private-helper review,
a complete build and axiom audit. Neither that work nor the graph extraction
is a repair to the mathematical theorem or an established local-memory cure.

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
