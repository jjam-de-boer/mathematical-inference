# Resource-capped local checks

Full project builds and the transitive axiom audit currently remain remote;
the normal-cache sequential bootstrap described below is being verified.
Useful selected-module checking is feasible under the conservative
640 MiB Lean / 768 MiB sampled-RSS / 30-second single-process profile below;
the explicit 768/1024 MiB pilot also checks downstream transportation modules.
The previous laptop-wide freeze has not been diagnosed; this result does not
establish that full proof elaboration fits local memory.

## Full-project sequential bootstrap (in progress)

`tools/build_local_sequential.py` is separate from the small-closure pilot.
It walks the actual default executable and full axiom-audit dependencies,
asks Lake to build prerequisite-first, and retains genuine ordinary artifacts
and traces in `.lake/build`. It never copies a pilot `.olean` into that cache
or invents a successful trace. Intermediate successes are resumable, not a
claim that the full project builds.

```sh
python3 -B lean/tools/build_local_sequential.py
python3 -B lean/tools/build_local_sequential.py --phase lean --max-builds 20 --check
python3 -B lean/tools/build_local_sequential.py --check
```

The first command only plans. The second is an optional checkpoint after 20
actual rebuilt modules; it returns a distinct checkpoint exit code, not full
success. Repeating it resumes using Lake freshness checks. The third attempts
all Lean modules, native object files, the actual complete build and the full
axiom audit. Only its explicit final gate result establishes end-to-end local
success; a passed `--target` or individual `--phase` does not.

The default explicit full-builder profile is 768 MiB Lean, 1024 MiB aggregate
sampled RSS and 30 seconds per invocation. A temporary declarative TOML file
adds only weak resource arguments (`-j1`, `-M768`, `-DmaxErrors=1`), which this
pinned Lake excludes from proof traces. The committed configuration is not
edited. The whole owned process group is monitored, including compiler and
linker children; its aggregate RSS deliberately counts shared resident pages
conservatively. Independent compiler families, unmonitorable children, source
changes and resource overruns stop the build. Wall/CPU stops are distinguished
from Lean's memory-threshold failures. Final commands use the original package
configuration, with a no-build preflight before those commands can run.

The original million-unit `uniform_margins` regression is now proved by a
private symbolic lemma for every natural mass, then specialized to the same
concrete total. Every original statement and numerical test remains. Its
direct cached check passed in 1.26 s (596.2 MiB invocation child peak). The
normal-cache seven-module transportation closure then passed sequentially;
its reservation rebuild sampled 725.4 MiB for Lake plus its compiler, and
the regression itself sampled 633.4 MiB. The unmodified package configuration
subsequently reported all eight targets up to date in 0.27 s, without rebuilding.
These establish real normal-cache integration, not yet the complete project.

The subsequent full-graph bootstrap rebuilt its first 20 missing/stale targets
at the pilot profile, then resumed through module 113. `BetaBinomialMoments`
reached Lean's 768 MiB threshold in `betaBinomial_secondMoment`. A separately
selected ceiling-profile run passed that unchanged module in 2.74 s with
884.3 MiB sampled aggregate RSS. No distribution theorem was altered. The
combined checkout now also contains main's newer distribution modules; its
full Lean/audit closure has 836 project modules at this checkpoint. Continuing
that bootstrap uses the explicit ceiling profile, not an automatic retry and
not a claim that every target fits the pilot profile:

```sh
python3 -B lean/tools/build_local_sequential.py --phase lean --profile ceiling --check
```

The large-proof stage then passed `DSeparationCorrectness` in 6.12 s with
977.4 MiB sampled aggregate RSS. The unsplit `Soundness` stopped around line
9740 at Lean's 1024 MiB threshold (6.16 s; 1090.8 MiB sampled group RSS); this
was a memory result, not a timeout or a mathematical counterexample.

Soundness is now extracted into `SoundnessFoundations`, `SoundnessRegions`,
`SoundnessRules` and the original public `Soundness` assembler. Every original
declaration's statement and proof script is retained byte-for-byte. Three
independent point-mass/product lemmas move alongside their private enumeration
helpers; all private helpers remain contained in their owning file, rather
than being exposed or duplicated across module boundaries. Existing public
names/imports are retained. The original unsplit source at `851b231` has
SHA-256 `93c7040fd9662e837483b85e24cb663e400383008298734d61618f8c50ff021f`;
the extraction's source partition was checked to reassemble it exactly.

All four resulting ordinary Lake targets passed sequentially at the ceiling:

| Soundness layer | Wall time | Sampled aggregate RSS |
| --- | --- | --- |
| Foundations | 2.79 s | 856.9 MiB |
| Regions | 2.64 s | 828.7 MiB |
| Rules | 4.44 s | 944.4 MiB |
| Public assembly | 0.70 s | 690.1 MiB |

The main import still certifies the same published soundness result. This
successful local target is a measured repair to the observed compilation
boundary, not yet evidence that the entire project or audit fits locally.

No larger memory or timeout setting is an automatic retry. Unrelated editor
or manual compiler processes are not terminated. Machine-wide headroom still
matters, especially on this machine while other applications retain swap.

## Transportation split and explicit resource profiles, 2026-10-19

The machine reports 18 GiB physical RAM and 11 CPU cores. At the assessment
snapshot, swap usage was zero and the system memory-pressure free metric was
79%. That pressure metric is not a count of unused physical RAM, and this
snapshot is not a permanent reservation or a guarantee against another freeze.
Only one compiler is allowed through the helpers' shared OS lock; unrelated
manual builds are not controlled by it. Both helpers now use the same monitor,
CPU/wall bounds and explicit profiles:

| Profile | Lean resident-memory threshold | Sampled child-RSS watchdog |
| --- | --- | --- |
| `conservative` (default) | 640 MiB | 768 MiB |
| `pilot` (explicit) | 768 MiB | 1024 MiB |
| `ceiling` (explicit upper trial) | 1024 MiB | 1280 MiB |

Every profile retains one compiler thread and a 30-second per-child timeout.
There is no automatic retry or promotion after failure. The ceiling is a
reviewed trial boundary, not a measured hardware maximum or permission for
parallel/full-project local builds. Source/closure/artifact bounds remain in
force. A sampled watchdog can miss a short peak; Lean's periodic internal
check is not an exact OS-enforced ceiling either.

`FourLabelTransportationConstruction` now owns the data, finite eligible-edge
search, supporting lemmas and `transport`. `FourLabelTransportation` imports
it and retains `transportation_capacity` and `transportation_exists_iff`.
All public names stay in `Thesis.Probability.FourLabelTransportation`, and
existing imports still re-export them. The extraction was compared against
checkpoint `2a87623`: both the construction body (from `abbrev Masses` through
`transport`) and the final two theorems are byte-for-byte unchanged. Only
module ownership/imports/documentation changed; zero totals, unbounded natural
weights and the separate batched algorithm retain their original meaning.
Source regressions guard the public boundary and full audit import coverage;
they do not replace Lean checking or the transitive axiom audit.

Actual sequential checks, with no overlapping compiler, gave:

| Check | Profile | Outcome and measurements |
| --- | --- | --- |
| Fresh Core, construction, final theorems | 640/768 | All passed; 2.36 s, 1.17 s, 0.87 s; invocation child peak 653.3 MiB |
| Cached construction and final theorems | 640/768 | Passed and retained; 2.08 s and 0.73 s; invocation child peak 633.9 MiB |
| Original small transportation example via unchanged import | 640/768 | Passed in 0.52 s after sequential split checks; invocation child peak 634.3 MiB |
| Fresh closure through reservation, batching and cell extrema | 768/1024 | All six library modules passed; reservation 2.37 s; invocation child peak 667.6 MiB before regression |
| Cached construction, final theorems, reservation | 768/1024 | Passed and retained; 1.14 s, 0.67 s, 2.21 s; invocation child peak 697.1 MiB |
| Cached batching, cell extrema, joint extrema | 768/1024 | Passed and retained; 0.63 s, 0.42 s, 0.50 s; invocation child peak 602.6 MiB |
| Unchanged retained joint-extrema client | 768/1024 | Reused without re-elaboration; ordinary Core trace check 0.21 s |
| Forced joint-extrema recheck with retained prerequisites | 768/1024 | Re-elaborated and passed; 1.34 s; invocation child peak 600.0 MiB |
| `Examples.FourLabelTransportationBatched` after fresh prerequisites | 768/1024 | Lean threshold at `uniform_margins`, 2.03 s; invocation child peak 768.2 MiB |
| Same fresh regression at upper trial | 1024/1280 | Same threshold failure, 4.25 s; invocation child peak 1024.2 MiB |

Reported child peaks are cumulative maxima across children within each helper
invocation, not separate exact per-module peaks or fresh proof-allocation
budgets. The 640 MiB fresh run's 653.3 MiB reported peak is consistent with
Lean's periodic check; no sampled watchdog was hit. These profiles are bounds
on checked runs, not claims of exact memory use.

The remaining large regression stops in the proof of the million-unit uniform
margins (line 38), before its later uniform-table computation is established.
The preceding billion-unit single-cell regression was reached without a
reported error. Thus this result must not be described as either a successful
whole regression or proof that the batching algorithm itself needs over 1 GiB.
No theorem, regression or kernel decision was removed/weakened to make the
local result green. The full project and these larger regressions still need
remote verification.

For a reusable local development loop, explicitly seed changed prerequisites
in small sequential batches, then check only the edited client:

```sh
python3 -B lean/tools/check_module_cached.py Thesis.Probability.FourLabelTransportationConstruction Thesis.Probability.FourLabelTransportation Thesis.Probability.FourLabelTransportationReservation --profile pilot --max-selected 3 --check --retain
python3 -B lean/tools/check_module_cached.py Thesis.Probability.FourLabelTransportationBatched Thesis.Probability.FourLabelTransportationExtrema Thesis.Probability.FourLabelTransportationJointExtrema --profile pilot --max-selected 3 --max-modules 8 --check --retain
python3 -B lean/tools/check_module_cached.py Thesis.Probability.FourLabelTransportationJointExtrema --profile pilot --max-modules 8 --check --retain
```

The last command reports reuse for unchanged inputs; add `--force-check` to
re-elaborate the selected client. This was tested separately, not inferred
from cache reuse. Inputs include the memory/compiler settings, so a checked
artifact from one profile is not silently reused as a check at another.
Changing the helper itself also invalidates its retained entries. These
artifacts stay separate from ordinary Lake output, which is never overwritten
by either helper. Full `lake build` and `Thesis.AxiomAudit` remain remote gates.

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
source tree and ordinary Lake build artifacts are never overwritten, and a
source change during the pilot invalidates its final result. The optional
separate retained store is described below; every actual check also holds an
OS lock so two invocations of this helper cannot overlap their compilers.

At the time of the initial measurements below, the default limits were a
384 MiB Lean memory threshold and 30 seconds per child.
An additional watchdog samples the child's RSS, stopping above 768 MiB.
Sampling permission is checked before a compiler or Lake child is launched;
if the sandbox denies that inspection, the helper stops. This is a sampled
watchdog, not a hard OS memory reservation or a guarantee against all system
pressure. No memory-limit increase is automatic. The accepted maximum was
640 MiB at that checkpoint, with values above the default requiring explicit
selection. The earlier
512 MB trial and the later 640 MiB diagnostic were separately authorized.

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

| Lean `-M` setting | Selected-module wall time | Reported child peak | Result |
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
unchanged one-thread, 384 MiB Lean threshold, 768 MiB sampled-RSS and 30-second
limits. Each core-based check first validated its copied dependency trace;
no prerequisite was rebuilt and all trial outputs remained disposable.

| Fixture | New work after imports | Selected wall time | Child peak | Result |
| --- | --- | --- | --- | --- |
| `LocalCheckImports` | None, `Std` only | 1.51 s | 572.6 MiB | Passed |
| `LocalCheckCoreImports` | None, cached probability core | 0.55 s | 573.3 MiB | Passed |
| `LocalCheckBaseline` | Apply the existing reflexivity theorem | 0.44 s | 580.4 MiB | Passed |
| `LocalCheckDefinition` | A tiny natural-number recursive definition | 0.44 s | 575.9 MiB | Lean memory threshold |
| `LocalCheckFiniteDecision` | Exhaustive proof on `Fin 4` | 0.44 s | 574.7 MiB | Lean memory threshold |

The core cache checks took 0.19--0.45 seconds and about 52 MiB child peak.
The table's peaks are the helper's cumulative child-peak measurements within
each invocation; sampled RSS is a distinct measurement. No sampled-RSS or
wall-time stop occurred, no children overlapped, and no limit was increased.

These results distinguish importing from checking new terms: the imported
environment is loadable, and a reused proof term can pass, while ordinary
small new definitions or finite kernel decisions already fail. The installed
compiler source confirms that the forwarded `-M` argument sets its internal
runtime memory threshold in units of 1024 squared bytes. It is not an
OS-enforced reservation or a separate fresh allowance for each declaration.
The later pinned-source/binary investigation below identifies the actual macOS
check; the earlier interpretation as an allocation budget was incomplete.

Thus neither module source size nor finite proof-search size explains the
whole observed boundary. A targeted graph extraction can still reduce
dependency scope, but is not established as a way past this earlier limit.
Import-only and reused-proof checks are feasible at these settings; larger
new proof work and the full project remain remote. The fixtures themselves
are included in CI and the full axiom gate so a local resource refusal never
stands in for mathematical verification.

### Minimal-failure diagnosis and bounded correction, 2026-10-18

The failure was reproduced before changing any limit. Lake validated the
copied core dependencies in 0.66 seconds (52.3 MiB child peak); checking
`LocalCheckDefinition` then failed at `triangle` with `(kernel) excessive
memory consumption detected`, in 1.47 seconds and 575.6 MiB child peak.
No other Lean/Lake build was running.

The exact pinned release's
[`src/runtime/memory.cpp`](https://github.com/leanprover/lean4/blob/v4.30.0-rc2/src/runtime/memory.cpp)
explains the refusal. In its non-jemalloc macOS implementation, `check_memory`
samples every 200 calls. It first tests `getrusage`'s peak and, when needed,
checks Mach `task_info`'s current resident size against `g_max_memory`.
`Lean/Shell.lean` forwards `-M` into that threshold after multiplying by
1024 squared. Thus this is the whole process's resident-memory test, including
the imported environment, not a fresh allocation budget for a new proof.

The installed ARM64 `libleanshared.dylib` independently confirms that path:
disassembling `lean::check_memory(char const *)` shows the 200-call counter,
`getrusage`, `task_info` and comparison against the stored threshold. This
rules out merely assuming that the published source's optional allocator
branch matches the local binary. A small import/reused-proof run need not
trigger the same periodic check; passing one does not establish memory headroom.

Both earlier thresholds, 384 and 512 MiB, are below the approximately 576 MiB
baseline at which the tiny-definition fixture was refused. The observed
failure is therefore explained by the selected cap; it is not evidence that
this elementary definition inherently consumes hundreds of additional MiB,
or that the large causal modules are its prerequisite bottleneck. This does
not diagnose the original laptop-wide freeze, whose concurrency/system state
was not recorded.

The user separately authorized one 640 MiB Lean-threshold pilot, keeping one
compiler process, the 768 MiB sampled-RSS watchdog and 30-second wall/CPU
limits. Dependencies again validated (0.32 seconds, 52.3 MiB child peak).
`LocalCheckDefinition` then **passed**, in 1.20 seconds, with sampled peak
564.6 MiB and reported child peak 584.1 MiB. The sampled and reported peaks
are different measurements; neither is an allocation delta. The successful
output was disposable, so this alone does not supply a persistent cache.

The same bounded 640/768 MiB, single-process, 30-second profile was then
authorized for continued sequential module/cache-loop checks, without any
further limit increase. At that checkpoint the helper's default remained
384 MiB: the corrected
profile is selected explicitly with `--memory-mb 640`. Larger modules,
persistent artifact reuse and the full project are separate verification
requirements, not conclusions of this one successful fixture.

The subsequent explicitly sequential checks gave these results:

| Module | Wall time | Reported child peak | Result |
| --- | --- | --- | --- |
| `LocalCheckFiniteDecision` | 1.15 s | 585.8 MiB | Passed |
| `FourLabelTransportation` | 1.16 s | 640.2 MiB | Lean threshold, at line 375 |
| `FiniteRecord` (independent invocation) | 1.19 s | 632.4 MiB | Passed |

The transportation refusal remains a real local resource boundary. Its
dependents were not silently accepted or rebuilt, and no threshold was
raised. The `FiniteRecord` result establishes a real probability-library
module check, not only an import or a tiny fixture. None is a full-project
build or an axiom audit.

### Persistent, input-addressed single-module development loop

Add `--retain` to preserve successful selected `.olean` files in the ignored
`lean/.lake/local-checks-v1` store. This is separate from Lake's ordinary
`.lake/build` cache; no fabricated Lake trace or C output is installed there.
For example, from the repository root:

```sh
python3 -B lean/tools/check_module_cached.py Thesis.Examples.LocalCheckDefinition --check --memory-mb 640 --retain
python3 -B lean/tools/check_module_cached.py Thesis.Examples.LocalCheckRetainedDependency --check --memory-mb 640 --retain
```

The first command checks and retains the definition. The second imports that
retained artifact and checks a genuinely new proof, without rebuilding the
definition. Repeating the second command reuses the client as well, reporting
`Reused checked artifact (no re-elaboration)`. `--force-check` re-elaborates
selected modules even when such a matching result exists.

Keys cover source bytes, recursive project-dependency keys, configuration,
compiler arguments, checker implementation and the installed pinned compiler/
runtime identity. The identity includes architecture and compiler/runtime
hashes; the installed standard library is trusted as in a normal Lake build.
Artifact hashes are verified on load. A prerequisite edit invalidates its
clients, not unrelated modules. Source changes during checking prevent
publication. Each successful module is published independently, so failure
of a later selected module does not discard earlier checked work.

Ordinary dependencies still pass Lake's copied-trace freshness check. A
retained dependency has its own checked manifest, not a synthetic Lake trace.
If an ordinary cached client depends on a retained module, the helper refuses
to validate that ordinary trace and asks the caller to select that client for
checking too. Missing/stale dependencies never become permission for an
implicit full rebuild. Select changed dependencies explicitly, at most three
sequential modules and eight closure modules under the existing size bounds.

Live verification of this workflow checked the retained definition in 0.95 s
(584.3 MiB reported child peak), then checked its importing client in 0.44 s
(581.4 MiB). The unchanged client reused its artifact without a compiler
launch. Adding the separate `triangle_four` theorem invalidated the old
client result and checked the edited source in 0.38 s (581.5 MiB), still
reusing the unchanged definition. The local checker files are tested without
Lean for key invalidation, corrupted/incomplete entries, symlink refusal,
compiler-slot locking and monitor/timeout failures. Both Lean fixtures remain
inside the complete remote build and transitive axiom audit.

The final implementation also retained an actual `FiniteRecord` check
(0.91 s; 631.8 MiB reported invocation child peak). A subsequent two-module
invocation imported that retained probability library, validated the ordinary
core/graph prerequisites, then checked and retained `Probability.Construction`
(0.93 s) and `Causality.Model` (0.66 s). The reported child peak for that
invocation was 631.2 MiB; this is cumulative across its children, not a separate
exact peak for each module. Thus the local loop reaches actual causal-model
definitions as well as synthetic fixtures, without checking their unchanged
prerequisites again. Repeating a check is still explicitly distinguished from
reusing its already checked artifact.

This is a usable loop for modules fitting these limits. It is not blanket
permission for full local builds, unbounded source closures, arbitrary package
hooks or concurrent manual compiler jobs. Exact-input reuse is not fresh
elaboration, and neither replaces the complete project build or axiom gate.

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

No broad soundness/completeness split is performed. The original 384/512 MiB
pilot stopped much earlier, including in `FiniteRecord` and a tiny definition
after the cached core. The later diagnosis and 640 MiB results above supersede
that old boundary; the graph extraction alone was not its cure. The
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
python3 -B lean/tools/check_module_capped.py Thesis.Probability.FourLabelTransportation --plan
python3 -B lean/tools/check_module_capped.py Thesis.Probability.FourLabelTransportation
```

It uses the installed toolchain pinned in `lean/lean-toolchain`, never installs
anything, never launches Lake, and checks project dependencies sequentially
into a disposable directory. It does not reuse possibly stale project caches.
The current default per-child limits are one compiler thread, Lean's 640 MiB
memory threshold, a 768 MiB sampled-RSS watchdog, 30 seconds wall time and a
separate CPU-time limit. It shares the cache-aware helper's named profiles and
exclusive compiler slot; it does not persist its compiled artifacts. Source
size and closure size are also bounded. Low-priority scheduling is requested
where permitted. The accepted import-header syntax is intentionally restricted;
nested documentation/line comments and quoted strings do not masquerade as
headers. Plan mode launches nothing and writes no cache.

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
