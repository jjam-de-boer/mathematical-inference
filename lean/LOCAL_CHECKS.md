# Resource-capped local checks

## Ordinary Lake builds (no Python prerequisite)

The supported native local route is now:

```sh
cd lean
export LEAN_NUM_THREADS=1
lake build
lake build Thesis.AxiomAudit
```

The environment setting gives Lake one worker. The committed `weakLeanArgs`
separately give each child Lean compiler one thread and a 4608 MiB memory
threshold. These are distinct controls: `-j1` alone does not serialize Lake's
independent jobs. An isolated two-module cold pilot and the actual complete
project commands were observed under the existing single-compiler watchdog;
neither launched concurrent compiler families.

The smoke executable has an explicit `needs = ["Thesis"]` build prerequisite.
It therefore still checks the **same entire public proof facade**, including
its regression examples, before compiling. `Main` itself only imports the
standard-library IO interface it uses. This removes unnecessary C-object
compilation and linking of the mathematical library from the executable,
without dropping proof checks, deleting declarations, changing imports of the
public facade, or weakening the separate full axiom gate. Building `thesis`
explicitly also retains this prerequisite; the optimization is not merely a
smaller default target list.

Ordinary Lake does **not** implement the Python helper's aggregate-RSS
watchdog, source-change fingerprints, shared lock or per-invocation wall stop.
The native command's per-compiler memory threshold is not a hard whole-machine
reservation. Keep the single-worker setting and adequate machine headroom;
use the monitored helper below when those extra safeguards are wanted.
No unrestricted parallel cold build is recommended for this laptop.

The sections below preserve the investigation and monitored route. Their
earlier object counts precede the native-build restructuring.

### Native measurements, 2026-10-20

The shared checkout's newer bounded-proof modules were included, not removed
for the comparison. The unchanged full proof/audit traversal contains 890
project modules. Before the restructuring, the actual default executable
build reported 1744 jobs and its runtime closure needed 871 project native
objects. Afterward, the actual default build reported 874 jobs and only Main
needed a project native object. The complete axiom audit still reported 890
jobs and checked 42,391 declarations under the unchanged permitted-axiom policy.
The smoke binary occupies approximately 2.2 MiB.

The first actual native build after changing Main passed in 2.03 s with
365.5 MiB sampled aggregate RSS, including Main elaboration, C compilation
and linking. The following full audit passed in 0.77 s from the current
proof cache. A subsequent fully cached native build/audit pair took **2.48 s**
in total, versus **11.92 s** for the fully cached monitored Python workflow
on the same restructured checkout: approximately **4.8 times faster** for
that warm verification workflow. Both native measurements used `--rehash`
and `--no-cache`, so they did not gain speed by bypassing dependency freshness
or downloading someone else's artifacts.

This is **not a measured twofold speedup of all proof elaboration or a full
cold build**. The native command avoids monitoring/startup overhead, and the
build-graph change eliminates unused machine-code work; existing mathematical
proofs still require their original kernel checks. The old baseline also
rebuilt several concurrently added proof modules, so its 170-second total is
not used as a warm speedup comparison. Further cold-build acceleration would
need a controlled complete cold benchmark and targeted optimization of the
remaining expensive proof checks, rather than counting skipped C jobs as
twice-faster mathematics.

An independent isolated Lake pilot also checks the prerequisite boundary:
two previously uncached proof modules build sequentially, and an intentionally
invalid proof makes the default executable build fail even when its previous
binary exists. It is not possible to obtain a successful smoke build merely
by avoiding a runtime import of the proof facade. The repository's 84 helper
and structural tests passed, and the retained monitored complete workflow
also passed with no rebuilt mathematical modules.

The native measurement logs are retained in
`.lake/native-lake-build-8h13a5wk/` and `.lake/native-lake-warm-whhj7apf/`.

## Monitored full-project route

The complete local build and transitive axiom audit passed on 2026-10-20,
using the cache-aware, sequential workflow below and the original committed
project configuration. The full builder's explicit `extended` profile keeps
one compiler family, a 4608 MiB Lean threshold, a 5120 MiB sampled aggregate-RSS
watchdog and a 30-second limit per invocation. The final audit checked 42,173
imported project declarations and allowed only `propext` and `Quot.sound`.

Useful selected-module checking is also feasible under the conservative
640 MiB Lean / 768 MiB sampled-RSS / 30-second single-process profile below;
the explicit 768/1024 MiB pilot also checks downstream transportation modules.
The previous laptop-wide freeze has not been diagnosed. This measured success
establishes a bounded sequential local route, not the safety of an unrestricted
parallel cold build or guaranteed responsiveness under arbitrary external load.

## Full-project sequential build (verified)

`tools/build_local_sequential.py` is separate from the small-closure pilot.
It walks the actual default executable and full axiom-audit dependencies,
asks Lake to build prerequisite-first, and retains genuine ordinary artifacts
and traces in `.lake/build`. It never copies a pilot `.olean` into that cache
or invents a successful trace. Intermediate successes are resumable, not a
claim that the full project builds.

```sh
python3 -B lean/tools/build_local_sequential.py
python3 -B lean/tools/build_local_sequential.py --phase lean --max-builds 20 --check
python3 -B lean/tools/build_local_sequential.py --profile extended --check
```

The first command only plans. The second is an optional checkpoint after 20
actual rebuilt modules; it returns a distinct checkpoint exit code, not full
success. Repeating it resumes using Lake freshness checks. The third attempts
all Lean modules, native object files, the actual complete build and the full
axiom audit. Only its explicit final gate result establishes end-to-end local
success; a passed `--target` or individual `--phase` does not.

Without an explicit profile the full builder uses 768 MiB Lean, 1024 MiB
aggregate sampled RSS and 30 seconds per invocation. That smaller profile is
not sufficient for the complete project; use `extended` for the verified
full-build route. A temporary declarative TOML file adds only weak resource
arguments (`-j1`, the selected `-M` threshold, `-DmaxErrors=1`), which this
pinned Lake excludes from proof traces. The committed configuration is not
edited. The whole owned process group is monitored, including compiler and
linker children; its aggregate RSS deliberately counts shared resident pages
conservatively. Independent compiler families, unmonitorable children, source
changes and resource overruns stop the build. Wall/CPU stops are distinguished
from Lean's memory-threshold failures. Final commands use the original package
configuration, with a no-build preflight before those commands can run.

The following measurements record the staged investigation chronologically.
References to outstanding gates describe those earlier checkpoints, not the
current result; the final verification is recorded below.

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

The monolithic `Completeness` subsequently exceeded the 1280 MiB aggregate
watchdog. Its original source is now partitioned chronologically into
certificate, failure-extraction, three historical legacy-case, and three
hedge-model/parity/countermodel layers. The original entry point remains an
import-compatible facade. All original declaration text reassembles exactly
in its original order; no deeper failure case was added and no historical
lemma was deleted. The unsplit `851b231` source has SHA-256
`c9e5000ada10ceabcb3492f17b98e0bb5fb5a57c773faa55e04ba900dd195fcd`.

All eight layers and the facade passed sequentially through ordinary Lake:

| Completeness layer | Wall time | Sampled aggregate RSS |
| --- | --- | --- |
| Certificates | 4.84 s | 978.3 MiB |
| Failure extraction | 1.51 s | 780.1 MiB |
| Legacy shrink cases | 2.45 s | 861.2 MiB |
| Legacy product cases | 1.77 s | 819.1 MiB |
| Legacy deeper cases | 1.62 s | 792.1 MiB |
| Hedge models | 9.03 s | 867.5 MiB |
| Hedge parity | 3.17 s | 835.7 MiB |
| Hedge countermodels | 2.74 s | 795.6 MiB |
| Original facade | 0.51 s | 625.2 MiB |

These are compilation repairs, not new mathematical soundness/completeness
claims. Full local project/native/audit gates are still outstanding at this
checkpoint. The builder now batches only no-build validation of unchanged
targets; a stale batch falls back to individual prerequisite-first compilation.
Intermediate source checks cover each target and its prerequisites so unrelated
in-progress edits do not interrupt earlier work; the final checks still cover
the complete planned tree. Resource-stop reports include the elapsed time,
sampled process-group peak and log path.

The resumed full bootstrap reached module 628/853 before the front-door
`IdentificationRegression` hit a native stack overflow (3.06 s; 1136.8 MiB
sampled aggregate RSS). That is distinct from a timeout or the RSS watchdog.
Merely spelling the generated formula with simpler finite masks did not
resolve the numerical reduction. The repaired regression also checks the
model's eight observed cell weights once, proves agreement for every event,
and reuses that exact table beneath the nested sums and quotients. Literal
syntax equality ties the compact expression to the engine's actual output.
Neither bridge uses causal soundness/completeness or assumes the answer.
Every original numerical statement, including the legacy `9/16` failure and
both current-engine `1/2` successes, remains checked.

The existing `ProbabilityTerm.observationalDenote` definition is extracted
unchanged into `Causality.ObservationalEvaluation`, below native completeness.
New `observationalDenote_eq_scm` and `observationalDenote_congr` bridges justify
table reuse, including unsupported results; actionful leaves remain rejected.
The resulting regression passed its ordinary Lake target in 2.56 s with
946.5 MiB sampled aggregate RSS. Two Type-valued semantic proof witnesses
are now explicitly `noncomputable`, consistently with the existing
congruence interface; the closed numerical checks are still kernel proofs.
The complete graph, now enlarged by newer distribution and certificate work,
is being resumed. These measurements still do not establish the final gates.

### Explicit extended profile after a measured higher-memory pilot

The next original numerical fixture, `GuardedIdentificationKernel`, did not
fit the conservative attempts, including the separately approved 1536 MiB
trial. Original-source 2048 and 3072 MiB trials also stopped in its guarded
value check. After explicit user approval for higher pilots, the unchanged
file passed with 4608 MiB Lean / 5120 MiB aggregate RSS bounds: 11.90 s and
3169.8 MiB sampled aggregate RSS. All three numerical theorem axiom reports
contained only `propext` and `Quot.sound`. No swap was observed afterward.
The speculative guarded-table refactor was discarded; its original proof
and the existing native observational bridge are retained without changes.

The full builder now accepts `--profile extended`, with that same reviewed
4608/5120 MiB pair, one compiler family and at most 30 seconds per invocation.
It is explicit, never selected automatically after a failure, and does not
change the small-closure helpers' older limits. It is a memory budget, not
a reservation or a measured hardware maximum; a single sampled process-group
watchdog cannot guarantee laptop responsiveness under changing external load.

```sh
python3 -B lean/tools/build_local_sequential.py --phase lean --profile extended --check
```

The direct original-source pilot did not itself create a Lake artifact.
The subsequent ordinary Lake check also passed the unchanged fixture:
11.98 s, 3246.5 MiB sampled aggregate RSS, with a genuine reusable trace.
The sequential run must still finish all remaining Lean/native/final gates
before local full-build success can be reported. A separate 20-target native
checkpoint already passed at the
old ceiling, with sampled aggregate peaks below 112 MiB for those C-object
builds; that small checkpoint does not certify the remaining native graph.

No larger memory or timeout setting is an automatic retry. Unrelated editor
or manual compiler processes are not terminated. Machine-wide headroom still
matters, especially on this machine while other applications retain swap.

### Resumed full-scope checks, 2026-10-20

The published `587fa1e` checkpoint includes the newer finite-grid and partial
moment distribution modules. Its complete local Lean/audit graph has 879
modules. All seven new distribution modules passed sequentially, with sampled
aggregate peaks below 700 MiB. Separately, all 38 then-unbuilt examples that
were independent of `HedgeObstructionModel` passed, including the positive and
supported-zero modal regressions. These are intermediate checks, not a full
build or a replacement for the complete axiom-policy gate.

The full traversal subsequently reached `HedgeObstructionModel` (module 836).
It stopped at the unchanged 30-second wall deadline: 30.04 s and 891.7 MiB
sampled aggregate RSS. This is **not** a memory failure, an invalid proof, or
evidence that local compilation is impossible. A longer single-module pilot
requires separate approval; the reusable builder still rejects time limits
above 30 seconds. No proof statement or numerical fixture has been removed
to get past this boundary.

Subsequent sequential preparation finished every target independent of that
one model. Separate no-build inventories using the **original committed
configuration** confirmed 874/879 Lean/audit targets and 857/861 native-object
targets current. Both inventories fingerprinted the complete source and
configuration scope before and after; neither started compilation. The five
remaining Lean targets are `HedgeObstructionModel`, its
`HedgeObstructionCounterexample` client, `Thesis`, `Main`, and `Thesis.AxiomAudit`.
The same first four still block the executable cache. These are dependencies
of one observed time-limit boundary, not five independently diagnosed errors.
Swap usage remained zero afterward. The actual complete local build, final
link and local axiom-policy gate still must pass before reporting success.

The subsequent published `16f690a` covariance/rank additions also passed
sequentially, including their new `DistroRanks` regression and affected
distribution examples. Each newly added library module stayed below 700 MiB.
Repeating the original-configuration, source-fingerprinted no-build inventories
then confirmed **881/886 Lean/audit targets and 863/867 native-object targets**
current. The blocked target names above are unchanged; the larger totals come
from the concurrent distribution additions, not from a new causal failure.

### Complete local build and audit passed, 2026-10-20

The two remaining exhaustive hedge regressions now check actual SCM factors
pointwise, then combine them by symbolic product arithmetic. The model's
`factual_slice_factor` certificate checks only the observed and shared inputs
read by each factor, leaving all other inputs arbitrary. The companion's
`intervention_slice_factor` reuses that certificate at untouched coordinates
and checks the two forced consistency indicators directly. Their respective
`factual_factors_product` and `intervention_factors_product` lemmas recover the
original likelihood weights and denominators. The original exhaustive Boolean
assertions still follow, without repeatedly reducing the full joint encoder.

Every pre-existing definition, theorem statement and numerical regression in
both files remains unchanged. Outside the new helper blocks, only the proof
bodies of the private `factual_slice_checks` and `intervention_slice_checks`
assertions changed. A preservation check removed the new blocks and restored
those two old bodies, reproducing the original files at `210ef53` byte-for-byte:

| Original source | SHA-256 |
| --- | --- |
| `HedgeObstructionModel.lean` | `fbb0143d1ffff9441bacff033cf46690f57b97c6beab02253ec148e920c98f59` |
| `HedgeObstructionCounterexample.lean` | `b0cb819e491df38d981853b6c84aa3bf15e7d1ad57fe0293a5051d9977f70677` |

Both original whole-table checks had reached the 30-second deadline. Their
repaired ordinary Lake targets passed in 4.95 s / 1119.8 MiB and 1.23 s /
765.3 MiB sampled aggregate RSS, respectively. Although a 60-second pilot was
subsequently approved, neither repair needed it: the reusable builder's
30-second limit and 5 GiB aggregate cap stayed unchanged. These are verified
proof-compilation repairs, not an enlargement of the causal theorem scope.

The complete `--profile extended --check` run then traversed all 886 Lean/audit
modules and 867 native-object modules, linked the executable, and ran the
actual final commands under the **original committed configuration**. Genuine
Lake artifacts were reused; no successful trace or artifact was fabricated.
The source/configuration fingerprints remained unchanged throughout the run.

| Final step | Result | Wall time | Sampled aggregate RSS |
| --- | --- | --- | --- |
| Elaborate `Thesis.AxiomAudit` | 42,173 declarations pass the axiom policy | 4.86 s | 1105.7 MiB |
| Link executable | Passed | 1.72 s | 753.8 MiB |
| Actual `lake build` | Passed, 1736 jobs current | 0.41 s | 144.3 MiB |
| Actual `lake build Thesis.AxiomAudit` | Passed, 886 jobs current | 0.30 s | 123.1 MiB |

The final warm-command measurements are not the memory cost of a cold build.
Earlier measured compilation in this bootstrap reached approximately 3.8 GiB
aggregate RSS. The verified local route prepares stale prerequisites one at a
time, then runs the real complete commands after no-build preflights; it does
not silently allow those commands to start an unbounded parallel rebuild.
Subsequent incremental runs reuse the same normal `.lake/build` cache.

Local measurements and individual invocation logs are retained in
`.lake/local-builds-v1/20261020-101218-uk54hjo6/`. The successful final banner is
`FULL LOCAL BUILD AND AXIOM AUDIT PASSED using the committed configuration.`
The build-helper regression suite also passed all 76 tests.

### Incremental bounded-enumeration pilot, 2026-10-20

The new `ProbabilityTermEnumeration` and `DerivationEnumeration` modules
passed ordinary sequential Lake targets at the conservative 640 MiB Lean /
768 MiB aggregate-RSS / 30-second profile: respectively 2.12 s / 651.2 MiB
and 1.00 s / 664.1 MiB sampled group RSS. Genuine prerequisite artifacts were
reused and the shared exclusive compiler lock prevented an overlapping build.

The downstream `NativeProofEnumeration` target stopped at Lean's 640 MiB
threshold, in its first definitions after loading the native support/checker
environment: 1.10 s / 762.4 MiB sampled group RSS. Its proof bridge and example
file were not established by that run. This was a resource refusal, not an
unsuccessful mathematical proof or a timeout. No larger profile was retried
automatically; native verification continued remotely. The earlier complete
local build above concerns its recorded checkpoint, not these later additions.
Logs are retained in `.lake/local-builds-v1/20261020-141555-pybr948z/`.

### Incremental resource-preflight pilot, 2026-10-20

The new arithmetic counting module `CodeEnumerationCounts` passed in 0.88 s
with 687.0 MiB sampled aggregate RSS; `CodeSearchPreflight` passed in 0.99 s
with 670.5 MiB. Both used the unchanged conservative 640 MiB Lean / 768 MiB
RSS / 30-second profile and genuine ordinary Lake artifacts. The helper's
exclusive lock refused an earlier attempt while another builder held it;
no competing compiler was launched. Those two small checks alone did not
establish the native semantic wrapper or a complete build.

The successful runs are recorded in
`.lake/local-builds-v1/20261020-145928-q6m5mxhe/` (counting module) and
`.lake/local-builds-v1/20261020-150105-xw0gdswv/` (syntax-preflight module).
These were selected-module results, not a complete local build or audit.

After the local-build restructuring was confirmed, the native wrapper passed
locally in 1.12 s / 784.5 MiB and its examples in 0.88 s / 812.8 MiB using the
explicit `extended` profile. A full local audit then caught an indirect
`Classical.choice` dependency introduced by automated reasoning about a
clipped-count inequality. Its proof now explicitly decides the natural-number
comparison and uses the two minimum bounds; the policy was not weakened.

The repaired stage subsequently passed the **complete local build and axiom
audit**, including the actual original-configuration final gates: 894
Lean/audit modules, 42,734 audited project declarations, and only `propext`
and `Quot.sound`. The audit rebuild took 5.25 s / 1112.9 MiB. Logs are in
`.lake/local-builds-v1/20261020-191432-z5gd9kba/`. No full code or model-support
catalogue was expanded by these regressions. These measurements do not
establish a cold-build speedup or a general runtime memory guarantee.

### Metadata-preflight hardening, 2026-10-20

The fallback syntax preflight now refuses mask overflow before calling any
coordinate value-enumeration function. The opt-in certified-metadata path
additionally checks reference overflow using numerical domain sizes whose
agreement with the original lists is proved in Lean. Both dictionary gates
precede real dictionary construction. Generated C was inspected to confirm
this evaluation order; the mathematical equality theorem alone would not
exclude expensive eager work with an unused result.

The changed fallback passed locally in 1.64 s / 686.4 MiB sampled aggregate
RSS, and `CodeSearchMetadata` in 0.49 s / 648.8 MiB. The native metadata wrapper
passed in 0.69 s / 769.2 MiB and its regressions in 0.74 s / 758.9 MiB. These
used the unchanged explicit `extended` profile and the shared single-builder
lock, with logs in `.lake/local-builds-v1/20261020-193935-wb0wmyhf/` and
`.lake/local-builds-v1/20261020-194323-am439pxa/`. These are selected-module
measurements, not a full-build claim. The large-domain refusal tests occur
only as erased propositions/proofs, not executable billion-element lists.
Neither these measurements nor metadata provide a general model-evaluation
time/RAM bound or a guarded complete profile generator.

The subsequent complete local build and full axiom audit passed on the same
combined checkout, including the concurrently committed lightweight
distribution extraction. The audit checked 43,156 imported project declarations
with the unchanged `propext`/`Quot.sound` policy; its rebuild took 5.06 s /
1106.1 MiB sampled aggregate RSS. Both actual final commands exited zero.
Logs are in `.lake/local-builds-v1/20261020-194452-arafz14b/`. All 93 helper
and source-regression tests also passed. This records that source checkpoint,
not later entropy additions or an unrestricted cold-build timing.

### Bounded native selector, 2026-10-21

The generic native scan passed locally in 0.75 s / 743.3 MiB sampled aggregate
RSS; the metadata-admitted bounded adapter passed in 0.72 s / 745.5 MiB and
its examples in 0.91 s / 756.5 MiB. All used the unchanged explicit `extended`
profile and shared single-builder slot. Busy slots were refused rather than
starting a competing compiler. Logs are retained in
`.lake/local-builds-v1/20261021-102715-_i0yqjez/` (generic layer) and
`.lake/local-builds-v1/20261021-102958-kc2osgeb/` (adapter and regressions).
These are selected-module checks, not a complete build or full-axiom claim.

Generated code was inspected: the adapter first calls the guarded catalogue,
returns a refusal without scanning, and calls the native first-available scan
only after admission. The scan tests each visited candidate once and returns
without visiting its tail after success. This is an observed implementation
property under the pinned compiler, not a formal whole-runtime cost bound.
Concrete regressions expand only eight native leaves on supplied tiny
profiles; deeper bounded acceptance coverage remains symbolic. Arbitrary
profile construction, record preparation and formula-evaluation costs remain
outside the structural comparison allowance.

The first complete-project attempt at this stage stopped when concurrent
refactoring changed source files during the run. It correctly withheld full
success, rather than accepting a mixed source snapshot. That stop was not a
selector proof failure or a resource-cap failure; selected-module success
alone still does not establish the complete project or axiom audit.

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
