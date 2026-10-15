# Resource-capped local checks

Full project builds and the transitive axiom audit currently remain remote.
The previous laptop freeze has not been diagnosed; faster endpoint arithmetic
does not establish that full proof elaboration fits local memory.

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
