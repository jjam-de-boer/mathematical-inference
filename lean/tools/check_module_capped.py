#!/usr/bin/env python3
"""Check a small, fresh Lean dependency closure without launching Lake jobs.

This deliberately conservative local-development helper is not a replacement
for the complete CI build or axiom audit.  It never consumes project .olean
caches: project dependencies are checked sequentially into one temporary
directory, using the exact installed toolchain selected by lean-toolchain.
Only the repository's ordinary, initial `import Module.Name` header syntax is
accepted.  Large closures and large source files require a different workflow,
not a silent relaxation of the local safety limits.

Lean's -M limits its own allocation accounting, not aggregate operating-system
RSS.  The separate CPU and wall-clock limits, low process priority, absence of
parallel children, and reported child peak RSS make this a bounded pilot; they
do not establish that an unrestricted local build is safe.
"""

import argparse
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import tempfile
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--seconds", type=int, default=30)
    parser.add_argument("--memory-mb", type=int, default=384)
    parser.add_argument("--max-modules", type=int, default=6)
    args = parser.parse_args()
    if not (1 <= args.seconds <= 60 and 128 <= args.memory_mb <= 512
            and 1 <= args.max_modules <= 8):
        parser.error("local pilot limits: 1–60 seconds, 128–512 MB, 1–8 modules")

    root = Path(__file__).resolve().parents[1]
    toolchain_name = (root / "lean-toolchain").read_text().strip().replace(":", "---").replace("/", "--")
    toolchain = Path.home() / ".elan" / "toolchains" / toolchain_name
    compiler = toolchain / "bin" / "lean"
    if not compiler.is_file():
        parser.error(f"pinned compiler is not installed: {compiler}; no download attempted")

    ordered = []
    visiting = set()
    checked = set()

    def visit(module):
        if not re.fullmatch(r"Thesis(?:\.[A-Za-z_][A-Za-z_0-9]*)+", module):
            parser.error(f"expected an explicit Thesis module, got {module!r}")
        if module in visiting:
            parser.error(f"cyclic project dependency at {module}")
        if module in checked:
            return
        source = root.joinpath(*module.split(".")).with_suffix(".lean")
        if source.stat().st_size > 128 * 1024:
            parser.error(f"source exceeds the 128 KiB local pilot limit: {module}")
        visiting.add(module)
        # These modules have plain initial import lines.  Do not attempt to
        # interpret arbitrary Lean syntax or infer dependencies from caches.
        header_done = False
        for line in source.read_text().splitlines():
            stripped = line.strip()
            if not stripped:
                continue
            if stripped.startswith("import ") and not header_done:
                imports = stripped.removeprefix("import ").split()
                for dependency in imports:
                    if dependency.startswith("Thesis."):
                        visit(dependency)
                    elif dependency != "Std" and not dependency.startswith(("Std.", "Lean.", "Init.")):
                        parser.error(f"unsupported dependency header in {module}: {line}")
            else:
                header_done = True
                if stripped.startswith(("import ", "public import ", "private import ")):
                    parser.error(f"non-initial/plain import header in {module}")
        visiting.remove(module)
        checked.add(module)
        ordered.append((module, source))
        if len(ordered) > args.max_modules:
            parser.error("dependency closure exceeds the local pilot module limit; use CI")

    for module in args.modules:
        visit(module)
    print("Fresh sequential closure: " + ", ".join(module for module, _ in ordered), flush=True)

    try:
        os.nice(15)
    except PermissionError:
        print("Low-priority scheduling is denied by this sandbox; all resource/time caps remain active.", flush=True)

    def limit_child():
        resource.setrlimit(resource.RLIMIT_CPU, (args.seconds, args.seconds + 1))

    with tempfile.TemporaryDirectory(prefix="thesis-lean-pilot-") as temporary:
        environment = os.environ.copy()
        environment["LEAN_PATH"] = temporary + os.pathsep + str(toolchain / "lib" / "lean")
        for module, source in ordered:
            output = Path(temporary).joinpath(*module.split(".")).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            command = [str(compiler), "-j1", f"-M{args.memory_mb}",
                       "-DmaxHeartbeats=400000", "-DmaxErrors=1",
                       "-R", str(root), "-o", str(output), str(source)]
            started = time.monotonic()
            child = subprocess.Popen(command, cwd=root, env=environment,
                                     start_new_session=True, preexec_fn=limit_child)
            try:
                result = child.wait(timeout=args.seconds)
            except (subprocess.TimeoutExpired, KeyboardInterrupt):
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
                print(f"Stopped {module}: wall limit or user interruption", flush=True)
                return 124
            elapsed = time.monotonic() - started
            peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
            # macOS reports bytes; Linux reports KiB.  This is the maximum
            # child peak for this invocation, not a live system-memory probe.
            peak_mib = peak / (1024 * 1024 if os.uname().sysname == "Darwin" else 1024)
            print(f"{module}: exit={result}, {elapsed:.2f}s, child peak ≤ {peak_mib:.1f} MiB", flush=True)
            if result:
                return result
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
