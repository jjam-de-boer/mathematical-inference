#!/usr/bin/env python3
"""Check a small fresh Lean closure under the same explicit local profiles.

Unlike the cache-aware checker, this helper imports no project build artifacts:
every project prerequisite is compiled sequentially into a disposable snapshot.
The installed pinned standard library remains trusted in both workflows.

Resource policy is shared, not reimplemented: the named profile, global helper
compiler-slot lock, sampled RSS monitor, CPU limit and wall timeout are exactly
those used by check_module_cached. A refusal never retries with larger limits.
Only explicitly bounded source closures and the reviewed plain configuration
are accepted. This is not permission to start an unrestricted local Lake build.
"""

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from check_module_cached import (ArtifactError, PilotError, RESOURCE_PROFILES,
    check_configuration, closure, describe_limits, digest, exclusive_check,
    resolve_limits, run_capped, source_path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--plan", action="store_true",
                        help="inspect the fresh closure without launching a compiler")
    parser.add_argument("--profile", choices=RESOURCE_PROFILES, default="conservative",
                        help="explicit memory pair; no automatic escalation")
    parser.add_argument("--seconds", type=int, default=30)
    parser.add_argument("--memory-mb", type=int, default=None)
    parser.add_argument("--rss-mb", type=int, default=None)
    parser.add_argument("--max-modules", type=int, default=6)
    parser.add_argument("--max-selected", type=int, default=1)
    args = parser.parse_args()
    try:
        limits = resolve_limits(args)
        selected = list(dict.fromkeys(args.modules))
        if len(selected) > limits.max_selected:
            raise PilotError("too many explicitly selected modules")
        root = Path(__file__).resolve().parents[1]
        check_configuration(root)
        ordered = closure(root, selected, limits)
        print(describe_limits(limits), flush=True)
        print("Fresh sequential closure: " + ", ".join(ordered), flush=True)
        if args.plan:
            print("Plan only: no compiler or cache writes were launched.")
            return 0

        release = (root / "lean-toolchain").read_text().strip().replace(":", "---").replace("/", "--")
        toolchain = Path.home() / ".elan/toolchains" / release
        compiler = toolchain / "bin/lean"
        if not compiler.is_file():
            raise PilotError("pinned compiler is not installed; no download attempted")
        try:
            os.nice(15)
        except PermissionError:
            print("Low-priority scheduling unavailable; all other caps remain active.", flush=True)

        # Snapshot source bytes as well as outputs. Concurrent source edits
        # invalidate the result, rather than producing a mixed-version closure.
        # The shared .lake is used only for the compiler-slot lock, never as a
        # project dependency search path.
        with exclusive_check(root), tempfile.TemporaryDirectory(prefix="thesis-fresh-pilot-") as directory:
            temporary = Path(directory)
            tracked = [source_path(root, module) for module in ordered]
            tracked += [root / name for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")]
            fingerprints = {path: digest(path) for path in tracked}
            for source in tracked:
                destination = temporary / source.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, destination)
            library = temporary / ".lake/build/lib/lean"
            environment = os.environ.copy()
            environment["LEAN_PATH"] = os.pathsep.join((str(library), str(toolchain / "lib/lean")))
            environment["LAKE_CACHE_DIR"] = str(temporary / "unused-artifact-cache")
            for module in ordered:
                output = library.joinpath(*module.split(".")).with_suffix(".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                print("Checking fresh module: " + module, flush=True)
                run_capped([str(compiler), "-j1", f"-M{limits.memory_mb}",
                    "-DmaxHeartbeats=400000", "-DmaxErrors=1", "-R", str(temporary),
                    "-o", str(output), str(source_path(temporary, module))],
                    temporary, environment, limits)
            if any(digest(path) != value for path, value in fingerprints.items()):
                raise PilotError("sources changed during the fresh check; result is not current")
        print("Fresh closure checked; outputs discarded. Full build and axiom audit remain separate.")
        return 0
    except (PilotError, ArtifactError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"Fresh check stopped: {error}", flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
