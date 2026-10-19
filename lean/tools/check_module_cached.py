#!/usr/bin/env python3
"""Check explicitly selected Lean modules against validated local dependencies.

This is a small opt-in pilot, not a second project build system. Lake validates
copied dependency traces with --no-build and --rehash; it never receives
permission to rebuild a missing dependency. Only the explicitly named modules
are subsequently compiled, one at a time, into a disposable workspace. Neither
the source checkout nor Lake's ordinary build cache is modified. With --retain,
successful outputs enter a separate input-addressed local store and can serve
as checked dependencies in later invocations. A held OS lock prevents two
instances of this helper from launching compilers concurrently.

The supported configuration is deliberately narrow: this repository's plain
TOML package, no external packages, and ordinary initial import headers. A
configuration change or a larger closure must be reviewed, not silently
accepted by weakening the pilot. Time/CPU limits and Lean's memory threshold
are supplemented by a sampled child-RSS watchdog. Sampling is not a hard OS
memory ceiling; inability to sample is a reason to stop before compilation.
"""

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import tempfile
import time
import tomllib

from local_check_artifacts import (ArtifactError, ArtifactStore, digest,
    exclusive_check, module_keys, ordinary_dependencies, toolchain_identity)


class PilotError(RuntimeError):
    """A failed precondition is not a successful proof check."""


@dataclass(frozen=True)
class Limits:
    seconds: int = 30
    memory_mb: int = 384
    rss_mb: int = 768
    max_modules: int = 6
    max_selected: int = 1

    def validate(self):
        if not (1 <= self.seconds <= 60 and 128 <= self.memory_mb <= 640
                and 256 <= self.rss_mb <= 768 and 1 <= self.max_modules <= 8
                and 1 <= self.max_selected <= 3):
            raise PilotError("limits: 1–60 seconds, 128–640 MiB Lean memory, "
                             "256–768 MiB sampled RSS, 1–8 closure modules, 1–3 selected modules")


def source_path(root, module):
    if not re.fullmatch(r"Thesis(?:\.[A-Za-z_][A-Za-z_0-9]*)+", module):
        raise PilotError(f"expected an explicit Thesis module: {module!r}")
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def imports(source):
    """Reject unsupported headers instead of guessing Lean dependencies.

    This parser is only a conservative preflight. Lake's own import parser and
    trace checker remain authoritative for every reused dependency. Selected
    modules are elaborated by the pinned compiler in the copied source tree.
    """
    result = []
    header_done = False
    for line in source.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("import ") and not header_done:
            for dependency in stripped.removeprefix("import ").split():
                if dependency.startswith("Thesis."):
                    source_path(Path("."), dependency)
                    result.append(dependency)
                elif dependency != "Std" and not dependency.startswith(("Std.", "Lean.", "Init.")):
                    raise PilotError(f"unsupported import: {dependency}")
        else:
            header_done = True
            if re.match(r"(?:public |private |meta )?import\b|module\b|prelude\b", stripped):
                raise PilotError("only ordinary initial import headers are supported")
    return result


def closure(root, selected, limits):
    ordered, visiting, visited = [], set(), set()

    def visit(module):
        if module in visiting:
            raise PilotError(f"cyclic project imports: {module}")
        if module in visited:
            return
        source = source_path(root, module)
        if source.is_symlink() or not source.is_file():
            raise PilotError(f"missing or symbolic-link source: {module}")
        if source.stat().st_size > 128 * 1024:
            raise PilotError(f"source exceeds 128 KiB pilot limit: {module}")
        visiting.add(module)
        for dependency in imports(source.read_text()):
            visit(dependency)
        visiting.remove(module)
        visited.add(module)
        ordered.append(module)
        if len(ordered) > limits.max_modules:
            raise PilotError("dependency closure exceeds pilot limit; use remote verification")

    for module in selected:
        visit(module)
    if sum(source_path(root, module).stat().st_size for module in ordered) > 512 * 1024:
        raise PilotError("combined source exceeds 512 KiB pilot limit")
    return ordered


def check_configuration(root):
    """Do not execute arbitrary package hooks while validating a cache.

    The exact supported declarative configuration has no scripts, plugin
    libraries, external packages, or per-module compiler-option overrides.
    Refuse an ambient Lean search path as well: it would defeat isolation.
    """
    expected = {"name": "thesis", "version": "0.1.0", "defaultTargets": ["thesis"],
                "lean_lib": [{"name": "Thesis"}],
                "lean_exe": [{"name": "thesis", "root": "Main"}]}
    if tomllib.loads((root / "lakefile.toml").read_text()) != expected:
        raise PilotError("package configuration differs from the reviewed pilot configuration")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    if manifest != {"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [],
                    "name": "thesis", "lakeDir": ".lake", "fixedToolchain": False}:
        raise PilotError("dependency manifest differs from the reviewed empty-package manifest")
    if os.environ.get("LEAN_PATH") or os.environ.get("LEAN_SRC_PATH"):
        raise PilotError("ambient Lean search paths must be unset for the isolated pilot")


def cache_paths(module):
    relative = Path(*module.split("."))
    library = Path(".lake/build/lib/lean") / relative
    return [library.with_suffix(".olean"), library.with_suffix(".ilean"),
            library.with_suffix(".trace"), (Path(".lake/build/ir") / relative).with_suffix(".c")]


def copy_dependencies(root, temporary, dependencies):
    """Copy, never link, the bounded artifact set that Lake will validate.

    Hash sidecars and local artifact-store entries are intentionally omitted.
    Lake must rehash the copied data, and cannot restore an unrelated cached
    result into the source worktree. New-style private/module artifacts are
    outside this initial pilot's explicitly supported format.
    """
    files = []
    for module in dependencies:
        trace = root / cache_paths(module)[2]
        if not trace.is_file() or trace.is_symlink():
            raise PilotError(f"dependency has no reusable local trace: {module}; no rebuild attempted")
        data = json.loads(trace.read_text())
        if data.get("synthetic") is not False or data.get("outputs", {}).get("m") is not False:
            raise PilotError(f"unsupported or synthetic dependency trace: {module}")
        for relative in cache_paths(module):
            source = root / relative
            if source.is_symlink() or not source.is_file():
                raise PilotError(f"missing or symbolic-link dependency artifact: {relative}")
            files.append((source, temporary / relative))
    if sum(source.stat().st_size for source, _ in files) > 64 * 1024 * 1024:
        raise PilotError("dependency artifacts exceed the 64 MiB pilot limit")
    for source, destination in files:
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)


def rss_mib(pid):
    """Read only the pilot child's resident size; never inspect app content."""
    result = subprocess.run(["/bin/ps", "-o", "rss=", "-p", str(pid)],
                            text=True, capture_output=True, timeout=1)
    if result.returncode or not result.stdout.strip():
        raise PilotError("child RSS sampling is unavailable; refusing an unmonitored pilot")
    try:
        return int(result.stdout.strip()) / 1024
    except ValueError as error:
        raise PilotError("invalid child RSS sample") from error


def terminate(child):
    if child.poll() is None:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    child.wait()


def run_capped(command, cwd, environment, limits):
    """One child at a time, including validation; failures never pass a gate.

    Output goes to a temporary file, avoiding pipe backpressure while polling.
    Reported sampled RSS and cumulative child peak are distinct measurements.
    The CPU limit is per process; the wall watchdog also covers waiting time.
    """
    rss_mib(os.getpid())  # Check monitoring permission before starting work.

    def child_limits():
        resource.setrlimit(resource.RLIMIT_CPU, (limits.seconds, limits.seconds + 1))

    started, sampled_peak = time.monotonic(), 0.0
    with tempfile.TemporaryFile(mode="w+") as output:
        child = subprocess.Popen(command, cwd=cwd, env=environment, stdout=output,
                                 stderr=subprocess.STDOUT, start_new_session=True,
                                 preexec_fn=child_limits)
        try:
            while child.poll() is None:
                if time.monotonic() - started >= limits.seconds:
                    raise PilotError("child stopped at wall-time limit")
                try:
                    sampled_peak = max(sampled_peak, rss_mib(child.pid))
                except PilotError:
                    if child.poll() is not None:
                        break  # The child can finish between poll and ps.
                    raise
                if sampled_peak > limits.rss_mb:
                    raise PilotError("child stopped at sampled RSS limit")
                time.sleep(0.05)
        except BaseException:
            terminate(child)
            raise
        result = child.wait()
        output.seek(0)
        log = output.read(128 * 1024)
    print(log, end="" if log.endswith("\n") else "\n", flush=True)
    peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    peak /= 1024 * 1024 if os.uname().sysname == "Darwin" else 1024
    print(f"exit={result}; wall={time.monotonic() - started:.2f}s; "
          f"sampled RSS={sampled_peak:.1f} MiB; invocation child peak={peak:.1f} MiB", flush=True)
    if result:
        raise PilotError("child failed; selected modules are not verified")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--check", action="store_true", help="opt in to bounded validation and compilation")
    parser.add_argument("--retain", action="store_true",
                        help="retain/reuse successful artifacts in the separate local-check store")
    parser.add_argument("--force-check", action="store_true",
                        help="elaborate selected modules even if --retain has a matching artifact")
    parser.add_argument("--seconds", type=int, default=30)
    parser.add_argument("--memory-mb", type=int, default=384)
    parser.add_argument("--rss-mb", type=int, default=768)
    parser.add_argument("--max-modules", type=int, default=6)
    parser.add_argument("--max-selected", type=int, default=1)
    args = parser.parse_args()
    try:
        limits = Limits(args.seconds, args.memory_mb, args.rss_mb, args.max_modules, args.max_selected)
        limits.validate()
        selected = list(dict.fromkeys(args.modules))
        if len(selected) > limits.max_selected:
            raise PilotError("too many selected compilation modules")
        root = Path(__file__).resolve().parents[1]
        check_configuration(root)
        ordered = closure(root, selected, limits)
        dependencies = [module for module in ordered if module not in selected]
        print("Selected: " + ", ".join(module for module in ordered if module in selected), flush=True)
        print("Dependencies requiring cache validation: " + (", ".join(dependencies) or "none"), flush=True)
        if not args.check:
            print("Plan only: no compiler, Lake process, or cache writes were launched.")
            return 0

        toolchain_name = (root / "lean-toolchain").read_text().strip().replace(":", "---").replace("/", "--")
        toolchain = Path.home() / ".elan/toolchains" / toolchain_name
        compiler, lake = toolchain / "bin/lean", toolchain / "bin/lake"
        if not compiler.is_file() or not lake.is_file():
            raise PilotError("pinned compiler/Lake is not installed; no download attempted")
        try:
            os.nice(15)
        except PermissionError:
            print("Low-priority scheduling unavailable; all other caps remain active.", flush=True)
        with exclusive_check(root), tempfile.TemporaryDirectory(prefix="thesis-cached-pilot-") as directory:
            temporary = Path(directory)
            tracked = [source_path(root, module) for module in ordered]
            tracked += [root / name for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")]
            fingerprints = {path: digest(path) for path in tracked}
            for source in tracked:
                destination = temporary / source.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, destination)
            # Keys describe copied source/configuration bytes, not mutable
            # filenames or Git status. They propagate edits through project
            # dependencies, while unrelated selected modules keep their keys.
            arguments = ["-j1", f"-M{limits.memory_mb}",
                         "-DmaxHeartbeats=400000", "-DmaxErrors=1"]
            store = ArtifactStore(root) if args.retain else None
            identity = toolchain_identity(toolchain) if store else None
            graph = {module: imports(source_path(temporary, module).read_text()) for module in ordered}
            keys = module_keys(ordered,
                {module: source_path(temporary, module) for module in ordered}, graph,
                {str(path.relative_to(temporary)): digest(path) for path in
                 [temporary / name for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")]} |
                {"checker": digest(Path(__file__)),
                 "artifact_policy": digest(Path(__file__).with_name("local_check_artifacts.py"))},
                identity, arguments) if store else {}
            retained = {module: artifact for module in dependencies
                        if store and (artifact := store.load(module, keys[module])) is not None}
            ordinary = ordinary_dependencies({module: graph[module] for module in dependencies}, retained)
            copy_dependencies(root, temporary, ordinary)
            if sum(path.stat().st_size for path in retained.values()) + sum(
                    (temporary / path).stat().st_size for module in ordinary
                    for path in cache_paths(module)) > 64 * 1024 * 1024:
                raise PilotError("combined dependency artifacts exceed the 64 MiB pilot limit")
            for module, artifact in retained.items():
                destination = temporary / cache_paths(module)[0]
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(artifact, destination)
                print(f"Using input-matched retained dependency: {module}", flush=True)
            environment = os.environ.copy()
            environment["LAKE_CACHE_DIR"] = str(temporary / "artifact-cache")
            environment["LEAN_PATH"] = os.pathsep.join((str(temporary / ".lake/build/lib/lean"),
                                                        str(toolchain / "lib/lean")))
            # Use only the copied dependency tree, with no downloads or
            # rebuilding. Lake's no-build mode may write .nobuild metadata;
            # any such metadata stays in this disposable workspace.
            if ordinary:
                print("Validating dependency traces without rebuilding:", flush=True)
                run_capped([str(lake), "--no-build", "--rehash", "--no-cache", "build"]
                           + [f"+{module}:olean" for module in ordinary],
                           temporary, environment, limits)
            for module in ordered:
                if module not in selected:
                    continue
                output = temporary.joinpath(".lake/build/lib/lean", *module.split(".")).with_suffix(".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                cached = store.load(module, keys[module]) if store and not args.force_check else None
                if cached is not None:
                    shutil.copyfile(cached, output)
                    print(f"Reused checked artifact (no re-elaboration): {module}", flush=True)
                    continue
                print(f"Checking {module} against the validated dependencies:", flush=True)
                run_capped([str(compiler), *arguments, "-R", str(temporary),
                            "-o", str(output), str(source_path(temporary, module))],
                           temporary, environment, limits)
                if store:
                    # Publish each completed module separately: failure of a
                    # later selected module must not discard an earlier real
                    # success. No compiler failure can reach this path.
                    if any(digest(path) != fingerprint for path, fingerprint in fingerprints.items()):
                        raise PilotError("sources changed during the check; output is not retained")
                    if toolchain_identity(toolchain) != identity:
                        raise PilotError("toolchain changed during the check; output is not retained")
                    store.publish(module, keys[module], output)
                    print(f"Retained checked artifact: {module}", flush=True)
            if any(digest(path) != fingerprint for path, fingerprint in fingerprints.items()):
                raise PilotError("sources changed during the pilot; result is not current")
            if store and toolchain_identity(toolchain) != identity:
                raise PilotError("toolchain changed during artifact reuse; result is not current")
        print("Selected modules checked or input-matched; ordinary Lake cache unchanged. "
              "Full build and axiom audit remain separate gates.")
        return 0
    except (PilotError, ArtifactError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"Pilot stopped: {error}", flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
