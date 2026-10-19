#!/usr/bin/env python3
"""Bootstrap the complete normal Lake cache, one bounded target at a time.

This is deliberately separate from check_module_cached: it asks Lake itself
to produce ordinary artifacts and genuine dependency traces in .lake/build.
No retained .olean is relabelled as a normal Lake result. Planning is the
default; --check opts into compilation. Successful intermediate targets remain
available after a resource stop, so another invocation resumes through Lake's
own freshness checks rather than restarting from an empty cache.

A temporary TOML configuration adds only weak Lean resource arguments. Lake
explicitly excludes weak arguments from mathematical build traces; thread and
memory limits change neither the source nor its proof. The committed package
configuration is never rewritten. Final gates also use the committed config.
The full process group (Lake plus its compiler/linker descendants) is sampled,
not just Lake's small parent process. This is still not a hard OS reservation.
"""

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import tempfile
import time

from check_module_cached import (Limits, PilotError, RESOURCE_PROFILES,
    check_configuration, digest, imports)
from local_check_artifacts import ArtifactError, exclusive_check


class BuildStopped(RuntimeError):
    """A resource/precondition stop is not a verified full build."""


@dataclass(frozen=True)
class Process:
    pid: int
    parent: int
    group: int
    rss_kib: int
    command: str


def processes():
    result = subprocess.run(["/bin/ps", "-axo", "pid=,ppid=,pgid=,rss=,comm="],
                            text=True, capture_output=True, timeout=2)
    if result.returncode:
        raise BuildStopped("process-group monitoring unavailable; refusing to launch")
    found = []
    for line in result.stdout.splitlines():
        fields = line.split(None, 4)
        if len(fields) != 5:
            raise BuildStopped("unrecognized process monitor output")
        try:
            found.append(Process(*(int(value) for value in fields[:4]), fields[4]))
        except ValueError as error:
            raise BuildStopped("invalid process monitor measurement") from error
    if not found:
        raise BuildStopped("empty process monitor result")
    return found


def group_measurement(snapshot, group):
    members = [process for process in snapshot if process.group == group]
    compilers = {process.pid for process in members
                 if Path(process.command).name in {"lean", "leanc", "cc", "clang", "clang++"}
                 or Path(process.command).name.startswith("clang-")}
    # A clang driver and its own frontend are one compiler family. Two
    # independent Lean/C compiler roots, however, violate sequential policy.
    roots = sum(process.pid in compilers and process.parent not in compilers
                for process in members)
    return sum(process.rss_kib for process in members) / 1024, roots


def kill_group(child):
    # Kill the owned group even if Lake exited before one of its descendants.
    # No unrelated compiler or editor process is ever a termination target.
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    child.wait()


def run_group(command, root, environment, limits, log, allowed=(0,)):
    processes()  # Monitoring must work before any build process starts.

    def cpu_limit():
        resource.setrlimit(resource.RLIMIT_CPU, (limits.seconds, limits.seconds + 1))

    started, peak = time.monotonic(), 0.0
    with log.open("w") as output:
        child = subprocess.Popen(command, cwd=root, env=environment, stdout=output,
            stderr=subprocess.STDOUT, start_new_session=True, preexec_fn=cpu_limit)
        try:
            while child.poll() is None:
                if time.monotonic() - started >= limits.seconds:
                    raise BuildStopped("wall-time limit (not a memory diagnosis)")
                rss, compiler_roots = group_measurement(processes(), child.pid)
                peak = max(peak, rss)
                if compiler_roots > 1:
                    raise BuildStopped("multiple compiler families detected; owned build stopped")
                if rss > limits.rss_mb:
                    raise BuildStopped("aggregate build-process RSS limit")
                time.sleep(0.05)
            result = child.wait()
            # A completed launcher must not leave an unmonitored compiler.
            if any(process.group == child.pid for process in processes()):
                raise BuildStopped("build launcher exited with descendants still running")
        except BaseException:
            kill_group(child)
            raise
    elapsed = time.monotonic() - started
    if result not in allowed:
        text = log.read_text()[-12000:]
        print(text, flush=True)
        cause = ("Lean memory threshold" if "excessive memory consumption" in text
                 else "CPU limit" if result == -signal.SIGXCPU
                 else "build error (see log)")
        raise BuildStopped(f"{cause}; exit={result}; wall={elapsed:.2f}s; "
                           f"sampled group RSS={peak:.1f} MiB; log={log}")
    return {"exit": result, "seconds": round(elapsed, 3), "group_rss_mib": round(peak, 1)}


def source_path(root, module):
    if module not in {"Main", "Thesis"} and not re.fullmatch(
            r"Thesis(?:\.[A-Za-z_][A-Za-z_0-9]*)+", module):
        raise BuildStopped(f"invalid project module: {module}")
    path = root.joinpath(*module.split(".")).with_suffix(".lean")
    if not path.is_file() or path.is_symlink():
        raise BuildStopped(f"missing or symbolic-link source: {module}")
    return path


def project_imports(source):
    # The small-module helper intentionally excludes the root facade. Adapt
    # that one ordinary header token in memory only, using an otherwise
    # impossible module spelling; source files presented to Lake are untouched.
    marker = "Thesis.__SequentialRootFacade"
    if marker in source:
        raise BuildStopped("reserved parser marker occurs in source")
    parsed = imports(re.sub(r"(?m)^import Thesis(?=\s|$)", "import " + marker, source))
    return ["Thesis" if module == marker else module for module in parsed]


def ordered_modules(root, targets):
    ordered, graph, visiting = [], {}, set()

    def visit(module):
        if module in visiting:
            raise BuildStopped(f"cyclic dependency: {module}")
        if module in graph:
            return
        visiting.add(module)
        dependencies = project_imports(source_path(root, module).read_text())
        for dependency in dependencies:
            visit(dependency)
        visiting.remove(module)
        graph[module] = dependencies
        ordered.append(module)

    for target in targets:
        visit(target)
    return ordered, graph


def resource_configuration(source, limits):
    if source.count("[[lean_lib]]") != 1:
        raise BuildStopped("unsupported configuration layout")
    args = json.dumps(["-j1", f"-M{limits.memory_mb}", "-DmaxErrors=1"])
    return source.replace("[[lean_lib]]", f"weakLeanArgs = {args}\n\n[[lean_lib]]", 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--profile", choices=RESOURCE_PROFILES, default="pilot")
    parser.add_argument("--seconds", type=int, default=30)
    parser.add_argument("--phase", choices=("lean", "native", "gates", "all"), default="all")
    parser.add_argument("--max-builds", type=int, default=None,
                        help="optional checkpoint after this many actual rebuilt targets")
    parser.add_argument("--target", action="append", default=None,
                        help="explicit intermediate module; final gates require default scope")
    args = parser.parse_args()
    try:
        memory, rss = RESOURCE_PROFILES[args.profile]
        limits = Limits(seconds=args.seconds, memory_mb=memory, rss_mb=rss)
        limits.validate()
        if args.max_builds is not None and args.max_builds < 1:
            raise BuildStopped("max-builds must be positive")
        root = Path(__file__).resolve().parents[1]
        check_configuration(root)
        targets = args.target or ["Main", "Thesis.AxiomAudit"]
        if args.target and args.phase in {"gates", "all"}:
            raise BuildStopped("intermediate targets require --phase lean or native")
        ordered, graph = ordered_modules(root, targets)
        print(f"Plan: {len(ordered)} modules; phase={args.phase}; "
              f"Lean={memory} MiB; aggregate RSS={rss} MiB; wall={limits.seconds}s; "
              "one compiler family", flush=True)
        if not args.check:
            print("Plan only; no compiler or cache writes.")
            return 0
        release = (root / "lean-toolchain").read_text().strip().replace(":", "---").replace("/", "--")
        lake = Path.home() / ".elan/toolchains" / release / "bin/lake"
        if not lake.is_file():
            raise BuildStopped("pinned Lake not installed; no download attempted")
        os.nice(15)
        with exclusive_check(root), tempfile.TemporaryDirectory(prefix="thesis-lake-resources-") as directory:
            build_cache = root / ".lake/build"
            if build_cache.is_symlink() or any(path.is_symlink() for path in build_cache.rglob("*")):
                raise BuildStopped("symbolic-link normal build artifacts require separate review")
            configuration = Path(directory) / "lakefile.toml"
            configuration.write_text(resource_configuration((root / "lakefile.toml").read_text(), limits))
            log_base = root / ".lake/local-builds-v1"
            if log_base.is_symlink():
                raise BuildStopped("symbolic-link log directory refused")
            log_base.mkdir(exist_ok=True)
            logs = Path(tempfile.mkdtemp(prefix=time.strftime("%Y%m%d-%H%M%S-"), dir=log_base))
            tracked = [source_path(root, module) for module in ordered]
            tracked += [root / name for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json")]
            fingerprints = {path: digest(path) for path in tracked}
            environment = os.environ.copy()
            environment["LAKE_CACHE_DIR"] = str(Path(directory) / "unused-cache")
            prefix = [str(lake), "--file", str(configuration), "--rehash", "--no-cache"]
            measurements, built, skipped = [], 0, 0

            def current():
                if any(digest(path) != value for path, value in fingerprints.items()):
                    raise BuildStopped("source/configuration changed; replan before continuing")

            def invoke(command, label, allowed=(0,)):
                log = logs / (f"{len(measurements):04d}-" + label.replace(":", "-") + ".log")
                result = run_group(command, root, environment, limits, log, allowed)
                measurements.append({"target": label, **result})
                (logs / "measurements.json").write_text(json.dumps(measurements, indent=2) + "\n")
                return result

            phases = ["lean", "native"] if args.phase == "all" else [args.phase]
            for phase in phases:
                if phase == "gates":
                    continue
                modules = ordered
                if phase == "native" and not args.target:
                    modules, _ = ordered_modules(root, ["Main"])
                for index, module in enumerate(modules, 1):
                    current()
                    facet = "olean" if phase == "lean" else "c.o"
                    target = "+" + module + ":" + facet
                    status = invoke(prefix + ["--no-build", "build", target], module + "-fresh-" + phase, (0, 3))
                    if status["exit"] == 0:
                        skipped += 1
                        if index % 50 == 0:
                            print(f"{phase}: {index}/{len(modules)}; rebuilt={built}; cached={skipped}", flush=True)
                        continue
                    # All prerequisite modules must already be current. Do
                    # not turn an unexpected dependency miss into a parallel
                    # rebuild, even though the group monitor is a second gate.
                    prerequisites = (["+" + dep + ":olean" for dep in graph[module]]
                                     if phase == "lean" else ["+" + module + ":olean"])
                    if prerequisites:
                        invoke(prefix + ["--no-build", "build", *prerequisites], module + "-deps-" + phase)
                    print(f"Rebuilding {index}/{len(modules)} {target}", flush=True)
                    result = invoke(prefix + ["build", target], module + "-build-" + phase)
                    current()
                    built += 1
                    print(f"Passed: {result['seconds']:.2f}s; group RSS={result['group_rss_mib']:.1f} MiB", flush=True)
                    if args.max_builds is not None and built >= args.max_builds:
                        print("Checkpoint only; complete local build NOT established. Resume through normal Lake cache.")
                        return 2
            if args.phase in {"all", "gates"}:
                current()
                # Finish any remaining executable link with resource flags
                # still available to Lean. Require the original configuration
                # to be wholly current BEFORE its actual final build commands,
                # so those commands cannot start an uncapped Lean rebuild.
                original = [str(lake), "--rehash", "--no-cache"]
                native_modules, _ = ordered_modules(root, ["Main"])
                invoke(original + ["--no-build", "build"] +
                       ["+" + module + ":c.o" for module in native_modules],
                       "all-native-prerequisites")
                current()
                invoke(prefix + ["build"], "finish-link")
                for command, label in ((["build"], "full-project"),
                                       (["build", "Thesis.AxiomAudit"], "axiom-audit")):
                    invoke(original + ["--no-build", *command], label + "-preflight")
                    current()
                    invoke(original + command, label)
                    current()
                print("FULL LOCAL BUILD AND AXIOM AUDIT PASSED using the committed configuration.")
            else:
                print("Intermediate phase passed; full build and audit NOT established.")
            return 0
    except (BuildStopped, PilotError, ArtifactError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"Sequential local build stopped: {error}", flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
