"""Private, input-addressed artifacts for the capped single-module checker.

These are not Lake traces and are never written into Lake's ordinary library
directory. A retained module can be imported by a later capped check only when
its source/configuration/dependency keys and pinned-toolchain identity still
match. Every retained artifact is also hashed before use. A cache hit reports
reuse, not a fresh elaboration or a project-wide axiom check.

The store is local build state, not a hostile-input proof-certificate format.
Like an ordinary build cache, it trusts the installed pinned standard library
and the local account that owns the artifacts. Missing entries are misses;
malformed or modified entries are refused rather than silently trusted.
Compiler coordination is shared across linked worktrees; artifacts remain
local to the calling worktree.
"""

from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import tempfile


class ArtifactError(RuntimeError):
    """A cache/locking refusal never counts as a successful proof check."""


# TMPDIR may differ between workers or worktrees. The fixed Unix temporary
# root gives updated helpers one host-wide location; the checked UID directory
# below it is private. Build artifacts still use their worktree-local stores.
COMPILER_LOCK_ROOT = Path("/tmp")


def digest(path):
    """Hash large runtime files with bounded Python memory, not read_bytes()."""
    result = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def record_key(record):
    return hashlib.sha256(json.dumps(record, sort_keys=True,
                                     separators=(",", ":")).encode()).hexdigest()


def checked_directory(path):
    """Do not follow a cache-directory symlink into unrelated user files."""
    if path.is_symlink() or (path.exists() and not path.is_dir()):
        raise ArtifactError(f"cache directory is not an ordinary directory: {path}")
    path.mkdir(exist_ok=True)
    return path


def store_directory(root):
    checked_directory(root / ".lake")
    return checked_directory(root / ".lake" / "local-checks-v1")


def compiler_repository(root):
    """Identify the shared repository without writing to any worktree.

    Linked worktrees have different .git files but one canonical common Git
    directory. Git resolves that relationship; a broken Git identity is a
    refusal rather than a fallback to separate, falsely independent slots.
    Plain source archives and temporary non-Git fixtures retain a slot keyed
    to their own canonical directory.
    """
    root = Path(root).resolve()
    if not any((parent / ".git").exists() or (parent / ".git").is_symlink()
               for parent in (root, *root.parents)):
        return "directory:" + str(root)
    environment = {key: value for key, value in os.environ.items()
                   if key not in {"GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE"}}
    try:
        result = subprocess.run(["git", "--no-optional-locks", "-C", str(root),
            "rev-parse", "--path-format=absolute", "--git-common-dir"],
            env=environment, text=True, capture_output=True, timeout=5)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise ArtifactError("cannot determine the shared Git compiler slot") from error
    identity = result.stdout.rstrip("\n")
    if result.returncode or not identity or "\n" in identity:
        raise ArtifactError("cannot determine the shared Git compiler slot")
    common = Path(identity)
    if not common.is_absolute() or not common.is_dir():
        raise ArtifactError("invalid shared Git compiler-slot directory")
    return "git:" + str(common.resolve())


def compiler_lock_path(root):
    """Keep one private, per-user OS lock per repository, outside its caches.

    Worktrees keep their own artifacts. Only this empty coordination file is
    shared; its existence is not evidence of a live build. The private parent
    prevents another account from replacing lock files in a shared /tmp.
    """
    identity = compiler_repository(root)
    directory = COMPILER_LOCK_ROOT / f"thesis-lean-compiler-{os.getuid()}"
    try:
        directory.mkdir(mode=0o700, exist_ok=True)
        info = directory.lstat()
    except OSError as error:
        raise ArtifactError("cannot open the private compiler-slot directory") from error
    if (not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid()
            or (stat.S_IMODE(info.st_mode) & 0o777) != 0o700):
        raise ArtifactError("compiler-slot directory must be private and not a symbolic link")
    key = record_key({"format": 1, "repository": identity})
    return directory / (key + ".lock")


@contextmanager
def held_compiler_lock(lock):
    """Hold a descriptor lock; failure or process exit releases the slot."""
    if lock.is_symlink():
        raise ArtifactError("refusing a symbolic-link compiler-slot lock")
    flags = os.O_CREAT | os.O_RDWR | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(lock, flags, 0o600)
    except OSError as error:
        raise ArtifactError("cannot open the compiler-slot lock") from error
    with os.fdopen(descriptor, "w") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ArtifactError("another capped local check owns the compiler slot") from error
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


@contextmanager
def exclusive_check(root):
    """Serialize updated helpers across every worktree of this repository.

    Keep the old local lock as well, so an older helper in this same worktree
    still causes a refusal. Other worktrees must use this updated helper to
    join the shared protocol; running old helpers and manual/editor builds
    still require coordination. No process is killed, no cache is shared, and
    no memory or time limit is changed by acquiring either lock.

    Both locks belong to open descriptors, not PID files. A crash releases
    them automatically; stale empty files never reserve the compiler slot.
    """
    shared = compiler_lock_path(root)
    local = store_directory(root) / "check.lock"
    with held_compiler_lock(shared), held_compiler_lock(local):
        yield


def toolchain_identity(toolchain):
    """Pin the compiler/runtime bytes as well as the release's directory name.

    Standard-library modules belong to the trusted installed toolchain, as in
    normal Lake builds. Its root module headers are included as additional
    accidental-change guards; this is not an audit of a tampered installation.
    """
    runtime = "libleanshared.dylib" if os.uname().sysname == "Darwin" else "libleanshared.so"
    files = [Path("bin/lean"), Path("lib/lean") / runtime,
             Path("lib/lean/Init.olean"), Path("lib/lean/Std.olean")]
    if any(not (toolchain / name).is_file() for name in files):
        raise ArtifactError("pinned compiler/runtime identity files are unavailable")
    return {"release": toolchain.name, "system": os.uname().sysname,
            "machine": os.uname().machine,
            "files": {str(name): digest(toolchain / name) for name in files}}


def module_keys(ordered, sources, dependencies, configuration, identity, compiler_args):
    """A dependency edit invalidates every dependent key, not unrelated modules.

    Sources here are the copied bytes actually presented to Lean. The ordinary
    dependencies still need Lake freshness validation before these keys can
    authorize reuse. A matching key alone never authorizes an unchecked module.
    """
    keys = {}
    for module in ordered:
        keys[module] = record_key({"format": 1, "module": module,
            "source": digest(sources[module]), "configuration": configuration,
            "toolchain": identity, "compiler_args": compiler_args,
            "dependencies": {name: keys[name] for name in dependencies[module]}})
    return keys


def ordinary_dependencies(dependencies, retained):
    """Avoid asking Lake to validate a trace against an untraced retained input.

    Retained artifacts intentionally have no fabricated Lake traces. A normal
    cached client of one must therefore be selected for checking too, rather
    than silently accepting a stale normal trace or letting Lake rebuild it.
    """
    ordinary = [module for module in dependencies if module not in retained]
    for module in ordinary:
        for imported in dependencies[module]:
            if imported in retained:
                raise ArtifactError(f"ordinary cached {module} imports retained {imported}; "
                                    "select the cached client for compilation as well")
    return ordinary


class ArtifactStore:
    def __init__(self, root):
        self.directory = store_directory(root)

    def entry(self, module, key):
        if not re.fullmatch(r"Thesis(?:\.[A-Za-z_][A-Za-z_0-9]*)+", module):
            raise ArtifactError("invalid retained module name")
        if not re.fullmatch(r"[0-9a-f]{64}", key):
            raise ArtifactError("invalid retained input key")
        parent = self.directory
        for component in module.split("."):
            parent = parent / component
            if parent.is_symlink():
                raise ArtifactError("refusing a symbolic-link artifact directory")
        entry = parent / key
        if entry.is_symlink():
            raise ArtifactError("refusing a symbolic-link artifact entry")
        return entry

    def load(self, module, key):
        entry = self.entry(module, key)
        if not entry.exists():
            return None
        manifest, artifact = entry / "checked.json", entry / "module.olean"
        if any(path.is_symlink() or not path.is_file() for path in (manifest, artifact)):
            raise ArtifactError(f"incomplete retained artifact for {module}")
        if manifest.stat().st_size > 4096 or artifact.stat().st_size > 64 * 1024 * 1024:
            raise ArtifactError(f"retained entry exceeds the bounded format for {module}")
        try:
            metadata = json.loads(manifest.read_text())
        except (ValueError, OSError) as error:
            raise ArtifactError(f"invalid retained manifest for {module}") from error
        expected = {"format": 1, "module": module, "input_key": key,
                    "artifact_sha256": digest(artifact)}
        if metadata != expected:
            raise ArtifactError(f"retained artifact or manifest changed for {module}")
        return artifact

    def publish(self, module, key, artifact):
        """Publish only an output whose compiler succeeded and inputs stayed fresh.

        The caller holds exclusive_check and checks input freshness first. Each
        file replacement is atomic. An interruption between the two replaces
        leaves a refused hash mismatch, never an accepted partial result. Prior
        successful modules remain reusable if a later selected module fails.
        """
        entry = self.entry(module, key)
        parent = self.directory
        for component in module.split(".") + [key]:
            parent = checked_directory(parent / component)
        artifact_hash = digest(artifact)
        metadata = {"format": 1, "module": module, "input_key": key,
                    "artifact_sha256": artifact_hash}
        with tempfile.TemporaryDirectory(prefix="publish-", dir=entry) as directory:
            temporary = Path(directory)
            shutil.copyfile(artifact, temporary / "module.olean")
            (temporary / "checked.json").write_text(json.dumps(metadata, sort_keys=True) + "\n")
            os.replace(temporary / "module.olean", entry / "module.olean")
            os.replace(temporary / "checked.json", entry / "checked.json")
        return self.load(module, key)
