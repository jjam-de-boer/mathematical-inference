#!/usr/bin/env python3
"""Typecheck one Agda file inside a fixed heap and resident-memory ceiling.

The Agda process is started in its own process group. Resident memory is the
sum over that group. Crossing the ceiling kills the group. If process listing
is unavailable, the checker refuses to start.

This Agda build typechecks one file at a time and rejects a jobs flag, so the
process is already a single typechecking job. The runtime is held to one
capability, a 4608 MiB heap and a 64 MiB stack. The resident ceiling is
5120 MiB.
"""

import argparse
import os
import signal
import subprocess
import sys
import time

HEAP = "4608m"
STACK = "64m"
RSS_LIMIT_MB = 5120
POLL_SECONDS = 0.2


def processes():
    result = subprocess.run(
        ["/bin/ps", "-axo", "pid=,ppid=,pgid=,rss=,comm="],
        text=True,
        capture_output=True,
        timeout=2,
    )
    if result.returncode:
        raise SystemExit("process listing unavailable; refusing to start Agda")
    found = []
    for line in result.stdout.splitlines():
        fields = line.split(None, 4)
        if len(fields) != 5:
            raise SystemExit("unrecognized process listing; refusing to start Agda")
        pid, parent, group, rss, command = fields
        found.append((int(pid), int(parent), int(group), int(rss), command))
    return found


def group_rss_mb(rows, root):
    by_pid = {pid: row for pid, *row in ((row[0], row) for row in rows)}
    # `rows` entries are (pid, parent, group, rss, command).
    members = set()
    stack = [root]
    children = {}
    for pid, parent, group, rss, command in rows:
        children.setdefault(parent, []).append(pid)
    while stack:
        current = stack.pop()
        if current in members:
            continue
        members.add(current)
        stack.extend(children.get(current, []))
    # Also keep every process that shares the started session's group.
    root_group = None
    for pid, parent, group, rss, command in rows:
        if pid == root:
            root_group = group
    if root_group is not None:
        for pid, parent, group, rss, command in rows:
            if group == root_group:
                members.add(pid)
    total = 0
    for pid, parent, group, rss, command in rows:
        if pid in members:
            total += rss
    return total / 1024


def main():
    parser = argparse.ArgumentParser(description="Typecheck Agda under a memory ceiling")
    parser.add_argument("file")
    parser.add_argument("agda_args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    # Fail before launch if listing does not work.
    processes()
    command = [
        "agda",
        "+RTS",
        "-N1",
        f"-M{HEAP}",
        f"-K{STACK}",
        "-RTS",
        "--without-K",
        args.file,
        *args.agda_args,
    ]
    child = subprocess.Popen(command, start_new_session=True)
    peak = 0.0
    try:
        while True:
            try:
                rows = processes()
            except SystemExit as stop:
                os.killpg(child.pid, signal.SIGKILL)
                raise SystemExit(f"{stop}; killed the Agda process group") from stop
            rss = group_rss_mb(rows, child.pid)
            peak = max(peak, rss)
            if rss > RSS_LIMIT_MB:
                os.killpg(child.pid, signal.SIGKILL)
                raise SystemExit(
                    f"resident memory {rss:.1f} MiB exceeded {RSS_LIMIT_MB} MiB; killed the process group"
                )
            if child.poll() is not None:
                break
            time.sleep(POLL_SECONDS)
    except KeyboardInterrupt:
        os.killpg(child.pid, signal.SIGKILL)
        raise
    code = child.wait()
    print(f"group RSS peak {peak:.1f} MiB", file=sys.stderr)
    return code


if __name__ == "__main__":
    sys.exit(main())
