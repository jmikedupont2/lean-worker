#!/usr/bin/env python3
"""Classify git artifacts named in a `locate` dump (locate-lean-worker.txt).

The dump is one absolute path per line. Branch, worktree, stash, and PR
records come from those paths. Uncommitted files are not stored in locate
output, so this script asks `git status` in each checkout the dump names
(skipping Lake package clones).

Usage:
  python3 classify-locate-lean-worker.py
  python3 classify-locate-lean-worker.py locate-lean-worker.txt -o out.json
  python3 classify-locate-lean-worker.py --no-status
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

SKIP_DIR_PARTS = {
    ".lake",
    "packages",
    "node_modules",
    ".nix",
}


def classify_path(path: str) -> str | None:
    """Return a single label for a locate path, or None if it is not an artifact."""
    if "/logs/" in path:
        return None
    if path.endswith("/refs/stash") or "/refs/stash/" in path:
        return "stash"
    if "/refs/pull/" in path:
        return "pr"
    if "/refs/heads/" in path:
        return "branch"
    if "/.git/worktrees/" in path:
        return "worktree"
    if "/worktrees/" in path and (path.endswith("/.git") or path.endswith("/.git/HEAD")):
        return "worktree"
    return None


def _after(path: str, marker: str) -> str | None:
    i = path.find(marker)
    if i < 0:
        return None
    rest = path[i + len(marker) :]
    return rest.split("/", 1)[0] or None


def branch_name(path: str) -> str | None:
    marker = "/refs/heads/"
    i = path.find(marker)
    if i < 0 or "/logs/" in path:
        return None
    name = path[i + len(marker) :].strip("/")
    return name or None


def pr_number(path: str) -> str | None:
    marker = "/refs/pull/"
    i = path.find(marker)
    if i < 0:
        return None
    num = path[i + len(marker) :].split("/", 1)[0]
    return num if num.isdigit() else None


def repo_of_git_meta(path: str) -> str | None:
    """Directory that owns a .git path (work tree or bare repo)."""
    if path.endswith("/.git"):
        return str(Path(path).parent)
    marker = "/.git/"
    i = path.find(marker)
    if i >= 0:
        return path[:i]
    if path.endswith(".git"):
        return path
    return None


def worktree_record(path: str) -> dict | None:
    if "/.git/worktrees/" in path:
        name = _after(path, "/.git/worktrees/")
        repo = repo_of_git_meta(path)
        if not name or not repo:
            return None
        return {"kind": "registered", "name": name, "repo": repo, "path": f"{repo}/.git/worktrees/{name}"}
    if "/worktrees/" in path and (path.endswith("/.git") or path.endswith("/.git/HEAD")):
        root = path[: -len("/.git/HEAD")] if path.endswith("/.git/HEAD") else path[: -len("/.git")]
        name = root.rstrip("/").split("/")[-1]
        return {"kind": "checkout", "name": name, "repo": root, "path": root}
    return None


def skip_checkout(root: str) -> bool:
    parts = set(Path(root).parts)
    return ".lake" in parts or "node_modules" in parts


def collect(lines: list[str]) -> dict:
    branches: dict[str, set[str]] = defaultdict(set)
    worktrees: dict[tuple, dict] = {}
    stashes: list[str] = []
    prs: dict[str, set[str]] = defaultdict(set)
    checkouts: set[str] = set()

    for raw in lines:
        path = raw.strip()
        if not path:
            continue
        label = classify_path(path)
        if label == "branch":
            name = branch_name(path)
            repo = repo_of_git_meta(path)
            if name and repo:
                branches[repo].add(name)
        elif label == "worktree":
            rec = worktree_record(path)
            if rec:
                worktrees[(rec["kind"], rec["path"])] = rec
                if rec["kind"] == "checkout":
                    checkouts.add(rec["path"])
        elif label == "stash":
            stashes.append(path)
        elif label == "pr":
            num = pr_number(path)
            repo = path.split("/refs/pull/", 1)[0]
            if num:
                prs[repo].add(num)
        if path.endswith("/.git") or path.endswith("/.git/HEAD"):
            root = repo_of_git_meta(path if path.endswith("/.git") else path[: -len("/HEAD")])
            if root and not skip_checkout(root):
                checkouts.add(root)

    return {
        "branches": {repo: sorted(names) for repo, names in sorted(branches.items())},
        "worktrees": sorted(worktrees.values(), key=lambda r: (r["kind"], r["path"])),
        "stashes": sorted(set(stashes)),
        "prs": {repo: sorted(nums, key=int) for repo, nums in sorted(prs.items())},
        "checkouts": sorted(checkouts),
    }


def git_status(root: Path, timeout: float) -> list[str]:
    try:
        proc = subprocess.run(
            ["git", "-C", str(root), "status", "--porcelain", "-uall"],
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return [f"! {exc}"]
    if proc.returncode != 0:
        err = (proc.stderr or proc.stdout or "git status failed").strip().splitlines()
        return [f"! {err[0][:200]}"] if err else ["! git status failed"]
    return [line for line in proc.stdout.splitlines() if line.strip()]


def git_stash(root: Path, timeout: float) -> list[str]:
    try:
        proc = subprocess.run(
            ["git", "-C", str(root), "stash", "list"],
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return []
    if proc.returncode != 0:
        return []
    return [line for line in proc.stdout.splitlines() if line.strip()]


def attach_live(data: dict, timeout: float) -> None:
    uncommitted: dict[str, list[str]] = {}
    live_stashes: dict[str, list[str]] = {}
    for root_s in data["checkouts"]:
        root = Path(root_s)
        if not root.is_dir():
            continue
        dirty = git_status(root, timeout)
        if dirty:
            uncommitted[root_s] = dirty
        st = git_stash(root, timeout)
        if st:
            live_stashes[root_s] = st
    data["uncommitted"] = uncommitted
    data["live_stashes"] = live_stashes


def summary(data: dict) -> str:
    n_branches = sum(len(v) for v in data["branches"].values())
    n_wt = len(data["worktrees"])
    n_pr = sum(len(v) for v in data["prs"].values())
    n_dirty = sum(len(v) for v in data.get("uncommitted", {}).values())
    lines = [
        f"branches: {n_branches} across {len(data['branches'])} repos",
        f"worktrees: {n_wt}",
        f"stash paths: {len(data['stashes'])}",
        f"live stashes: {sum(len(v) for v in data.get('live_stashes', {}).values())}",
        f"prs: {n_pr}",
        f"uncommitted lines: {n_dirty} across {len(data.get('uncommitted', {}))} checkouts",
        f"checkouts considered: {len(data['checkouts'])}",
    ]
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "locate_file",
        nargs="?",
        default="locate-lean-worker.txt",
        help="locate dump, one path per line",
    )
    parser.add_argument("-o", "--output", default="locate-lean-worker-classified.json")
    parser.add_argument("--no-status", action="store_true", help="do not run git status/stash")
    parser.add_argument("--timeout", type=float, default=20.0, help="per-checkout git timeout seconds")
    args = parser.parse_args(argv)

    src = Path(args.locate_file)
    if not src.is_file():
        print(f"missing {src}", file=sys.stderr)
        return 1
    lines = src.read_text(errors="replace").splitlines()
    data = collect(lines)
    data["source"] = str(src)
    data["lines"] = len(lines)
    if not args.no_status:
        attach_live(data, args.timeout)
    else:
        data["uncommitted"] = {}
        data["live_stashes"] = {}

    out = Path(args.output)
    out.write_text(json.dumps(data, indent=2) + "\n")
    print(summary(data))
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
