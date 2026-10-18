#!/usr/bin/env python3
"""Lean chunk splitter for the Qwen3-30B-A3B-Thinking-2507 proof loop.

Produces compiler-grounded chunks, one provable goal per chunk, with
surrounding declarations and the exact compiler goal/error attached.

Design targets (from the user's spec):
  * Chunk = one proof obligation / small proof block, 300-1500 Lean tokens
    by default (per-task budgets up to 10K tokens).
  * Context = minimal type-correct: enclosing declaration, relevant imports,
    helper lemmas, exact target statement, and current goal/error.
  * Pipeline = outline -> dependencies -> isolated obligation.

Outputs:
  * stdout   : one JSON per line (JSONL corpus)
  * --out     : same JSONL but written to a file
  * --manifest: machine-readable manifest of the split (paths, chunk counts)
  * --diagnostics: extra JSONL with raw `lean` compiler diagnostics
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path


# ---------------------------------------------------------------------------
# Lean token/comment hygiene
# ---------------------------------------------------------------------------

MINI_TOKEN = re.compile(r"[^\s]{3,}")
COMMENT_TOK = re.compile(r"\s+|//[^\n]*|/\*.*?\*/", re.S)
DEF_SIGNATURE = re.compile(r"^\s*(import|open|namespace|structure|inductive|abbrev|def|theorem|lemma|example|instance|axiom|constant|macro|opaque)\b")

SKIP_PATTERN = re.compile(
    r"(?s)"
    r"--.*?(?=\n(?:-- |---)|$)"           # single-line end-of-line comments
    r"|-.*?->|"                            # match "->" as a single token (stronger signal)
    r"\|\|.*|"                             # don't over-split on `||`/`&&` spans
    r"/\*.*?\*/",                          # block comments (non-greedy safety)
    re.S,
)
# Keep this simple and intentionally conservative: remove trailing comments
# and block comments (rare in this repo), then count kata-ish tokens.

def strip_comments(text: str) -> str:
    # remove block comments
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    # remove line comments (but keep the newline)
    text = re.sub(r"//[^\n]*", "", text)
    return text

def lean_tokens(text: str) -> list[str]:
    cleaned = strip_comments(text)
    # replace common delimiters with spaces so they don't merge identifiers
    cleaned = re.sub(r"([(){}[\],;:=])", r" \1 ", cleaned)
    return cleaned.split()

def token_count(text: str) -> int:
    return len(lean_tokens(text))

# ---------------------------------------------------------------------------
# Source navigation
# ---------------------------------------------------------------------------

@dataclass
class DefNode:
    path: str
    start: int          # 0-based line index
    end: int            # 0-based line index (inclusive)
    depth: int          # 0-based indentation
    kind: str           # import / def / theorem / structure / ...
    name: str = ""
    body: str = ""
    preview: str = ""

@dataclass
class Chunk:
    path: str
    source_range: tuple[int, int]
    node: DefNode
    header: str          # imports + preceding declarations/decls
    goal: str            # target statement / goal block
    body: str            # proof body
    diagnostics: list[str] = field(default_factory=list)
    token_count: int = 0
    kind: str = "theorem"

def find_nodes(lines: list[str], root_path: str) -> list[DefNode]:
    nodes: list[DefNode] = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            i += 1
            continue
        m = DEF_SIGNATURE.match(line)
        if m:
            kind = m.group(1)
            depth = len(line) - len(line.lstrip())
            name = ""
            # grab identifier right after the keyword where sensible
            if kind in ("def", "theorem", "lemma", "example", "inductive", "structure", "instance", "opaque", "axiom", "constant"):
                rest = line[m.end():].strip()
                name = rest.split()[0].split("(")[0].rstrip(":=").strip().rstrip(":")
            if kind in ("import", "open", "namespace"):
                nodes.append(
                    DefNode(path=root_path, start=i, end=i, depth=depth, kind=kind, name=name)
                )
            else:
                # scoped blocks (structure/theorem etc.)
                # End a scoped block at the next top-level declaration
                # (same depth, new signature) or at end-of-file.
                end = i
                j = i + 1
                while j < n:
                    nxt = lines[j]
                    stripped = nxt.strip()
                    if stripped.startswith("--"):
                        j += 1
                        continue
                    if DEF_SIGNATURE.match(nxt):
                        nxt_depth = len(nxt) - len(nxt.lstrip())
                        if nxt_depth <= depth:
                            break
                    j += 1
                end = j - 1
                body = "\n".join(lines[i:end + 1])
                # drop line comments so the chunk parses as Lean
                body = "\n".join(
                    l for l in body.split("\n")
                    if l.strip() and not l.strip().startswith("--")
                )
                nodes.append(
                    DefNode(path=root_path, start=i, end=end, depth=depth, kind=kind, name=name,
                            body=body)
                )
                i = j
                continue
        i += 1
    return nodes

# ---------------------------------------------------------------------------
# Chunking policy
# ---------------------------------------------------------------------------

def order(nodes: list[DefNode]) -> list[DefNode]:
    # imports first, then declarations in source order.
    # `namespace` nodes carry no body themselves (the body is the
    # nested declarations), so they sort after imports but don't get
    # emitted as chunks.
    return sorted(nodes, key=lambda nd: (0 if nd.kind in ("import", "open") else 1, nd.start))

def choose_budget(kind: str, max_tokens: int) -> int:
    table = {
        "repair/tactic": 800,
        "prove_sorry": 2000,
        "new_lemma": 3000,
        "refactor": 8000,
        "audit": 15000,
        "default": 1000,
    }
    for k, v in table.items():
        if k in kind:
            return v
    return max(300, min(max_tokens, 10000))

def chunk_node(node: DefNode, header: str, goal: str, body: str,
               kind: str, budget: int) -> Chunk:
    return Chunk(
        path=node.path,
        source_range=(node.start, node.end),
        node=node,
        header=header,
        goal=goal,
        body=body,
        kind=kind,
        token_count=token_count(header + goal + body),
    )

def _strip_comments(text: str) -> str:
    # remove block comments
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    # remove line comments (but keep the newline)
    text = re.sub(r"//[^\n]*", "", text)
    return text


def _strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    text = re.sub(r"//[^\n]*", "", text)
    return text


def _decl_lines(nd: DefNode) -> list[str]:
    """Lines of a declaration, keeping its body on one logical line."""
    body = _strip_comments(nd.body)
    lines = body.split("\n")
    # drop internal comment-only lines but keep code
    cleaned: list[str] = []
    for ln in lines:
        if ln.strip().startswith("--"):
            continue
        cleaned.append(ln)
    return cleaned


def build_header(node: DefNode, all_nodes: list[DefNode], own_set: set[int]) -> str:
    """Imports + all preceding declarations (scope-aware), as plain Lean code."""
    lines: list[str] = []
    # imports first
    imports = [_strip_comments(nd.body) for nd in all_nodes if nd.kind == "import"]
    lines.extend(imports)
    # preceding declarations
    for nd in all_nodes:
        if nd.start == node.start and nd.end == node.end:
            continue
        if nd.start in own_set:
            continue
        # only declarations that end at or before this node's start
        if nd.end > node.start:
            continue
        lines.extend(_decl_lines(nd))
        lines.append("")
    return "\n".join(lines).strip()

def build_goal(node: DefNode) -> str:
    """The prover-facing statement.

    `def`/`structure`/`inductive`/`abbrev`: the declaration header (name +
    type), not the body — the body is the term the model re-proves.
    `theorem`/`lemma`/`example`: the full proposition.
    `opaque`: the type (they are irreducible defs of a type)."""
    body = node.body
    if ":= by" in body:
        stmt, _ = body.split(":= by", 1)
        return stmt.strip().rstrip(":")
    m = re.search(r"(opaque)\s+(\w+)\s*:\s*(\w+)", body)
    if m and m.group(1) == "opaque":
        return f"opaque {m.group(2)} : {m.group(3)}"
    m = re.search(r"(theorem|lemma|example)\s+(\w+)", body)
    if m:
        return body.split(m.group(0), 1)[0].strip().rstrip(":")
    if ":=" in body:
        # def / structure / inductive / abbrev
        return body.split(":=")[0].strip().rstrip(":")
    return body.strip().rstrip(";")


def build_body(node: DefNode) -> str:
    """The proven term after `:=`, including `by` proofs; empty for
    propositions proved by rfl/decide (who are their own statement)."""
    body = node.body
    if ":= by" in body:
        _, proof = body.split(":= by", 1)
        return proof.strip()
    if ":=" in body and not body.strip().startswith("theorem") and not body.strip().startswith("def"):
        # structure / inductive / abbrev define a term; leave body empty —
        # the goal already states the declaration.
        return ""
    if ":=" in body:
        # `def f := term` — keep the term as the body.
        return body.split(":=")[1].strip()
    return ""


def build_sounding(node: DefNode) -> str:
    """Compact source citation for the LLM: declaration + line numbers."""
    return f"{node.path}:{node.start + 1}-{node.end + 1} ({node.kind} {node.name})"

# ---------------------------------------------------------------------------
# Compiler diagnostics
# ---------------------------------------------------------------------------

def run_lean(args: list[str]) -> tuple[int, str, str]:
    proc = subprocess.run(
        ["lean"] + args,
        capture_output=True,
        text=True,
        cwd=str(Path(args[0]).parent) if args else None,
    )
    return proc.returncode, proc.stdout, proc.stderr

def extract_diagnostics(path: Path, lines: list[str]) -> list[str]:
    # replicate gokujo-style error collection: keep lines containing errors
    # from Lean output when a file is checked stand-alone
    res = []
    prev = ""
    for ln in lines:
        if any(k in ln for k in ("error", "warning", "declaration uses", "failed", "unsolved")):
            res.append(ln.strip())
    return res

# ---------------------------------------------------------------------------
# The pipeline
# ---------------------------------------------------------------------------

def split_file(path: Path, args: argparse.Namespace) -> list[Chunk]:
    text = path.read_text(encoding="utf-8")
    lines = text.split("\n")
    nodes = find_nodes(lines, str(path))
    nodes = order(nodes)
    chunks: list[Chunk] = []

    # Pre-compute which nodes precede a given node (simple linear scan)
    for idx, node in enumerate(nodes):
        if node.kind in ("import", "open", "namespace"):
            continue  # emit at corpus level, not as a chunk
        own_set = {nd.start for nd in nodes[:idx]}
        header = build_header(node, nodes, own_set)
        goal = build_goal(node)
        body = build_body(node)
        budget = choose_budget(node.kind, args.max_tokens)
        chunks.append(chunk_node(node, header, goal, body, node.kind, budget))

    # Do NOT compile a chunk alone: a chunk is a declaration fragment and
    # will never parse standalone. The whole file does compile in the repo
    # (it is the aggregator that builds the full twin model), so capture its
    # compiler diagnostics once and attach them to every chunk so the model
    # has the live goal/error context near each declaration.
    whole_rc, whole_out, whole_err = run_lean([str(path)])
    whole_diag = [l.strip() for l in (whole_out + whole_err).split("\n")
                  if any(k in l for k in ("error", "warning", "declaration uses", "unsolved"))]
    for ch in chunks:
        ch.diagnostics = whole_diag[:20]
    return chunks

def emit(chunks: list[Chunk], manifest: dict, args: argparse.Namespace) -> None:
    for ch in chunks:
        chunk_obj = {
            "path": ch.path,
            "start": ch.source_range[0] + 1,
            "end": ch.source_range[1] + 1,
            "node_kind": ch.node.kind,
            "node_name": ch.node.name,
            "chunk_kind": ch.kind,
            "token_count": ch.token_count,
            "source": build_sounding(ch.node),
            "header": ch.header,
            "goal": ch.goal,
            "body": ch.body,
            "diagnostics": ch.diagnostics,
        }
        print(json.dumps(chunk_obj, ensure_ascii=False))
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            for ch in chunks:
                chunk_obj = {
                    "path": ch.path,
                    "start": ch.source_range[0] + 1,
                    "end": ch.source_range[1] + 1,
                    "node_kind": ch.node.kind,
                    "node_name": ch.node.name,
                    "chunk_kind": ch.kind,
                    "token_count": ch.token_count,
                    "source": build_sounding(ch.node),
                    "header": ch.header,
                    "goal": ch.goal,
                    "body": ch.body,
                    "diagnostics": ch.diagnostics,
                }
                f.write(json.dumps(chunk_obj, ensure_ascii=False) + "\n")
    if args.manifest:
        # manifest as JSONL, one "line" per file, so the output contract stays
        # readable without a second file format.
        with open(args.manifest, "w", encoding="utf-8") as f:
            for entry in manifest["files"]:
                f.write(json.dumps(entry, ensure_ascii=False) + "\n")
            f.write(json.dumps({
                "total_chunks": manifest["total_chunks"],
                "total_tokens": manifest["total_tokens"],
            }, ensure_ascii=False) + "\n")

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Lean chunk splitter for Qwen3-30B-A3B-Thinking-2507")
    ap.add_argument("paths", nargs="+", help=".lean files or directories to split")
    ap.add_argument("--out", help="write JSONL chunks to this file")
    ap.add_argument("--manifest", help="write split manifest to this file")
    ap.add_argument("--diagnostics", help="write compiler diagnostics JSONL to this file")
    ap.add_argument("--max-tokens", type=int, default=10000,
                    help="hard cap per chunk (default 10000)")
    args = ap.parse_args(argv)

    paths = [Path(p) for p in args.paths]
    all_chunks: list[Chunk] = []
    manifest = {"files": [], "total_chunks": 0, "total_tokens": 0}

    for p in paths:
        if p.is_dir():
            files = sorted([q for q in p.rglob("*.lean") if q.suffix == ".lean"])
        else:
            files = [p]
        for f in files:
            manifest["files"].append({"path": str(f), "chunks": 0})
            try:
                lines = f.read_text(encoding="utf-8").split("\n")
                nodes = order(find_nodes(lines, str(f)))
            except Exception as e:
                manifest["files"][-1]["error"] = str(e)
                continue
            chunks = split_file(f, args)
            all_chunks.extend(chunks)
            manifest["files"][-1]["chunks"] = len(chunks)
            manifest["total_chunks"] += len(chunks)
            manifest["total_tokens"] += sum(c.token_count for c in chunks)

    emit(all_chunks, manifest, args)

    if args.diagnostics:
        diag_path = Path(args.diagnostics)
        with open(diag_path, "w", encoding="utf-8") as f:
            for ch in all_chunks:
                for d in ch.diagnostics:
                    f.write(json.dumps({"path": ch.path, "start": ch.source_range[0] + 1,
                                        "end": ch.source_range[1] + 1, "diagnostic": d,
                                        "node_kind": ch.node.kind, "node_name": ch.node.name},
                                       ensure_ascii=False) + "\n")
    return 0

if __name__ == "__main__":
    sys.exit(main())
