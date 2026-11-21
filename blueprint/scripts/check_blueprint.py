#!/usr/bin/env python3
"""Static checks and cross-chapter edge resolution for the Alpöge blueprint.

Usage: check_blueprint.py [--resolve] [--archive SRC] [--maps DIR]

Reads src/chapters/*.tex. For every node it collects \\label, \\lean{...},
\\uses{...} and `% uses-lean:` comment lines.

Checks (static, from source text; nothing is compiled):
  * every \\uses label exists;
  * every \\lean name is declared in the archive: a declaration line whose
    name, prefixed by the enclosing `namespace` blocks, equals the full name
    (Mathlib names, which are not in the archive, are reported separately);
  * no \\leanok / \\mathlibok anywhere.

--resolve rewrites each `% uses-lean: A, B` line into
    % uses-lean: A, B
    \\uses{lab_A, lab_B} % resolved
for names carried by some node's \\lean, replacing an earlier resolved line.
Names no node carries are listed as unresolved.  Writes check-report.json.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent
ENV = r"(definition|lemma|proposition|theorem|corollary|remark|example)"
BEGIN = re.compile(r"\\begin\{" + ENV + r"\}")
LABEL = re.compile(r"\\label\{([^}]*)\}")
LEAN = re.compile(r"\\lean\{([^}]*)\}")
USES = re.compile(r"\\uses\{([^}]*)\}")
USES_LEAN = re.compile(r"^(\s*)%\s*uses-lean:\s*(.*)$")
RESOLVED = re.compile(r"^\s*\\uses\{[^}]*\}\s*% resolved\s*$")
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+"
    r"(?:\([^)]*\)\s*)?([^\s:({\[]+)")
NS = re.compile(r"^\s*(namespace|end|section|noncomputable section)\b\s*([^\s-]*)")


def split_names(s: str) -> list[str]:
    return [x.strip().strip("`") for x in s.split(",") if x.strip().strip("`")]


def parse(files):
    nodes, uses = [], []
    for f in files:
        text = f.read_text()
        for m in BEGIN.finditer(text):
            env = m.group(1)
            end = text.find("\\end{" + env + "}", m.end())
            body = text[m.end():end]
            lab = LABEL.search(body)
            lean = [n for g in LEAN.findall(body) for n in split_names(g)]
            nodes.append({"file": f.name, "env": env,
                          "label": lab.group(1) if lab else None, "lean": lean})
        for lineno, line in enumerate(text.splitlines(), 1):
            if line.lstrip().startswith("%"):
                continue
            for g in USES.findall(line):
                uses += [(f.name, lineno, x) for x in split_names(g)]
    return nodes, uses


def ns_at(lines, upto):
    stack = []
    for line in lines[:upto]:
        m = NS.match(line)
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        if kind == "namespace":
            stack.append(("ns", name))
        elif kind in ("section", "noncomputable section"):
            stack.append(("sec", name))
        elif kind == "end" and stack:
            stack.pop()
    return ".".join(n for k, n in stack if k == "ns" and n)


def decl_at(path: Path, ln: int, full: str) -> bool:
    try:
        lines = path.read_text().splitlines()
    except OSError:
        return False
    i = ln - 1
    if not 0 <= i < len(lines):
        return False
    # allow attributes/docstrings: look at this line and the next two
    for j in range(i, min(i + 3, len(lines))):
        m = DECL.match(lines[j])
        if not m:
            continue
        name = m.group(2).removeprefix("_root_.")
        ns = ns_at(lines, j)
        cand = (ns + "." + name) if ns and not m.group(2).startswith("_root_.") else name
        if cand == full or full.endswith("." + name) and cand.endswith(full):
            return True
    return False


def declared(full: str, src: Path, hints: list[str], cache: dict) -> str | None:
    """Locator of the declaration of `full`: first the TSV hints, then a search."""
    for h in hints:
        path, _, ln = h.strip().partition(":")
        ln = ln.split()[0] if ln else ""
        if ln.isdigit() and decl_at(src / path, int(ln), full):
            return f"{path}:{ln}"
    last = full.split(".")[-1]
    if last not in cache:
        pat = (r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+"
               r"(\([^)]*\)\s*)?([^\s:({\[]*\.)?" + re.escape(last) + r"([\s:({\[]|$)")
        out = subprocess.run(["rg", "-n", "--no-heading", "-e", pat, str(src), "-g", "*.lean"],
                             capture_output=True, text=True).stdout
        cache[last] = [l.split(":", 2)[:2] for l in out.splitlines()]
    for path, ln in cache[last]:
        if decl_at(Path(path), int(ln), full):
            return f"{Path(path).relative_to(src)}:{ln}"
    return None


def load_hints(maps: Path) -> dict:
    hints = {}
    for t in sorted(maps.glob("*.tsv")):
        rows = t.read_text().splitlines()
        head = rows[0].split("\t")
        for r in rows[1:]:
            c = dict(zip(head, r.split("\t")))
            locs = [x for x in c.get("locators", "").split(",") if x.strip()]
            for n in c.get("lean_names", "").split(","):
                if n.strip():
                    hints.setdefault(n.strip().strip("`"), []).extend(locs)
    return hints


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--resolve", action="store_true")
    ap.add_argument("--archive", default=str(HERE.parent.parent / "refs/alpoge-lean/src"))
    a = ap.parse_args()
    src = Path(a.archive)
    files = sorted((HERE / "src/chapters").glob("*.tex"))
    nodes, _ = parse(files)
    by_lean = {}
    for n in nodes:
        for x in n["lean"]:
            by_lean.setdefault(x, n["label"])
    unresolved = {}
    if a.resolve:
        for f in files:
            out, lines = [], f.read_text().splitlines()
            for line in lines:
                if RESOLVED.match(line):
                    continue
                out.append(line)
                m = USES_LEAN.match(line)
                if m:
                    names = split_names(m.group(2))
                    labs = sorted({by_lean[x] for x in names if x in by_lean})
                    for x in names:
                        if x not in by_lean:
                            unresolved.setdefault(x, []).append(f.name)
                    if labs:
                        out.append(f"{m.group(1)}\\uses{{{', '.join(labs)}}} % resolved")
            f.write_text("\n".join(out) + "\n")
    nodes, uses = parse(files)
    labels = [n["label"] for n in nodes if n["label"]]
    dup = sorted({l for l in labels if labels.count(l) > 1})
    bad_uses = [u for u in uses if u[2] not in labels]
    cache, missing, located = {}, [], {}
    hints = load_hints(HERE / "maps")
    for n in nodes:
        for x in n["lean"]:
            loc = declared(x, src, hints.get(x, []), cache)
            if loc:
                located[x] = loc
            else:
                missing.append((n["label"], x))
    leanok = [str(f.name) for f in files if re.search(r"(?<!\|)\\(leanok|mathlibok)\b", f.read_text())]
    rep = {
        "nodes": len(nodes),
        "nodes_with_lean": sum(1 for n in nodes if n["lean"]),
        "lean_names": len(located) + len(missing),
        "lean_names_located": len(located),
        "lean_names_not_found_in_archive": missing,
        "edges": len(uses),
        "uses_to_missing_labels": bad_uses,
        "duplicate_labels": dup,
        "unresolved_uses_lean": unresolved,
        "files_with_leanok": leanok,
        "per_file": {f.name: sum(1 for n in nodes if n["file"] == f.name) for f in files},
    }
    (HERE / "check-report.json").write_text(json.dumps(rep, indent=1, ensure_ascii=False) + "\n")
    (HERE / "lean-locations.json").write_text(json.dumps(located, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
    short = {k: (len(v) if isinstance(v, (list, dict)) and k != "per_file" else v) for k, v in rep.items()}
    print(json.dumps(short, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
