#!/usr/bin/env python3
"""Batched '#print axioms' audit over every declaration in every successfully-built
Propositio module. Requires a completed `lake build Propositio` (reads cached
oleans only -- no recompilation). Writes /tmp/axiom_audit_batch_*.log files that
export_graph.py's log-miner will pick up on its next run.

Usage: python3 scripts/audit_axioms.py [--batch-size 25]
"""
import argparse
import glob
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROP_DIR = os.path.join(ROOT, "Propositio")
DECL_RE = re.compile(r"^(theorem|lemma)\s+([A-Za-z0-9_'.]+)", re.MULTILINE)
NS_OPEN_RE = re.compile(r"^namespace\s+([A-Za-z0-9_'.]+)", re.MULTILINE)
NS_CLOSE_RE = re.compile(r"^end\s+([A-Za-z0-9_'.]*)", re.MULTILINE)


def module_name_for(path):
    return os.path.relpath(path, ROOT)[:-5].replace(os.sep, ".")


def qualified_decls(path):
    """Walk the file top-to-bottom tracking the open namespace stack so each
    theorem/lemma gets its fully-qualified name."""
    with open(path, errors="ignore") as f:
        lines = f.readlines()
    stack = []
    out = []
    for line in lines:
        m = NS_OPEN_RE.match(line)
        if m:
            stack.append(m.group(1))
            continue
        m = NS_CLOSE_RE.match(line)
        if m:
            if stack:
                stack.pop()
            continue
        m = DECL_RE.match(line)
        if m:
            name = m.group(2)
            qualified = ".".join(stack + [name]) if stack else name
            out.append(qualified)
    return out


def has_olean(mod):
    p = os.path.join(ROOT, ".lake", "build", "lib", "lean", mod.replace(".", "/") + ".olean")
    return os.path.exists(p) and os.path.getsize(p) > 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--batch-size", type=int, default=20)
    args = ap.parse_args()

    files = sorted(glob.glob(os.path.join(PROP_DIR, "**", "*.lean"), recursive=True))
    jobs = []  # (module, [qualified_decl_names])
    for f in files:
        mod = module_name_for(f)
        if not has_olean(mod):
            continue
        decls = qualified_decls(f)
        if decls:
            jobs.append((mod, decls))

    total_decls = sum(len(d) for _, d in jobs)
    print(f"{len(jobs)} built modules, {total_decls} declarations to audit", file=sys.stderr)

    batch_num = 0
    i = 0
    env = dict(os.environ)
    while i < len(jobs):
        batch = jobs[i:i + args.batch_size]
        i += args.batch_size
        batch_num += 1
        tmp = os.path.join(ROOT, f"_audit_batch_{batch_num}.lean")
        with open(tmp, "w") as f:
            for mod, _ in batch:
                f.write(f"import {mod}\n")
            for mod, decls in batch:
                for d in decls:
                    f.write(f"#print axioms {d}\n")
        logpath = f"/tmp/axiom_audit_batch_{batch_num}.log"
        print(f"batch {batch_num}: {len(batch)} modules -> {logpath}", file=sys.stderr)
        with open(logpath, "w") as logf:
            subprocess.run(
                ["lake", "env", "lean", tmp],
                cwd=ROOT, env=env, stdout=logf, stderr=subprocess.STDOUT, timeout=300,
            )
        os.remove(tmp)

    print(f"done: {batch_num} batches", file=sys.stderr)


if __name__ == "__main__":
    main()
