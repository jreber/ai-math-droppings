#!/usr/bin/env python3
"""Regenerate Propositio.lean from the actual Propositio/ tree, minus
excluded-from-aggregator.json. The single source of truth for what's "in" the
library build -- do not hand-edit Propositio.lean's import list.

Usage: python3 scripts/gen_root.py
"""
import glob
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main():
    with open(os.path.join(ROOT, "excluded-from-aggregator.json")) as f:
        excluded = set(json.load(f)["excluded"])

    mods = []
    for path in glob.glob(os.path.join(ROOT, "Propositio", "**", "*.lean"), recursive=True):
        mod = os.path.relpath(path, ROOT)[:-5].replace(os.sep, ".")
        if mod not in excluded:
            mods.append(mod)
    mods.sort()

    out = os.path.join(ROOT, "Propositio.lean")
    with open(out, "w") as f:
        for m in mods:
            f.write(f"import {m}\n")
    print(f"wrote {out}: {len(mods)} imports ({len(excluded)} excluded)")


if __name__ == "__main__":
    main()
