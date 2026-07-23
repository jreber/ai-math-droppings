#!/usr/bin/env python3
"""Export a graph.json describing the Propositio/ Lean tree for the explorer.

Self-contained: reads only Propositio/**/*.lean (source of truth) plus, if
present, the build logs left in /tmp/*build*.log from a `lake build` run
(mined for '... depends on axioms: [...]' lines -- no live Lean invocation
needed here; the caller is expected to have already run `lake build`).

No dependency on ai-math's KB: any "headline"/"status" signal is either
parsed from a structured block in the file's own module docstring (see
CONVENTION below) or inferred heuristically when that block is absent.

CONVENTION (optional, add to a file's module docstring `/-! ... -/` block
to get first-class treatment instead of heuristic guesses):

    Status: <free text, e.g. "PROVED, unconditional">
    Source: <paper citation or "original construction">
    Headline: true

Usage:
    python3 scripts/export_graph.py [--out docs/explorer/graph.json]
"""
import argparse
import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROP_DIR = os.path.join(ROOT, "Propositio")

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.MULTILINE)
DECL_RE = re.compile(r"^(theorem|lemma|def)\s+([A-Za-z0-9_'.]+)", re.MULTILINE)
DOC_RE = re.compile(r"/-!(.*?)-/", re.DOTALL)
DECL_DOC_RE = re.compile(r"/--(.*?)-/\s*\n\s*(theorem|lemma)\s+([A-Za-z0-9_'.]+)", re.DOTALL)
STRUCT_FIELD_RE = re.compile(r"^\s*(Status|Source|Headline)\s*:\s*(.+)$", re.MULTILINE)
AXIOM_LINE_RE = re.compile(
    r"'([A-Za-z0-9_'.]+)' depends on axioms: \[([^\]]*)\]"
)
CLEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def module_name_for(path):
    rel = os.path.relpath(path, ROOT)[:-5]
    return rel.replace(os.sep, ".")


def parse_file(path):
    with open(path, errors="ignore") as f:
        text = f.read()
    mod = module_name_for(path)
    imports = [m for m in IMPORT_RE.findall(text) if m.startswith("Propositio")]
    decls = [name for kind, name in DECL_RE.findall(text)]
    doc_match = DOC_RE.search(text)
    docstring = doc_match.group(1).strip() if doc_match else ""
    struct = {}
    if doc_match:
        for key, val in STRUCT_FIELD_RE.findall(doc_match.group(1)):
            struct[key.strip().lower()] = val.strip()
    decl_docs = {}
    for doc, kind, name in DECL_DOC_RE.findall(text):
        decl_docs[name] = " ".join(doc.strip().split())
    # conservative sorry check: an actual `sorry` tactic token outside comments/docstrings
    code_only = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    code_only = re.sub(r"--.*", "", code_only)
    has_sorry = bool(re.search(r"\bsorry\b", code_only))
    has_axiom_decl = bool(re.search(r"^axiom\s", code_only, re.MULTILINE))
    return {
        "module": mod,
        "path": os.path.relpath(path, ROOT),
        "imports": sorted(set(imports)),
        "declarations": decls,
        "declDocs": decl_docs,
        "docstring": docstring,
        "struct": struct,
        "hasSorry": has_sorry,
        "hasAxiomDecl": has_axiom_decl,
        "sizeBytes": len(text),
    }


def mine_axioms_from_logs():
    """theorem short-name -> sorted axiom list, module -> worst tier, from any
    /tmp/*build*.log left by a `lake build` run."""
    theorem_axioms = {}
    # broad glob: ad-hoc build-log filenames vary session to session (build/verify/audit/...)
    # and the axiom-line regex is specific enough that scanning extra unrelated logs is harmless
    logpaths = glob.glob("/tmp/*.log")
    for logpath in logpaths:
        try:
            with open(logpath, errors="ignore") as f:
                text = f.read()
        except OSError:
            continue
        for thname, axlist in AXIOM_LINE_RE.findall(text):
            axioms = sorted(a.strip() for a in axlist.split(",") if a.strip())
            theorem_axioms[thname] = axioms
    return theorem_axioms


def tier_for_axioms(axioms):
    if axioms is None:
        return "unknown"
    axset = set(axioms)
    if axset <= CLEAN_AXIOMS:
        return "clean"
    if "sorryAx" in axset:
        return "sorry"
    if any("native_decide" in a or "ofReduceBool" in a for a in axioms):
        return "native_decide"
    if axset - CLEAN_AXIOMS:
        return "custom_axiom"
    return "clean"


MECHANICAL_RE = re.compile(r"^(.*?)([A-Z]|_?\d+)$")


def detect_families(nodes):
    """Group files sharing a stem + trailing numeric/letter suffix (>=3 siblings)
    into a collapsed meta-family, e.g. ThirteenL25_0..39, ResidueDescent65536A..H."""
    by_stem = {}
    for n in nodes:
        leaf = n["id"].rsplit(".", 1)[-1]
        m = re.match(r"^(.*?)(_?\d+|[A-H])$", leaf)
        if not m:
            continue
        stem = n["id"].rsplit(".", 1)[0] + "." + m.group(1)
        by_stem.setdefault(stem, []).append(n["id"])
    families = {}
    for stem, members in by_stem.items():
        if len(members) >= 4:
            families[stem] = sorted(members)
    return families


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=os.path.join(ROOT, "docs", "explorer", "graph.json"))
    args = ap.parse_args()

    files = sorted(glob.glob(os.path.join(PROP_DIR, "**", "*.lean"), recursive=True))
    parsed = [parse_file(f) for f in files]
    theorem_axioms = mine_axioms_from_logs()

    nodes = []
    for p in parsed:
        # "domain" = the grouping used for the overview map. Normally the first path segment
        # (Propositio.<X>.leaf -> X), but NumberTheory alone has real further subdivision
        # (Collatz/Beal/Diophantine/Analytic/Zsygmondy/ErdosStraus each with 30-230+ files) --
        # grouping all of it as one "NumberTheory" bubble would swallow ~90% of the library
        # into one illegible node, so it goes one level deeper there specifically.
        domain_parts = p["module"].split(".")
        if len(domain_parts) > 1 and domain_parts[1] == "NumberTheory" and len(domain_parts) > 3:
            domain = "NumberTheory." + domain_parts[2]
        elif len(domain_parts) > 1:
            domain = domain_parts[1]
        else:
            domain = "Propositio"
        # axiom tier: worst across declarations we have log data for
        decl_axioms = {d: theorem_axioms[d] for d in p["declarations"] if d in theorem_axioms}
        # also match qualified names (Namespace.decl) since docs use short names
        for full_name, axlist in theorem_axioms.items():
            short = full_name.rsplit(".", 1)[-1]
            if short in p["declarations"] and short not in decl_axioms:
                decl_axioms[short] = axlist
        tiers = [tier_for_axioms(ax) for ax in decl_axioms.values()]
        if p["hasAxiomDecl"]:
            overall_tier = "custom_axiom"
        elif p["hasSorry"]:
            overall_tier = "sorry"
        elif "custom_axiom" in tiers:
            overall_tier = "custom_axiom"
        elif "native_decide" in tiers:
            overall_tier = "native_decide"
        elif "clean" in tiers:
            overall_tier = "clean"
        else:
            overall_tier = "unknown"

        headline = False
        struct_headline = p["struct"].get("headline", "").lower()
        if struct_headline in ("true", "yes"):
            headline = True
        elif re.search(r"\b(capstone|headline|main theorem)\b", p["docstring"], re.IGNORECASE):
            headline = True

        nodes.append({
            "id": p["module"],
            "path": p["path"],
            "domain": domain,
            "leaf": p["module"].rsplit(".", 1)[-1],
            "imports": p["imports"],
            "declarations": p["declarations"],
            "declDocs": p["declDocs"],
            "docstring": p["docstring"][:4000],
            "status": p["struct"].get("status"),
            "source": p["struct"].get("source"),
            "headline": headline,
            "axiomTier": overall_tier,
            "declAxioms": decl_axioms,
            "sizeBytes": p["sizeBytes"],
        })

    node_ids = {n["id"] for n in nodes}
    edges = []
    for n in nodes:
        for imp in n["imports"]:
            if imp in node_ids:
                edges.append({"from": n["id"], "to": imp})

    indeg = {n["id"]: 0 for n in nodes}
    outdeg = {n["id"]: 0 for n in nodes}
    for e in edges:
        outdeg[e["from"]] += 1
        indeg[e["to"]] += 1
    for n in nodes:
        n["inDegree"] = indeg[n["id"]]
        n["outDegree"] = outdeg[n["id"]]

    families = detect_families(nodes)
    family_of = {}
    for stem, members in families.items():
        for m in members:
            family_of[m] = stem
    for n in nodes:
        n["family"] = family_of.get(n["id"])

    domains = sorted({n["domain"] for n in nodes})

    graph = {
        "generatedFrom": "Propositio/**/*.lean (static analysis) + mined lake build logs",
        "nodeCount": len(nodes),
        "edgeCount": len(edges),
        "domains": domains,
        "families": {k: v for k, v in families.items()},
        "nodes": nodes,
        "edges": edges,
    }

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(graph, f)
    print(f"wrote {args.out}: {len(nodes)} nodes, {len(edges)} edges, {len(families)} mechanical families", file=sys.stderr)

    template_path = os.path.join(ROOT, "scripts", "explorer_template.html")
    if os.path.exists(template_path):
        with open(template_path) as f:
            template = f.read()
        html = template.replace("__GRAPH_DATA__", json.dumps(graph))
        html_out = os.path.join(os.path.dirname(args.out), "index.html")
        with open(html_out, "w") as f:
            f.write(html)
        print(f"wrote {html_out} ({len(html)} bytes, data inlined)", file=sys.stderr)


if __name__ == "__main__":
    main()
