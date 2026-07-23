# Proof Explorer

A self-contained visual map of the `Propositio` library — open `index.html` in a browser, no server or build step required.

- **Domain overview** first: bubbles sized by file count, connected by cross-domain dependency weight.
- **Click a domain** to drill into its file-level dependency graph. Mechanically-generated case-split families (e.g. `ThirteenL25_0..39`) collapse into a single dashed-ring node by default — click one to expand and jump to a member.
- **Click any file** to open the drilldown panel: its module docstring (rendered), parsed declarations with axiom data where available, and its direct dependencies / dependents.
- Filter by rigor tier (axiom-clean / `native_decide` / custom axiom / has a `sorry` / not yet audited), headline-only, or free-text search.
- Gold halo = a file whose docstring is flagged headline/capstone/main-theorem, or carries an explicit `Headline: true` marker.

## Regenerating

```
python3 scripts/export_graph.py
```

Reads `Propositio/**/*.lean` (declarations, imports, module docstrings) plus, opportunistically, any `/tmp/*build*.log` left behind by a `lake build` run (mined for `... depends on axioms: [...]` lines — no live Lean invocation happens here). Writes `docs/explorer/graph.json` and the fully self-contained `docs/explorer/index.html` (data inlined, zero runtime dependencies).

## Docstring convention

The parser reads a file's module docstring (the `/-! ... -/` block) as markdown, and looks for optional structured lines to get first-class treatment instead of a heuristic guess:

```
Status: PROVED, unconditional
Source: Halbeisen & Hungerbühler (1997), Acta Arithmetica 78.3
Headline: true
```

Absent that block, the explorer falls back to heuristics (docstring mentions "capstone"/"headline"/"main theorem", `sorry`/`axiom` detection via source scan). Retrofitting the structured block onto more files over time gets them first-class treatment for free on the next `export_graph.py` run — no explorer changes needed.
