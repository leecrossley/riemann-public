# Blueprint of the Alpöge Lean archive

A leanblueprint describing in mathematical language the Lean 4 archive that Levent Alpöge published on alpo.ge on 2026-11-20. The local copy is `refs/alpoge-lean` (gitignored), at archive commit `155fd7918` on Lean `v4.33.1` and Mathlib `0df444a3`. The archive has no comments and no manuscript, so this blueprint was written backwards: from the Lean to the prose.

## What is canonical

The blueprint is hand-written (create-blueprint "Working mode"), and no file in it is generated.

- `src/content.tex` and `src/chapters/*.tex` hold the nodes.
- `src/macros/paper.tex` holds the shared theorem environments and notation.
- `src/macros/web.tex` and `src/macros/print.tex` hold renderer-specific macros.
- `src/web.tex`, `src/print.tex` and `src/plastex.cfg` are the leanblueprint preambles and configuration.
- `maps/NN.tsv` has one row per node of chapter NN: the Lean names, the declaration locators (`path:line` under `src/` of the archive), the edges seen in the Lean body (`edges_formal`), the edges inferred from the mathematics only (`edges_described`), and how deeply the agent read the declaration.
- `maps/NN.md` holds the chapter agent's notes: disagreements with the 2026-11-20 survey, misleading names, hollow definitions and unexpanded nodes.
- `scripts/check_blueprint.py` holds the static checks and the cross-chapter edge resolution.

A cross-chapter dependency is written in a chapter as a `% uses-lean: Full.Lean.Name` comment. `scripts/check_blueprint.py --resolve` turns it into a `\uses{label} % resolved` line for whichever node carries that `\lean` name. Rerun it after editing.

## What `\leanok` means here

Nothing. No node carries `\leanok` or `\mathlibok`, because the archive was never compiled and `#print axioms` was never run for this blueprint. A `\lean{...}` link records only that a declaration with that fully qualified name exists in the source (checked by `check_blueprint.py` against the declaration line and its enclosing namespaces) and that the node transcribes it. Whether the prose matches the Lean is the reading agents' claim, and no human has reviewed it. Fidelity evidence is the per-node `read_depth` column of `maps/` and the notes.

## Rebuild

```bash
cd blueprints/alpoge && python3 scripts/check_blueprint.py --resolve
```

```bash
cd blueprints/alpoge/src && plastex -c plastex.cfg web.tex
```

```bash
cd blueprints/alpoge/src && latexmk
```

The web build writes `blueprints/alpoge/web/` (with the dependency graph at `dep_graph_document.html`). The print build (xelatex) writes `src/print.pdf`. Both are untracked.

## Contents and findings

The blueprint has 377 nodes across 8 chapters plus an introduction. 308 nodes carry `\lean` links, naming 801 declarations. 800 of those are declarations of the archive. The other is Mathlib's `RiemannHypothesis`, which the archive does not declare. There are 824 dependency edges. `maps/external-refs.tsv` lists the 233 declarations mentioned as dependencies that have no node of their own. Duplicate nodes from different chapters were merged, and `maps/dedupe-redirects.tsv` records each merge.

The chapters were reverse-engineered by agents and then checked by two independent review agents (`maps/reviews.md`). Points a reader should know first:

- The final theorems go through `every_character_of_green_v_win`. The `plugAll`/`everyE₂` branch is dead code.
- `OpenLiteratureStatements` is filled entirely by theorems proved inside the archive. There is no `sorry` or `axiom` in the source, but nothing has been compiled.
- `RecTExists` is much weaker than local Langlands. `llOf_alt` and `recTExists_of_published_inputs` are identity functions.
- The Arakelov interface `DV.Geo` is instantiated on the main chain by a one-point model whose `nef` and `big` are `True`.
- `FamP.Large` contains a literal `True`. `tiedCore_of_chainTied` drops every lattice tie before the analytic chain.

## Provenance

Written on 2026-11-21 by AI agents (Claude Code, claude-opus-5-5: one coordinator, eight chapter agents and two review agents) for Taylor Dupuy. The record is in `ai/ai-usage.md` and `ai/tokens.md`, and the working folder is `scratch/2026-11-21-alpoge-blueprint/`.
