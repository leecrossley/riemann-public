# Reviews of the blueprint against the Lean (2026-11-21)

Two independent reviewer agents (claude-opus-5-5, Claude Code subagents) read the Lean source directly. Neither ran Lean. No human has reviewed this.

## Fidelity sample

24 nodes were sampled at random, 3 per chapter with seed 20261121:

- 01: fin:rh-of-everychar, fin:main, fin:rh-of-every
- 02: an:poledata-lemma, an:small-eps, an:level
- 03: host:exists-pagen, host:raw-der, host:frame
- 04: bal:ask-expansion, bal:vonmangoldt-pp, bal:thick-part
- 05: geoa:clauses, geoa:divdata, geoa:clauses-5
- 06: geob:slower, geob:covolsupply, geob:loG
- 07: sha:charparts, sha:fw, sha:split
- 08: fam:junk-ex, fam:exs, fam:shape-win

The reviewer judged 20 of 24 fully faithful in statement, proof sketch and edges. All findings below were fixed:

- geob:slower: added the edges to geoa:clauses and geoa:clauses-5 (`s_lower5` takes their clauses).
- fam:shape-win: added the omitted seventh hypothesis of `hypsE₂` (the bound at 2 and 3 for closed families at `prm1 cDep`).
- fam:junk-ex: added the missing `CuspT` fields `inj`, `depth` and `type`.
- host:raw-der: completed the field list.
- maps/06.tsv: corrected the locator of `topCovolSlim2_use_alt_alt` (it is in `ThirdPlaceSeries/`).

## Audit of the strongest negative claims

The audit included a syntactic reachability search from the five theorems of `Main.lean` over about 1.06M declarations. It is approximate: it misses instances and dot-notation. Every chain it cites was checked link by link.

| # | Claim | Verdict |
| --- | --- | --- |
| 1 | `plugWin`, `plugAll`, `everyE₂`, `shapeWin` and `shape_of` are a dead branch; the live path runs through `every_character_of_green_v_win` | true |
| 2 | `OpenLiteratureStatements` is filled entirely by in-archive theorems, and fields 1 and 3 have the same type | true |
| 3 | `RecTExists` is not local Langlands | true, but off the good classes the value is still constrained by `dim`, `langlands`, `cusp`, `nu`, `absCentral` and `type` (wording fixed in ch08) |
| 4 | `DV.Geo` is instantiated by the one-point `pointGeo` (nef, big := True) | true, and it is reached on the main chain via `ThirdIdx.nonempty_divX` (ch05 remark updated) |
| 5 | `FamP.Large` has a literal `True` conjunct | true |
| 6 | `ChebyshevInequalityAtWindowScale` has no inequality | partly true; on the main chain the tie `ChainTied` contains real inequalities (ch06 remark updated) |
| 7 | `tiedCore_of_chainTied` discards all lattice ties | partly true; it keeps three parts of `TieArith`, and `ChainTied.core_of` is dead code (ch05 updated) |
| 8 | Ferrero–Washington has a suspiciously short proof | false as phrased; the short term assembles about 62 files and 4,700 lines, not audited (ch07 updated) |
| 9 | `ZeroFreeAll` has no exception at s = 1; ζ(1) ≠ 0 comes from Mathlib's junk value | true |
| 10 | `HostConditions` is never constructed | true; its only users are dead code |
