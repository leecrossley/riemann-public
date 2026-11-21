# Notes on the Riemann Hypothesis

AI-generated notes, printed by Taylor Dupuy. They are temporary and are meant
to help readers digest Levent Alpöge's Lean proof of the Riemann Hypothesis.

## PDFs

- [Notes on Alpöge's Proof of the Riemann Hypothesis](https://tdupu.github.io/riemann-public/riemann-book.pdf)
- [The Approach to the Riemann Hypothesis via Hilbert–Pólya Operators and Deninger Cohomology Theories](https://tdupu.github.io/riemann-public/hilbert-polya-deninger.pdf)

Independent verification of Alpöge's Lean proof:
[Drew Sutherland's verification page](https://math.mit.edu/~drew/grh/).

## Contents

| Path | What it is |
| --- | --- |
| `riemann-book.pdf` | The book on Alpöge's proof, built from `latex/riemann-book.tex` |
| `hilbert-polya-deninger.pdf` | The Hilbert–Pólya and Deninger notes, built from `latex/notes.tex` |
| `latex/` | LaTeX sources, bibliographies, and the figure and data files the two builds read |
| `lean/` | Lean 4 + Mathlib project formalizing claims of `latex/notes.tex` (not Alpöge's proof) |
| `blueprint/` | Hand-written leanblueprint describing Alpöge's Lean archive in mathematical language |
| `ai/` | The AI provenance record (`ai-usage.md`) and token/cost record (`tokens.md`) |
| `AI-POLICY.md` | The AI-use policy the records follow |

This repository is a published copy. It is regenerated from a private
working repository, so references inside the sources to `ai/<date>-…/`
packages, `scratch/` or `refs/` point to files that are not included here.

## Building

```bash
cd latex && latexmk -pdf -outdir=build riemann-book.tex
cd latex && latexmk -pdf -outdir=build notes.tex
cd lean && lake exe cache get && lake build
```
