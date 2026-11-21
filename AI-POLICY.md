# AI-POLICY.md — AI-usage and software-citation contract

| Field | Value |
| --- | --- |
| Repo | `riemann` |
| Status | Draft |
| Date | `2026-09-20` |
| Approved by | `pending — approval requested` |
| Prefix | AI |
| Checked by | `latex-ai-statement` (manuscript, `[C]`); `update-ai-usage` / `update-tokens` (records, `[R]`) |
| Amended by | `new-repo-ai-policy` |
| Rule budget | 24 — wording is scarce; a new rule must displace or earn its slot |
| Transcript retention | `ai/` dated packages for durable evidence; raw Codex session transcripts remain in the user's local Codex session store and are not published |

How this repo discloses AI assistance and cites software.

**Floors.** Rules marked `[F]` may be tightened by a repo's copy, never
weakened or deleted, and bind repos whose copy predates them. An amendment
lowering one is refused, not presented.

**Markers.** `[C]` — checked in the manuscript by `latex-ai-statement`.
`[R]` — checked in the records at write time by `update-ai-usage` /
`update-tokens`. `[F]` — a template floor (see the **Floors** paragraph above). A rule may carry both `[C]` and
`[R]`: manuscript and record are different enforcement points for one
obligation, and a record writer may refuse a write that would put the record
below a rule it carries. Unmarked rules are judgment obligations, surfaced
but not gated.

**Quality floor.** `mathcity/subdomains/latex/POLICY.md` (LX-rules) and the repo's
`STYLE.md` (ST-rules). This file tightens them and never loosens them; AI2/AI3
specialize LX2 and LX6. Community anchors: the
[Leiden Declaration](https://leidendeclaration.ai/) (June 2026, IMU-endorsed),
the [AMS AI policy](https://www.ams.org/publications/journals/policies/UseofArtificialIntelligence),
and arXiv's 2026 sanction for hallucinated citations.

**Preserve-existing instantiation.** The policy and its companion live at
the root. The sole existing master records remain at `ai/ai-usage.md` and
`ai/tokens.md`, as required by the installed owner skills
`update-ai-usage` and `update-tokens`. No competing root records are created.
This draft reconciles the template's obsolete root-location wording with
those current owner paths; the single-ledger, retention, and record-content
requirements are unchanged. Approval of this path resolution is requested.

## Declared tools

Documents what tasks used, never restricts use: the task that used a tool
adds its row without approval; an unknown `.bib` key is `missing` for AI2.

| Tool | Kind | Version / model id | `.bib` key | Access date | Refs verified |
| --- | --- | --- | --- | --- | --- |
| Claude Code | AI harness (Anthropic) | 2.1.282, 2.1.314, 2.1.316; desktop app 2026-11-20 (version not recorded) | `AnthropicClaudeCode` | 2026-09-25 to 2026-11-20 | per task entry |
| Claude Opus 5.5 | LLM (Anthropic) | `claude-opus-5-5` | `AnthropicClaudeOpus` | 2026-09-25 to 2026-11-20 | per task entry |
| Claude Fable 5.1 | LLM (Anthropic) | `claude-fable-5-1` | `AnthropicClaudeFable` | 2026-09-25 to 2026-11-01 | per task entry |
| Claude Fable 5.2 | LLM (Anthropic) | `claude-fable-5-2` | missing (`AnthropicClaudeFable` names 5.1) | 2026-11-20 | per task entry |
| GPT-6 Astra | LLM (OpenAI) | `gpt-6-astra` | `OpenAIGPT6Astra` | 2026-09-11 to 2026-09-26 | per task entry |
| GPT-6 Sol | LLM (OpenAI) | `gpt-6-sol` | `OpenAIGPT6Sol` | 2026-10-15 to 2026-11-01 | per task entry |
| GPT-6.1 Sol | LLM (OpenAI) | `gpt-6.1-sol` | missing | 2026-10-14 to 2026-10-15 | per task entry |
| GPT-6 Luna | LLM (OpenAI) | `gpt-6-luna` | `OpenAIGPT6Luna` | 2026-10-14 to 2026-11-01 | per task entry |
| Codex desktop | AI harness (OpenAI) | not recorded | `OpenAICodex` | 2026-09-19 to 2026-11-01 | per task entry |
| Lean 4 | theorem prover | v4.34.1 (`lean/lean-toolchain`) | `Moura2021lean` | 2026-09 to 2026-11 | n/a |
| Mathlib | Lean library | v4.34.1, `d13f23b723b8a846827a245b89c10fc7d3f11612` | `Mathlib2026library` | 2026-09 to 2026-11 | n/a |
| Lean 4 (pinned by the Alpöge archive `refs/alpoge-lean`) | theorem prover | v4.33.1 (`refs/alpoge-lean/lean-toolchain`); read as text, not run here | `Moura2021lean` | 2026-11-20 | n/a |
| Mathlib (pinned by the Alpöge archive `refs/alpoge-lean`) | Lean library | `0df444a360eaa60ab8c11dca51a86af692955474` (`refs/alpoge-lean/lake-manifest.json`); not built here | `Mathlib2026library` (names the repo's own pin) | 2026-11-20 | n/a |
| SageMath | CAS | 10.8 | `Sage2026sagemath` | 2026-10-14 | n/a |
| LMFDB | database | not recorded | missing | 2026-09-25 to 2026-09-26 | n/a |
| latexmk | build tool | 4.86a | missing | 2026-09 to 2026-11 | n/a |
| Claude Sonnet 5.5 | LLM (Anthropic) | `claude-sonnet-5-5` | missing | 2026-11-20 | per task entry |
| Claude Code CLI | AI harness (Anthropic) | 2.1.326, 2.1.329 | `AnthropicClaudeCode` | 2026-11-20 | per task entry |
| ripgrep | search tool | 15.1.0 | missing | 2026-11-20 | n/a |
| pdftotext (Poppler) | PDF text extraction | not recorded | missing | 2026-11-20 | n/a |
| Python | language runtime | 3.13.7 | missing | 2026-11-20 | n/a |
| Semantic Scholar MCP | literature search service | not recorded | missing | 2026-11-20 | n/a |
| curl | HTTP client | 8.7.1 (installed version on 2026-11-20; version at run time not recorded) | missing | 2026-11-20 | n/a |
| WebSearch | web search tool (Claude Code built-in) | not recorded | missing | 2026-11-20 | per task entry |
| WebFetch | web page fetch tool (Claude Code built-in) | not recorded | missing | 2026-11-20 | per task entry |
| TikZ/PGF | LaTeX graphics package | 3.1.10 (TeX Live 2025) | missing | 2026-11-20 | n/a |
| pgfplots | LaTeX plotting package | 1.18.1 (TeX Live 2025) | missing | 2026-11-20 | n/a |
| tikz-cd | LaTeX commutative-diagram package | 1.0 (2021/05/04, TeX Live 2025) | missing | 2026-11-20 | n/a |
| plasTeX | LaTeX-to-HTML converter | 3.1 (leanblueprint pipx venv) | missing | 2026-11-21 | n/a |
| leanblueprint | plasTeX plugin for Lean blueprints | 0.0.20 | missing | 2026-11-21 | n/a |
| plastexdepgraph | plasTeX dependency-graph plugin | 0.0.5 | missing | 2026-11-21 | n/a |
| plastexshowmore | plasTeX plugin | 0.0.2 | missing | 2026-11-21 | n/a |
| XeTeX | TeX engine | 3.141592653-2.6-0.999997 (TeX Live 2025/Homebrew) | missing | 2026-11-21 | n/a |
| dvisvgm | DVI-to-SVG converter (plasTeX imager) | 3.4.3 | missing | 2026-11-21 | n/a |
| pdftoppm (Poppler) | PDF-to-raster converter | 26.04.0 (installed version on 2026-11-21) | missing | 2026-11-21 | n/a |
| NumPy | Python numerical library | 2.3.2 (installed in the Python 3.13.7 on PATH on 2026-11-21) | missing | 2026-11-21 | n/a |
| preview (LaTeX package) | LaTeX float-extraction package | 14.0.6 (2024/06/30, TeX Live 2025) | missing | 2026-11-21 | n/a |

## Rules

**AI1 — AI is never mentioned without its model and harness [C][R].**
The model identifier actually used (`claude-opus-5`, not "an LLM"), the harness
(Claude Code, Codex CLI, web chat, API), the date, and reasoning-effort or
temperature when the harness exposes them.
Pass: every AI mention carries model + harness + date. Fail: a bare "AI",
"an LLM", or an unversioned product name.

**AI2 — Every software system used substantively is cited [C].**
CAS, languages, libraries, databases, build tools, AI products and providers
all get a BibTeX entry and a pinpoint `\cite` (LX2). AI providers are cited as
software, exactly as Magma or SageMath are. Where the source is unpaginated —
a provider page, a model card, a CAS home page — the locator is AI3's
hyperlink form. Give the version actually used and a stable public URL.
Pass: every declared-tools row has a key, an entry, and a pinpoint citation;
no dead entries (LX6). Fail: a tool used and not cited, or a bare `\cite{key}`.

**AI3 — Skills and workflow software are cited to their source, with a link [C].**
The repository or README is the cited object and the locator is a hyperlink:
`\cite[\href{https://github.com/<org>/<repo>/blob/<ref>/README.md}{README}]{Author1938}`,
pinned to a tag or commit that contains the version used. A local checkout or
private mirror does not establish public availability.
Pass: a keyed entry and a hyperlinked locator resolving to a public URL.
Fail: a skill named in prose only, or a locator pointing at a local path.

**AI4 — AI-results are declared as such [C][R].**
An **AI-result** is anything from an AI session that, had a fellow
mathematician supplied it, would have required acknowledgement: a statement,
counterexample, proof strategy, reference, reformulation, computation, **or
drafted mathematical prose**. Each is identified with the model, harness, and
named skill that produced it (`frontier-dump`, `fable-prompt`).
Pass: each AI-result is attributed to a concrete tool chain.
Fail: an AI-derived contribution with no provenance, or provenance given only
as "AI assistance was used".

**AI5 — Every AI-result gets a literature search, and the search is reported [C][R][F].**
Agent output is frequently already known, and Leiden makes proactive
attribution an obligation, not a courtesy. For each AI-result: search; report
each **hit** — a pinpoint reference (LX2) the result is equivalent to, follows
from, or could reasonably have been derived from — and state the relation;
**compare and contrast the methods**, not merely priority; say plainly when
the technique was clearly available even if no one reference states the
result; and report the AI-result **even when the search returns nothing**,
saying the search was run and came back empty. Attribution that cannot be
resolved is stated as unresolved, not omitted.
Pass: every AI-result has hits with locators and a method comparison, or an
explicit no-hits statement. Fail: no search, or a hit with no comparison.

**AI6 — Agents are cited as software, never as mathematical warrant [C][F].**
The distinction is **origin versus warrant**. Naming a model as the *origin*
of an AI-result is required (AI4), and the AI2 provider citation belongs in
that same provenance or methods sentence. Offering a model as the *warrant*
for a mathematical claim is forbidden: a model is never an author, never a
corresponding author, and never the authority a statement rests on. Do not
write "the model proved"; do not present a transcript as an argument.
Pass: no AI system in the author block, and every model `\cite` sits in a
sentence asserting provenance or method rather than mathematics.
Fail: an AI system in the author block; a model `\cite` in a sentence making a
mathematical assertion; or a claim whose stated support is a model.

**AI7 — The starting material is disclosed [C].**
What was available to the agents before the searches — definitions,
conjectures, drafts, prior notes, computations — and for each, whether it was
human-generated or AI-generated.
Pass: inputs named with their human/AI provenance.
Fail: results reported with no account of what they were built on.

**AI8 — No blind credit [C][R].**
Never "the model found it". State what was asked, what the search or
derivation did, and what the human did to turn it into the claim as stated.
Pass: each AI-result has a derivation account. Fail: bare attribution.

**AI9 — Responsibility stays with the human authors [C][F].**
Responsibility for the correctness and adequacy of every argument, result, and
citation remains exclusively with the human authors, whatever produced the
draft, and the disclosure says so. Every coauthor is told of the AI use and
assents to the disclosure before submission.
Pass: an explicit human-responsibility statement is present.
Fail: language that shares or defers responsibility to a tool.

**AI10 — The expert-talk gate [R].**
Nothing ships that the authors could not present in an expert talk and defend
under questioning without further AI assistance. Agent review is never
disclosed as human verification.
Pass: every shipped claim is independently understood by a human author.
Fail: a result retained because the model was convincing.

**AI11 — AI-surfaced references are verified before use [C][R][F].**
Every reference an AI proposed is checked against the actual source — it
exists, the numbering matches, it says what it is claimed to say — before it
enters the bibliography. Fabricated citations are sanctionable under arXiv's
2026 policy.
Pass: every AI-surfaced entry in the `.bib` is marked verified in the records.
Fail: an unverified AI-proposed reference in the `.bib`. (A reference surfaced,
checked, and correctly discarded is not a finding.)

**AI12 — Placement is fixed [C].**
The unnumbered **Software and AI assistance** subsection goes at the end of
the introduction; in a document with no introduction, immediately after the
opening overview; in a document with neither, as the first unnumbered
subsection before the first numbered section; failing all three, immediately
after the front matter. A document that has an abstract
also carries one factual disclosure sentence in it; a document with no
abstract owes no abstract sentence. Acknowledgements stay separate — no
invented grants, hospitality, or thanks. A journal or user placement
requirement overrides this rule when recorded with the manuscript.
Pass: the subsection is present, unnumbered, correctly headed, at the first
of those four positions the document admits; and the abstract carries the
disclosure sentence whenever the document has an abstract.
Fail: subsection absent, misheaded, numbered, placed later than the position
the document admits, or an abstract without the sentence.

**AI13 — Computations are recomputed, not quoted [C][R].**
Numeric, algebraic, and combinatorial claims originating in an AI session are
re-derived in a real system (Magma, SageMath, Macaulay2, Python) and reported
as that system's output, cited per AI2. "The model asserted" and "the system
computed" are different claims and are worded differently.
Pass: each computational claim traces to a rerunnable computation.
Fail: a model transcript standing in for a system run.

**AI14 — AI sessions owe a record even when they produced only a refutation [C][R].**
ST11/LX11/LX12 already require negative results to be stated and carried
forward; this rule adds what they do not cover — a session whose only output
was a refutation, counterexample, or ill-posed proposal still gets an
`ai-usage.md` entry and an AI5 search. Discharge is by the floor's own test:
exhibit each finding as a numbered statement with both locators, **before**
the positive results, naming the expectation it corrects ("it is natural to
expect $X$; in fact $Y$"). A keyword scan does not discharge it. ST11 and LX12 grant a
scope-reason escape to *derived* artifacts; the canonical document is not one,
so the escape does not apply here.
Pass: every negative finding in the records is exhibited in the document with
its locators, in that order and framing; counts reported.
Fail: a refuted claim deleted together with its refutation, a finding recorded
but not exhibited, or a refutation-only session with no `ai-usage.md` entry.

**AI15 — One master `ai-usage.md` and one `tokens.md` per repository [R][F].**
At `ai/ai-usage.md` and `ai/tokens.md`, covering the whole repo. Subdirectory artifacts
keep working records; those are sources consolidated upward, never competing
ledgers. `update-ai-usage` is the sole write path for `ai-usage.md`,
`update-tokens` for `tokens.md`. Session transcripts and raw telemetry behind an
entry are retained for the life of the submission as the primary evidence
beneath the AI4/AI5/AI8 accounts. The repo declares the default location in
this file's header; an entry names its own only when it differs.
Pass: exactly one master of each at the declared `ai/` paths; the header's retention location
resolves, and any entry-level override resolves too.
Fail: a competing master record, an unconsolidated orphan, or an account with no
surviving evidence.

**AI16 — Token usage is priced and dated [R][F].**
Per task: token counts, the model spent on, the rates applied, the cost, the
task date, and the rate's own as-of date. Exact telemetry where available.
Where attribution is impossible, say so and record the raw observations and
why they cannot be separated. A labelled estimate of a **magnitude** is
permitted; a fabricated **attribution** across inseparable aggregates is not.
Totals mark which rows are measured and which estimated.
Pass: every row carries tokens, model, rates, cost, date, rate-as-of, and a
source label. Fail: an unlabelled estimate, an invented figure, or a total
mixing measured and estimated rows silently.

**AI17 — Confidential material stays out of third-party models [R].**
Unpublished third-party work — referee reports, submissions under review,
private communications — is not sent to a third-party model without the
owner's permission. Where a workflow step is skipped for this reason, record
what was withheld.
Pass: no confidential third-party content in any recorded session.
Fail: a referee report or submission under review sent to a model.

**AI18 — No residual AI artifacts in the manuscript [C].**
No leftover prompts, model chatter, hedging boilerplate, placeholder
citations, or chat scaffolding. Readers are never directed to local paths,
scratch files, private chats, `ai-usage.md`, or `tokens.md`; the manuscript
states the substance itself. A supplement may be cited only if it will
accompany the paper or has a verified, stable public location.
Pass: the document reads as a self-contained mathematical text.
Fail: prompt residue, or a reader pointed at a file they will not receive.

**AI19 — Submission gate [C].**
A manuscript is not submitted, posted, or promoted to a higher tier until
`latex-ai-statement` has run against **that exact revision** — identified by
commit hash or version string — and returned no FAIL, with every DEFER either
resolved or accepted in writing by a named human. The audit report is
retained with the submission — `latex-ai-statement` writes it under `ai/`,
which travels with the repository. An `ADVISORY` verdict
from a `Status: Draft` policy does **not** clear this gate; adopt the policy
or record the named human's acceptance.
Pass: a retained audit names the submitted revision and carries no FAIL and no
unaccepted DEFER.
Fail: no audit, an audit of a different revision, an unresolved FAIL, or an
unaccepted DEFER.

**AI20 — Records are self-describing [R][F].**
A record says which task it belongs to and what kind of file it is.
*Identity:* every record carries the task identifier
`<ISO-8601-datetime-with-offset>__<skill>__<slug>` — the offset so agents in
different zones cannot mint colliding keys, the double underscore because `-`
occurs inside all three fields. It is minted once, by `update-ai-usage`, and
joins `ai-usage.md` to `tokens.md`; a caller pricing a task with no provenance
entry mints a provisional identifier and marks the row as lacking provenance.
*Type:* a roll-up index over records (the established name is `usage.md`)
declares itself on its first line and is never consolidated — consolidating one
counts every record it indexes a second time. An unlabelled file carrying an
index signal is reported as ambiguous and left unconsolidated, never guessed
at: guessing "record" double-counts silently while every row still reads as
correct, whereas guessing "index" under-counts and surfaces later.
Pass: every record names a well-formed identifier; every index declares itself;
ambiguous files are reported, not consumed.
Fail: a missing, malformed, or never-reconciled provisional identifier; an
undeclared index consolidated as a record; or an ambiguity resolved by guess.

## Change Log

| Date | Change | Approved by |
| --- | --- | --- |
| 2026-09-20 | Draft instantiation; preserve existing research and declare the proposed survey. | Pending; not adopted |
| 2026-11-20 | Declared-tools preamble reworded as documentation, not a gate; 14 rows backfilled from `ai/ai-usage.md` and `latex/notes.bib`. | Taylor, in chat, 2026-11-20 ("The declared tools is anything. It is to document not to restrict."); rows added by an agent under that instruction, not separately reviewed |
| 2026-11-20 | Rows added for curl, WebSearch and WebFetch, used by the Stepanov–Bombieri frontier dumps (`ai/2026-11-20-stepanov-bombieri-rh/`, `ai/2026-11-20-stepanov-bombieri-varieties/`). | Taylor, in chat, 2026-11-20 ("Yes, add them"); rows added by an agent, not separately reviewed |
| 2026-11-20 | Rows added for TikZ/PGF, pgfplots and tikz-cd, used for the figures of `latex/stepanov-bombieri/stepanov-bombieri.tex`. | Taylor, in chat, 2026-11-20 ("Yes, add them"); rows added by an agent, not separately reviewed |
| 2026-11-20 | Rows added for the Lean 4 and Mathlib versions pinned by the Alpöge archive (`refs/alpoge-lean`), cited by `latex/alpoge/alpoge.tex` but not run, for task `2026-11-20T16:03-05:00__harvest-dumps__alpoge-manuscript`. | Under the declared-tools preamble (documentation, no approval needed); rows added by an agent at the coordinator's request, not separately reviewed |
| 2026-11-21 | Rows added for plasTeX, leanblueprint, plastexdepgraph, plastexshowmore, XeTeX and dvisvgm, used to build `blueprints/alpoge/` for task `2026-11-21T05:55-05:00__create-blueprint__alpoge-blueprint`. | Under the declared-tools preamble and the repository owner's standing approval (2026-11-19); rows added by an agent, not separately reviewed |
| 2026-11-21 | Rows added for pdftoppm (Poppler), NumPy and the LaTeX preview package, used by the figure center-of-mass measurement for task `2026-11-21T14:58:58-05:00__session__riemann-book-figure-audit`. | Under the declared-tools preamble and the repository owner's standing approval (2026-11-19); rows added by an agent, not separately reviewed |
