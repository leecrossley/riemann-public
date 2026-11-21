# Roadmap: Arakelov groundwork for `latex/notes.tex`

Status: **plan only** (round 43, 2026-10-31). No Lean code is written for it yet, and no round is
dispatched until Taylor approves the **Decisions** in §7. Written by an AI agent (Claude Opus 5.5 in
Claude Code) at Taylor's request: "I think we should have a good plan for it and it should build on a
standard source", and, on the first draft (round 42, anchored on Neukirch for number fields only):
"It needs to be more general. This has to be like Faltings or what Faltings used for his proof of
Mordell or something even more modern than this."

This version replaces round 42's draft. The dimension-one targets of that draft (`X̄_K`, `Λ_K`,
`ξ_K`, `prop:content` (i),(iv)) are kept, now as the dimension-one specialisation of a general
framework.

## 1. What the notes need

- `def:arakelov-pair`: for X regular, projective and flat over Spec ℤ, the pair `X̄ = (X, X_∞)` with
  `X_∞ = (X(ℂ), F_∞, ω)`, where ω is a Kähler form with `F_∞*ω = −ω` (notes, following Flach–Morin
  2020, p. 521 and Notation 2.2, p. 522).
- `def:compactified-schemes` (a)–(h): the category `\Schbar` (morphisms of schemes with the induced
  `F_∞`-equivariant map on ℂ-points; Kähler forms not preserved), its subcategories `\Schbar^reg`,
  `\Schbar^proj`, `\Schbar_1`, the prescribed function `Z_X` and the unit `U_X`.
- `def:deninger-theory`, F1–F4: a functor on `\Schbar^proj`. F2 uses `Z_X`; F4 uses `X̄_L → X̄_K` for
  Galois extensions.
- Blocked claims: `prop:A1-number-fields`; `prop:xiK`, `prop:xiK-asymp`; `prop:content` (i),(iv);
  the `X̄_K` rows of `thm:main-general` and `thm:A-schemes`; `prop:weil-restriction`.

None of the blocked claims uses arithmetic intersection theory in its proof. The general framework
is needed so that the objects of `\Schbar^proj` are the real objects of the theory, and so that the
dimension-one case is a specialisation of it rather than a separate definition.

## 2. Sources compared

"Checked" means the pinpoint was read in the primary text during this round. Everything else is
**section-level, unverified**.

| Source | Scope | Pair (X, X_∞) and metric data | Match with `def:arakelov-pair` | Status of pinpoints |
| --- | --- | --- | --- | --- |
| S. Yu. Arakelov, "Intersection theory of divisors on an arithmetic surface", Izv. Akad. Nauk SSSR 38 (1974) 1179–1192 | Arithmetic surfaces only (regular model of a curve over a number field). Divisors with archimedean components; intersection pairing via Green's functions on the Riemann surfaces | Model plus Arakelov's canonical (admissible) metrics at each infinite place | Dimension 2 only; no general X | Bibliographic data checked (Math-Net.Ru); content unverified |
| G. Faltings, "Calculus on arithmetic surfaces", Ann. of Math. 119 (1984) 387–424; and the height machinery of "Endlichkeitssätze für abelsche Varietäten über Zahlkörpern", Invent. Math. 73 (1983) | Arithmetic surfaces: admissible hermitian line bundles, Riemann–Roch, Noether formula, Hodge index. 1983: the Faltings height of an abelian variety, as the Arakelov degree of a metrized line bundle on Spec 𝒪_K | Admissible hermitian metrics, no general Kähler form | Dimension 2 (1984); heights over Spec 𝒪_K (1983). Narrower than the notes | 1984 bibliographic data checked; the review describes the Riemann–Roch analogue; Noether formula and section numbers unverified; 1983 unverified |
| H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990) 93–174 (Numdam, read this round) | All dimensions. Arithmetic rings and varieties, Green currents, arithmetic Chow groups `ĈH^p(X)`, a ring structure on `ĈH^*(X)_ℚ`, flat pullback, proper pushforward, intersection numbers in `ĈH^1(Spec ℤ) ≅ ℝ`; Arakelov varieties `(X, ω)` and Arakelov's pairing recovered | Arithmetic variety over an arithmetic ring (A, Σ, F_∞), with `X_∞ = X_Σ(ℂ)` and the involution `F_∞`; the metric is **not** part of an arithmetic variety. An **Arakelov variety** adds a Kähler form ω with `F_∞*ω = −ω` | **Verbatim.** The notes' pair is GS §5.1.1 with A = ℤ | Checked (list in §3) |
| H. Gillet and C. Soulé, "An arithmetic Riemann–Roch theorem", Invent. Math. 110 (1992) | Arithmetic Riemann–Roch for hermitian vector bundles | Same as GS 1990 | Same | Unverified |
| J.-B. Bost, H. Gillet and C. Soulé, "Heights of projective varieties and positive Green forms", J. Amer. Math. Soc. 7 (1994) 903–1027 | Heights of subvarieties of projective space over rings of integers, via arithmetic intersection theory; positive Green forms | GS 1990 | Same convention; adds heights | Bibliographic data checked (AMS listing); content unverified |
| C. Soulé, with D. Abramovich, J.-F. Burnol and J. Kramer, *Lectures on Arakelov Geometry*, Cambridge Stud. Adv. Math. 33, CUP 1992 | Textbook exposition of GS: Ch. 1 intersection theory on regular schemes, Ch. 2 Green currents, Ch. 3 arithmetic Chow groups, Ch. 4 characteristic classes, Ch. 5 determinant of Laplace operators, Ch. 6 determinant of the cohomology; an arithmetic Riemann–Roch theorem | GS 1990 | Same convention as GS | Chapter titles checked from publisher and library listings; no result numbers checked (no copy) |
| A. Moriwaki, *Arakelov Geometry*, Transl. Math. Monographs 244, AMS 2014 | Textbook: geometry of numbers; arithmetic curves; arithmetic surfaces; general arithmetic varieties (up to the GS arithmetic Riemann–Roch formula, per a review); arithmetic volumes, Nakai–Moishezon, arithmetic Bogomolov, Lang–Bogomolov | Green functions / hermitian line bundles in the GS line | Same line as GS; strongest on line bundles and volumes | Chapter list checked from listings; section numbers unverified (no copy) |
| X. Yuan and S.-W. Zhang, "Adelic line bundles on quasi-projective varieties", arXiv:2105.13587 (v9, 2025; PUP book 2026) | Adelic line bundles on quasi-projective varieties over finitely generated fields; intersection, volume and height theory | Adelic (Zhang-style) metrics at all places; no Kähler form, no projective regular model required | More general than the notes, but a different convention: objects are not GS pairs (X, ω) | Abstract checked (arXiv); content unverified |

## 3. Recommended anchor

**Primary anchor: Gillet–Soulé 1990.** It is the source the notes' definition comes from, word for
word. It works in every dimension, it is the framework in which Faltings' and Arakelov's surface
theories and the Bost–Gillet–Soulé heights are special cases, and every pinpoint the plan uses from it
was checked:

| GS 1990 | Content (checked) |
| --- | --- |
| §1.2, Thm. 1.2.1 | existence of solutions of `dd^c γ = η` on a compact Kähler manifold, compatible with an antiholomorphic involution |
| Def. 3.1.1 | arithmetic ring (A, Σ, F_∞): excellent regular Noetherian domain, finite nonempty set Σ of embeddings into ℂ, conjugate-linear involution F_∞ |
| 3.1.2 (1) | for 𝒪_K (or K), Σ = Hom(A, ℂ) with F_∞ from complex conjugation |
| 3.1.3 | homomorphisms of arithmetic rings; 𝒪_K → 𝒪_L for E/F; ℤ is initial |
| Def. 3.2.1 | arithmetic variety: flat and of finite type over Spec A with smooth generic fibre; `X_∞ = X_Σ(ℂ)` with the involution F_∞; real (p,p)-forms and currents |
| 3.3.3 | Green current for a cycle Z: `dd^c g + δ_Z = [ω(Z, g)]` |
| Def. 3.3.4 | arithmetic Chow groups `ĈH^p(X) = Ẑ^p(X)/R̂^p(X)` |
| 3.4.3 | for X = Spec A, A Dedekind: exact sequence `A^* → (⊕_Σ ℝ)^{F_∞} → ĈH^1(A) → Cl(A) → 0` |
| Thm. 3.6.1 | flat pullback and proper pushforward |
| Thm. 4.2.3 | for X regular with quasi-projective generic fibre: pairing `ĈH^p ⊗ ĈH^q → ĈH^{p+q}_ℚ`, making `ĈH^*(X)_ℚ` a commutative associative ring |
| §4.3, 4.3.1–Thm. 4.3.2 | intersection numbers; for X projective nonsingular over ℤ, a pairing to `ĈH^1(Spec ℤ) ≅ ℝ` |
| 5.1.1 | **Arakelov variety** `X = (X, ω)`: X regular with projective generic fibre, ω a Kähler form on X_∞ with `F_∞*ω = −ω` |
| Thm. 5.1.2, 5.1.4 | the harmonic Chow groups of an Arakelov variety; Arakelov's intersection pairing recovered |

**Companion textbook: Soulé–Abramovich–Burnol–Kramer, *Lectures on Arakelov Geometry*.** Same
conventions as GS, written as a text, with the analytic prerequisites (Green currents, characteristic
classes, determinants). It needs a copy before any of its result numbers is cited (Decision D1).
Moriwaki 2014 is the alternative companion if Taylor prefers a more recent text. Yuan–Zhang is not an
anchor; it is the natural later extension if the notes move to quasi-projective objects (D6).

Faltings and Arakelov are cited where the notes discuss arithmetic surfaces and heights, as special
cases of GS, not as the foundation.

## 4. Conventions and their reconciliation

| Point | GS 1990 | Notes / Flach–Morin | Plan |
| --- | --- | --- | --- |
| Base | arithmetic ring (A, Σ, F_∞), Def. 3.1.1 | Spec ℤ | Define arithmetic rings and varieties over general A (needed for 𝒪_K and for F4), and specialise to A = ℤ (initial, 3.1.3) for `\Schbar` |
| Smoothness | generic fibre smooth (3.2.1); regular for products (4.2.3) and Arakelov varieties (5.1.1) | regular, projective, flat over ℤ | For X regular and flat over ℤ, X_ℚ is regular, hence smooth over ℚ (characteristic 0); record as a lemma, so notes' objects are GS Arakelov varieties |
| X_∞ | the complex manifold `X_Σ(ℂ)` with F_∞ | `X(ℂ)` with F_∞ and ω | Same. Over A = ℤ, Σ is the single embedding, so `X_Σ(ℂ) = X(ℂ)`. For X = Spec 𝒪_K over ℤ, `X(ℂ) = Hom(𝒪_K, ℂ)`, matching 3.1.2 (1) |
| Kähler form | data of an Arakelov variety, not of an arithmetic variety | data of the pair | Keep ω as data of the Arakelov pair. In dimension one X(ℂ) is a finite set; a (1,1)-form on a 0-dimensional manifold is 0, so ω is unique and carries no information |
| Morphisms | morphisms of arithmetic varieties (3.6) | scheme morphisms with induced F_∞-equivariant map; metrics not preserved | Same; the map on ℂ-points is induced, so it is no extra data |
| Completed zeta | not used | `Z_X = ζ(X, s) ζ(X_∞, s)` (FM p. 521); notes' `Λ_K` | Keep the notes' `Λ_K` primary, prove FM's ζ(X̄_K, s) = e^{a+bs}·Λ_K. Only the divisor enters the axioms (ruling R-1) |

## 5. What Mathlib (pinned v4.34.1) has and lacks

Checked by grep in `lean/.lake/packages/mathlib`.

**Has:**
- schemes and morphism properties: `AlgebraicGeometry.Scheme`, `Spec`, `Morphisms/Flat`,
  `FiniteType`, `Proper`, `Smooth`, `Separated`; `Properties` (regular/integral), `Noetherian`;
- cycles: `AlgebraicGeometry.AlgebraicCycle` (with pushforward `map`), `OrderOfVanishing`;
- number fields: `NumberField.InfinitePlace`, `ComplexEmbedding.conjugate`, `RingOfIntegers`,
  `ClassGroup`, `NumberField.Units.regulator`, `dedekindZeta`, `prod_abs_eq_one`;
- analysis: manifolds via `ChartedSpace`/`ModelWithCorners` (including over ℂ), smooth vector
  bundles, Riemannian metrics on bundles (`VectorBundle/Riemannian`), differential forms on normed
  spaces (`Analysis/Calculus/DifferentialForm`), distributions and test functions on open subsets of
  ℝⁿ (`Analysis/Distribution`).

**Lacks** (each is a Mathlib-scale project, not a loop round):
- the analytification `X(ℂ)` of a scheme as a complex manifold;
- differential forms of type (p,q), `∂`, `∂̄`, `dd^c` on complex manifolds; currents on manifolds;
- Kähler metrics and forms; Hodge theory (needed for GS Thm. 1.2.1);
- Chow groups (cycles modulo rational equivalence) and intersection products; K-theory with supports
  (used in GS Thm. 4.3.2);
- the completed Dedekind zeta function and Hecke's functional equation.

**External-source update (2026-11-13).** [AxiomMath/Weil](https://github.com/AxiomMath/Weil/tree/27cdb2049be62ee2911429b47f54774078450e32)
has a topology on complex points and proves the finite-field Weil conjectures;
[AxiomMath/Mordell](https://github.com/AxiomMath/Mordell/tree/82a30cb7857f6e3cfdb1be91f5533c0ccb57d493)
has Weil heights, a height machine and a Néron–Tate pairing. These are external
libraries, not declarations in this project's pinned Mathlib. Their Lean/Mathlib
pins differ from this project, and direct application has not been compiled here.
The checked local zero-dimensional evaluation topology is in
`WeilRH/ComplexPointsTopology.lean`; the source map and remaining comparison
obligations are in `scratch/2026-11-13-axiom-math/report.md`.

## 6. Targets in dependency order

Sizes: **S** ≈ one ~45-min loop round; **M** ≈ 1–2 rounds; **L** ≈ a planned sub-project; **L+** ≈
a Mathlib-scale project. "Dispatchable" means it fits a single loop round as specified.

### Tier A: general framework (statement level)

| # | Target | Source result | Mathlib | Size | Dispatchable | Unblocks |
| --- | --- | --- | --- | --- | --- | --- |
| A1 **(done, round 44; excellence not encoded)** | `ArithmeticRing` (A, Σ, F_∞); instances ℤ and 𝒪_K; homomorphisms; ℤ initial | GS Def. 3.1.1, 3.1.2 (1), 3.1.3 | `RingHom`, `ComplexEmbedding.conjugate`, `RingOfIntegers` | S | yes | everything |
| A2 **(done, rounds 44–45; `X_∞` as a set with `F_∞`, complex-manifold structure is Tier B)** | `ArithmeticVariety A`: X over Spec A, flat, finite type, smooth generic fibre; `X_∞` as the set of ℂ-points over Σ with F_∞ | GS Def. 3.2.1 | `Scheme`, `Morphisms/Flat`, `FiniteType`, `Smooth` | M | 2 rounds | A3–A5, D1 |
| A3 **(started, round 45: structure with `KahlerInterface`, proper for projective; Hodge data and the smoothness lemma remain)** | `ArakelovVariety`: A2 plus regular, projective generic fibre, and the Kähler datum, as an **interface** (a structure the analytic data must satisfy, see D2); lemma: regular flat over ℤ ⇒ smooth generic fibre | GS 5.1.1; notes `def:arakelov-pair` | A2; Kähler datum not available (§5) | M | 2 rounds | A4, D1 |
| A4 **(done, round 46: `CompactifiedScheme`, `Schbar`, `reg` without pure dimension, `proj`; `\Schbar_1` only via its connected objects)** | the category `\Schbar` and `\Schbar^reg`, `\Schbar^proj`, `\Schbar_1` | notes `def:compactified-schemes` (a)–(e); GS 3.6 for morphisms | `CategoryTheory`, A2–A3 | M | 2 rounds | F1–F4 statements; `prop:A1-number-fields` |
| A5 | cycles `Z^p(X)` and `div f`; Chow groups `CH^p(X)` | GS 3.3.1 | `AlgebraicCycle`, `OrderOfVanishing`; codimension and rational equivalence missing | L | no | Tier C |

### Tier B: analytic prerequisites (Mathlib-scale)

| # | Target | Source | Mathlib | Size |
| --- | --- | --- | --- | --- |
| B1 | analytification `X(ℂ)` as a complex manifold, with F_∞ antiholomorphic | GS 3.2.1 | manifolds exist; analytification missing | L+ |
| B2 | (p,q)-forms, `dd^c`, currents `D^{p,p}(X_ℝ)` on complex manifolds | GS §1.1, 3.2.1 | forms on normed spaces and distributions on ℝⁿ only | L+ |
| B3 | Kähler forms; `dd^c`-lemma / Hodge theory on compact Kähler manifolds | GS Thm. 1.2.1 | missing | L+ |

### Tier C: arithmetic intersection theory

| # | Target | Source | Needs | Size | Dispatchable | Unblocks |
| --- | --- | --- | --- | --- | --- | --- |
| C1 **(done, rounds 48–49: `ArithChow.ChowGroup`, `chowDegree`, `deg_principal`, `chowDegree_surjective`, `toClass`, `toClass_eq_zero_iff`, `ofGreen_eq_zero_iff`, `chowDegreeEquivRat`)** | `ĈH^1(Spec 𝒪_K)` and the exact sequence `𝒪_K^* → (⊕_Σ ℝ)^{F_∞} → ĈH^1 → Cl(𝒪_K) → 0`; the arithmetic degree `ĈH^1(Spec 𝒪_K) → ℝ` | GS 3.4.3, §4.3 (degree to `ĈH^1(Spec ℤ) ≅ ℝ`) | A1, D1; **no Tier B**: X_∞ is finite, so currents are functions | M | 2 rounds | the Arakelov class group of X̄_K; heights over Spec 𝒪_K |
| C2 | Green currents and `ĈH^p(X)` in general | GS 3.3.3, Def. 3.3.4 | A5, B1–B3 | L+ | no | general arithmetic Chow groups |
| C3 | the product on `ĈH^*(X)_ℚ` and intersection numbers | GS Thm. 4.2.3, Thm. 4.3.2 | C2, K-theory with supports | L+ | no | general intersection theory |
| C4 | heights: Faltings height over Spec 𝒪_K (degree of a hermitian line bundle); BGS heights | Faltings 1983; BGS 1994 (unverified) | C1 for the curve case; C3 in general | M (curve case) / L+ | curve case only | none in the notes' current proofs |

### Tier D: dimension one, the notes' blocked claims

| # | Target | Source | Needs | Size | Dispatchable | Unblocks |
| --- | --- | --- | --- | --- | --- | --- |
| D1 **(done, round 46: `Xbar.obj`, `pointsEquiv`, `place_eq_place_iff`, `isReal_place_iff`, `card_fiber_place`, `card_points`)** | `X̄_K = (Spec 𝒪_K, Hom(𝒪_K, ℂ), conjugation)` as an Arakelov variety over ℤ; orbits of F_∞ ↔ `InfinitePlace`; #X_∞ = [K:ℚ]; instance for ℚ | GS 3.1.2 (1), 5.1.1; notes `def:arakelov-pair` | A1–A3 | S | yes | D2–D5, C1 |
| D2 **(done on connected objects, round 47: `NumberFieldCurves.homEquiv`, `NumberFieldCat.arith_fullyFaithful`, `arithEquiv`; `\Schbar_1` disjoint unions not built)** | morphisms `X̄_L → X̄_K` and `\Schbar_1`; equivalence with number fields^op | notes `prop:A1-number-fields`, `def:compactified-schemes` (e) | D1, A4, `SliceNotFull` | M | 2 rounds | `prop:A1-number-fields`; setup for F4 |
| D3 **(done as far as Mathlib allows, rounds 49–50: `xiK*`, `SimplePoles` (Hecke's simple poles as a hypothesis), `ξ_K` entire, `ξ_K(0)ξ_K(1) ≠ 0` from the class number formula; open: nonvanishing for Re s > 1 needs the Euler product of `ζ_K`; round 61: convergence on Re s > 1, nonvanishing on the real axis, and the exact reduction to `ζ_K ≠ 0` in `DedekindZetaConv.lean`; round 62: multiplicativity of the ideal count and the Euler product over rational primes in `DedekindEuler.lean`, reducing nonvanishing to the local factors; round 63: local factors as finite products over the primes above `p`, so `ζ_K ≠ 0` on Re s > 1 and `NonvanishingRight` hold unconditionally, in `DedekindLocal.lean`; round 64: Mathlib has no Hecke continuation, recorded as a Mathlib gap; `SimplePoles` reduced to one bound at `s = 1` in `SimplePolesCrit.lean`)** | `Λ_K`, `ξ_K`; `prop:xiK` given Hecke's continuation | notes `def:zeta`, `prop:xiK`, `thm:imp-hecke`; Sutherland L19 Thm. 19.12 (checked in round 42) | `dedekindZeta`, `Dedekind.lean` | M | yes, with the Euler-product gap recorded if needed | `prop:xiK` |
| D4 **(done, round 50: `ArakelovZeta.zetaFM_eq`, `analyticOrderAt_xiFM`)** | FM's `ζ(X̄_K, s) = e^{a+bs} Λ_K`; `Z_X` for X̄_K | FM formula (1), p. 521 (checked) | D3 | S | yes | F2 for X̄_K |
| D5 **(done in degree one, round 51: `ContentXiK.content_free`, `content_iff`)** | `Σ_K = div ξ_K`; `prop:content` (i),(iv) | notes' proofs | D3, `TrivialModelGraded`, `Dedekind` | M | 2 rounds | obligation 21 |

## 6a. Minimum viable path

**A1 → A2 → A3 (interface) → A4 → D1 → D2 → C1 → D3 → D4 → D5**, about 13–15 rounds.

**Status (round 51, 2026-10-31):** all targets of the minimum viable path are done (rounds 44–51), with the
recorded gaps: excellence of A, "projective" weakened to "proper", X_∞ a set (no analytification),
`\Schbar_1` on connected objects only, and (closed in round 63) the Euler product of `ζ_K`. Next,
per decision D8: the Flach–Morin path.

This gives:
- the general objects of `\Schbar^proj` as GS Arakelov varieties over arithmetic rings, with real
  Mathlib schemes and the analytic datum as an interface;
- the category `\Schbar` and its subcategories, so F1–F4 can be stated against `Deninger.lean`;
- the dimension-one case X̄_K as a genuine instance, with its Arakelov class group and arithmetic
  degree (GS 3.4.3), which is the case Faltings' heights live in;
- every currently blocked notes claim that needs Arakelov objects.

It defers Tier B and C2–C4 in general dimension, which need Mathlib-scale analytic work and serve no
blocked claim.

## 6b. Two paths: Flach–Morin versus Gillet–Soulé

The two sources use the Arakelov compactification for different things. Read in the local Flach–Morin
PDF (`refs/citation-tree/weil-etaile/flach-morin-2020-deninger-conjectures-weil-arakelov.pdf`) this
round:
- **Γ-factors.** FM p. 521, formula (1): ζ(X̄, s) = ζ(X, s)·ζ(X_∞, s), where ζ(X_∞, s) is a product of
  Γ-factors read off from the real Hodge structure on H*(X(ℂ), ℂ) (Serre, refs [34], [35]).
- **Deligne cohomology, not Chow groups.** FM §3.1 (p. 523) defines cohomology with compact support
  through Deligne cohomology. In §3.2 (p. 523), the Kähler metric ω is used only to give a canonical
  retraction RΓ_D(X/ℝ, ℝ(n)) → τ_{<2n}RΓ_D(X/ℝ, ℝ(n)), citing FM 2018, Remark 2.13. RΓ(X̄, ℝ(n)) is
  the mapping fibre of RΓ(X, ℝ(n)) → τ_{<2n}RΓ_D.
- **Weil–Arakelov cohomology.** §3.3–3.4 (pp. 523–525) defines it, with the map ∪θ.
- **Gillet–Soulé appears only twice.** Through the Arakelov–Chow groups around Remark 3.6 (p. 525),
  and in the remark after Prop. 4.14 (p. 535). That remark expects the duality pairing to coincide
  with Arakelov's intersection pairing (GS 5.1.4). Prop. 4.14 itself uses ordinary Chow groups
  CH^n(X)_ℂ.

So FM need the analytic and Hodge-theoretic data of X(ℂ), not arithmetic intersection theory.
Deninger 2010 (`refs/deninger/deninger-2010-hilbert-polya-height-pairings.pdf`, as cited by the
notes) links the positivity of cup product and star to Beilinson–Bloch height pairings, which is the
Gillet–Soulé/Bloch side.

| Path | What it builds | Prerequisites | Notes claims that need it |
| --- | --- | --- | --- |
| **Dimension one** (common core) | A1–A4, D1–D5, C1 | none beyond Mathlib + interface | `def:arakelov-pair` and `def:compactified-schemes` for X̄_K; `prop:A1-number-fields`; `prop:xiK`, `prop:xiK-asymp`; `prop:content` (i),(iv); F4's `X̄_L → X̄_K`; the X̄_K rows of `thm:main-general` and `thm:A-schemes`; `prop:weil-restriction`. Here the Γ-factors come from r₁, r₂ directly (D4), so neither path below is needed |
| **Flach–Morin path** (started round 52: E1 interface `HodgeDatum` and E2 in degree 0, `HodgeInfty.lean`, computed for X̄_K; round 53: E2 in all degrees for ℙⁿ over 𝒪_K, `HodgeProj.lean`, with FM's completed ζ(ℙ̄ⁿ, s); round 54: E3 started, `WeilArakelov.lean` — `DeligneDatum` interface for the fibre triangle, FM (2)–(5) for ∪θ on cohomology, Dirichlet regulator of X̄_K in degree one; round 55: genuine degree-one `DeligneDatum` for X̄_K, `DeligneDegreeOne.lean` — regulator ⊗ ℝ injective with image the sum-zero hyperplane, H¹_c = 0, H²_c ≅ ℝ; round 56: §3.2 interface `CompactifiedDatum` and E4 for X̄_K, n = 1, `CompactifiedDeligne.lean` — H^i_ar(X̄_K, ℝ̃(1)) is ℝ in degrees 2, 3 and 0 elsewhere, the shape of FM Prop. 4.14 (i); round 57: H²(X̄_K, ℝ(1)) ≅ ĈH¹(X̄_K)_ℝ ≅ ℝ via the arithmetic degree, `ArakelovChowReal.lean` (real coefficients, not ĈH¹ ⊗_ℤ ℝ, which is larger); round 58: FM Prop. 4.14 (iii) for X̄_K, n = 1, `ZetaOrder.lean` — ord_{s=1} ζ(X̄_K, s) = −1 = −dim ĈH¹(X̄_K)_ℝ, and ord_{s=0} = −1, under simple poles only; round 59: X̄_K at n = 0, `CompactifiedZero.lean` — the first nontrivial (zero, non-identity) Kähler retraction, H^i_ar(X̄_K, ℝ̃(0)) ℝ in degrees 0, 1, FM Prop. 4.14 (i), (iii) at n = 0 agree; for finite X(ℂ) the twists with H^{≥2n}_D ≠ 0 are exactly n ≤ 0 and every retraction is forced; round 60: X̄_K at n < 0, `CompactifiedNeg.lean` — H^0_D has dimension r₁ + r₂ (n even) or r₂ (n odd), all H^*(X̄_K, ℝ(n)) and H^*_ar vanish, ord_{s=n} ζ(X̄_K, s) = 0, FM Prop. 4.14 (i), (iii) agree (Euler-product nonvanishing assumed except for ℚ). **The X̄_K part of the FM path is complete** (n ≤ 1; n ≥ 2 needs Borel regulators); next steps need analytic input for dim X(ℂ) > 0 (ℙⁿ), blocked on analytification) | E1: real Hodge structure on H*(X(ℂ)) with F_∞; E2: Serre's Γ-factors ζ(X_∞, s) (Serre 1970, `refs/standard-refs/serre-1970-facteurs-locaux-sdpp.pdf`); E3: Deligne cohomology RΓ_D(X/ℝ, ℝ(n)) and the Kähler retraction; E4: RΓ(X̄, ℝ(n)) and Weil–Arakelov cohomology | B1–B3, Hodge decomposition; for E4 also motivic cohomology (Bloch's cycle complex) | the prescribed function `Z_X` of `def:compactified-schemes` (g) for general X; axiom F2 in dimension > 1; `conj:arithmetic-realization` and `conj:arithmetic-realization-full` (the completed function includes Serre's archimedean factors of the generic fibre); `prop:kun-arch` (archimedean factors of tensor products) |
| **Gillet–Soulé path** | A5, C2–C4: Green currents, arithmetic Chow groups, products, heights | A5, B1–B3, K-theory with supports | the height-pairing discussions: Deninger's positivity versus the Beilinson–Bloch height pairing (`subsec:prior-den`), the Néron–Tate height around `prop:bsd-coefficient-gap` and `rem:bsd-implication-status`, and the "height pairing on one eigenspace" witnesses (`subsec:witnesses`). None of these is a theorem the notes prove from heights. They are comparisons and motivation, and the Lean versions already formalized (`bsd-*`, `R*`) are abstract |

Consequences for the plan:
- **The minimum viable path (§6a) serves both paths.** In dimension one, FM's analytic data is
  trivial and GS's ĈH^1 is the Arakelov class group.
- **The interface of A3 should be shaped for the FM path.** It should record the G_ℝ-complex manifold,
  the Kähler form and the real Hodge structure on H*(X(ℂ)). That is what Z_X and F2 need.
  Arithmetic Chow data would be layered on later only if D3 asks for it.
- **The FM path for dimension > 1 is as Mathlib-scale as the GS path.** It needs analytification and
  Hodge theory, plus Deligne and motivic cohomology for E3–E4. It is cheaper only if it stops at E2:
  Γ-factors from a Hodge structure taken as data of the interface.

## 7. Decisions for Taylor

**Decided by Taylor, 2026-10-31** (recorded in round 44):
- **D1:** anchor Gillet–Soulé 1990, companion Soulé–Abramovich–Burnol–Kramer, *Lectures on
  Arakelov Geometry*, cited at section level until a copy is in `refs/`.
- **D3 / D8:** the minimum viable path first, then the Flach–Morin path.
- **D7:** build over a general arithmetic ring `(A, Σ, F_∞)` as GS do (`WeilRH/ArithmeticRing.lean`).

Still open: D2 (analytic datum as an interface; the current plan assumes yes), D4, D5, D6, and the
`refs/` copy of GS 1990 (the round-43 Numdam download sits in the session scratchpad only).

The original decision list follows.

- **D1, anchor and copies.** Approve Gillet–Soulé 1990 as the primary anchor and SABK *Lectures on
  Arakelov Geometry* as the companion (or Moriwaki instead). GS 1990 is open on Numdam
  (`PMIHES_1990__72__93_0`); add it to `refs/` with a checksum. Provide a legitimate copy of the
  companion so its result numbers can be checked; until then only GS pinpoints are cited.
- **D2, the analytic datum.** Encode X_∞'s complex-manifold and Kähler structure as an interface
  (structure fields that a future analytification must satisfy, trivially satisfied in dimension
  one), or wait for Tier B. The interface keeps the general definition honest about what is assumed.
- **D3, depth of intersection theory.** Stop at the minimum viable path (dimension-one `ĈH^1` and
  degree), or plan Tiers B and C as a long-term sub-project, possibly aimed at Mathlib.
- **D4, Hecke.** Keep Hecke's continuation and functional equation as a hypothesis, as the notes do
  (`thm:imp-hecke`).
- **D5, normalization.** Keep the notes' `Λ_K` primary, with FM's ζ(X̄_K, s) derived (D4 target).
- **D6, Yuan–Zhang.** Out of scope now; revisit if the notes adopt quasi-projective or adelic objects.
- **D8, which path beyond dimension one.** After the minimum viable path, extend along the
  Flach–Morin path first (E1–E2: Hodge-structure data and Serre's Γ-factors, so Z_X and F2 make sense
  in every dimension), along the Gillet–Soulé path (arithmetic Chow groups and heights), or neither.
- **D7, base ring.** Define the framework over general arithmetic rings (GS 3.1.1), which 𝒪_K-relative
  statements and F4 need, and specialise to ℤ for `\Schbar`; or restrict to ℤ from the start.
