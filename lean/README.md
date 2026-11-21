# `lean/` — Lean 4 formalization of the Weil-cohomology ⇒ RH claims

Formalizes the claims of `ai/2026-09-25-weil-rh-notes/plan.md` (C-PUR, C-WEIL, C-RH, C-GRH
scaffold, C-CONV, R2/R3/R12). The mathematical source is
`ai/2026-09-19-arithmetic-weil-cohomology/report.md` (§§3–5, §7.1). Round 3 adds the class-level
and calibration claims of the two 2026-09-25 research dumps:
`ai/2026-09-25-zeta-class-axioms/report.md` (Q1: Lemma 4.2, Theorem A, Prop. 5.1/Cor. 5.2) and
`ai/2026-09-25-finite-field-calibration/report.md` (Q2: Theorem 1′, Remark 4.4, Prop. 6.2,
Thm 6.5(4)). Round 4 adds Theorem 6 of `ai/2026-09-25-arithmetic-kunneth-conjecture/report.md`
(Hodge index on the arithmetic surface ⟺ AW4-E, claim C-K6) with the tensor-positivity core of its
Prop. 5. Round 5 adds, from the manuscript `latex/notes.tex` directly (labels cited), the
multiplicative algebra form AW4-E_F (`def:aw4-EF`, `prop:aw4-EF`, `prop:rosati-EF`), the phantom
Frobenius eigenvalues (`prop:ff-phantom`), the finite-dimensional core of `thm:ff-lefschetz`, and the
thick-subcategory induction behind the étale Eilenberg–Moore statements (`prop:EM`,
`prop:EM-criterion`). Round 6 adds, again from `latex/notes.tex`, the support of the duality
pairing on generalized eigenspaces (`prop:B-support`) and the generalized-eigenspace decomposition
of a tensor product of spectral cores (`prop:tensor-eigen`, first display; `def:spectral-core`).
Round 7 completes `prop:tensor-eigen` (directness of the block sum, stability and finiteness of the
blocks, and the multiplicity formula) and adds the Jordan block with pure eigenvalues and no
positive Frobenius polarization (`prop:N-jordan`, with `def:frob-pol`). Round 8 derives the
`prop:B-support` weight identity from the derivation rule of AW1 and the trace equivariance of AW3,
and adds the converse of the Weil–Serre lemma (`prop:weil-converse` (i)–(ii)). Round 9 completes
`prop:weil-converse` (ii) as stated (the polarizations are exactly the orthogonal sums `⊕_α h_α` of
arbitrary positive definite forms on the eigenspaces) and adds `prop:N-lines` for `X = E × ℙ¹`:
the product formula (i) from point counts, the identification of `ζ_X` with an explicit rational
function, its zeros on the two lines `Re s = 1/2, 3/2` (ii) and its poles on `Re s ∈ {0, 1, 2}` (iii).
Round 10 packages `def:spectral-core` (b) as a structure `SpectralCore`, restates `prop:tensor-eigen`
for spectral cores with the dimension formula as a `finrank` identity when only finitely many pairs
contribute, and proves the second clause of `prop:N-jordan` by the manuscript's route through
`prop:weil-converse` (i).
Round 11 maps `prop:polarization-identity` to the existing derivation law and formalizes the formal curve (`def:formal-curve`, `prop:formal-curve` (i)–(iv)): an explicit
graded algebra on which `F` is an automorphism with an alternating perfect pairing of weight `q = 3`,
`N_n = 0` and `Z = P₁/((1-t)(1-qt))`, whose `H¹` eigenvalues are impure, whose Frobenius-compatible
Hermitian forms are exactly the indefinite ones `[[0, c], [c̄, 0]]`, and whose algebraic classes
carry a nondegenerate weight-one pairing with `F` semisimple of eigenvalues `1, q`.
Round 12 builds the logarithmic suspension of `def:log-susp` as an object, the algebraic direct sum
`V̂ = ⨁_{q^ρ ∈ spec F} V_{(q^ρ)}` with `Θ = ρ + (log q)⁻¹ log(α⁻¹F)` on each summand, and proves
`prop:suspension` (i) (zeros of `1 - α q^{-s}`, simplicity, multiplicities), (ii) (`(V̂, Θ)` is a
spectral core with `V̂_{Θ∼ρ} = V̂_ρ`), (iii) (a Frobenius polarization suspends to an infinitesimal
one) and (iv) (purity and diagonalizability of `Θ`); the suspension of `id_ℂ` shows `SpectralCore`
is not vacuous.
Round 13 proves `prop:susp-converse`: the restricted form (`def:log-susp` (b)) of a positive
infinitesimal polarization on the suspension, for any choice `ρ_α ∈ Σ_q(α)`, is a positive Frobenius
polarization (`SuspConverse`).
Round 14 completes `prop:suspension` (i): `det(1 − F q^{-s}) = ∏_α (1 − α q^{-s})^{dim V_{(α)}}`, and
the analytic zero order of `s ↦ det(1 − F q^{-s})` at every `ρ ∈ ℂ` is the algebraic multiplicity
of `ρ` as an eigenvalue of `Θ` (`Suspension`). It also restates `prop:aw4-EF` (ii) (`Θ ι_σ = ι_σ θ_σ`
for the sheet map `ι_σ : V → V̂`) and `prop:ff-phantom` (ii) (the spectrum of `Θ` for
`(ℂ^{S_N}, diag(S_N))` is `C_{N log q}`) on the suspension itself (`SuspObject`).
Round 15 states `prop:aw4-EF` (iii) about `V̂` itself: under AW4-E_F every vector of `V̂` lies in a
finite-dimensional `Θ`-stable subspace `V̂' = ⨁_m V̂_{σ_m}` on which `Θ|V̂'` satisfies the additive
algebra form AW4-E of weight `j` (`AW4EFDatum.exists_aw4EAdd_suspension`, `SuspObject`).
Round 16 adds the sheet spaces of `def:aw4-EF` (c) and the remark after (d): `ι_σ` is an isomorphism
of `V` onto `V̂_σ = ⨁_α V̂_{σ(α)}` (`Suspension.sheetEquiv`, `range_sheetMap`), and for `q > 1`,
`V̂ = ⨁_{m ∈ ℤ} V̂_{σ + 2πim/log q}` as an internal direct sum (`Suspension.isInternal_sheetSpace`,
`SuspObject`).
Round 17 proves `prop:weighted-algebra-obstruction`: for a graded algebra of spectral cores in degrees
`0, …, 2d` with a derivation, a trace of weight `d + w` and positive star forms, `w ≠ 0` forces every
`V^j = 0`, and a unit forces `w = 0` (`WeightedAlgebraDatum.eq_bot`, `eq_zero_of_unit`,
`WeightedAlgebra`).
Round 18 adds three linear-algebra obstructions (`LinearGaps`): Serre's `prop:R5` (no unital ring
antihomomorphism `ℍ → M₂(ℝ)`, `LinearGaps.isEmpty_antihom`), and the BSD gaps
`prop:bsd-positive-gap` (`bsd_positive_gap`) and `prop:bsd-jordan-gap`
(`rootMultiplicity_charpoly_jordan`, `finrank_ker_jordan_sub_one`).
Round 19 adds `prop:R2-star` (iii) (no antilinear `J'` commuting with `Θ` makes `B(v, J'w)`
positive definite, `R2.not_exists_posStar`, `Negative`) and, in `ElementaryGaps`, the remaining
elementary gaps `prop:bsd-coefficient-gap` (`bsd_coefficient_gap`, `lattice_gap`),
`prop:bsd-primary-gap` (`primaryComponent_finite`, `G_infinite`), `prop:R11` (i)–(ii)
(`R11.eval_quartetC_eq_zero_iff`, `R11.im_neg_logDeriv_pos`) and `prop:R14` (i)–(ii)
(`R14.compact_and_eigenvalue`, `R14.shift`).
Round 20 adds `prop:R14` (iii)–(iv) for the correlation `c_f` of `def:R14-sources`
(`R14.corr`, `corr_eq_zero`, `corr_pos`, `corr_log_eq_zero`, `exists_corr_log_pos`,
`ElementaryGaps`) and a nonzero unital `WeightedAlgebraDatum` with `w = 0`
(`WeightedAlgebraDatum.trivialModel`, via `Spectral.spectralCore_of_finiteDimensional`), so the
hypotheses of `prop:weighted-algebra-obstruction` are not vacuous.
Round 21 rechecks the weighted rows against the manuscript's type-`(d, 0)` repair of `def:aw`
(fidelity note "Weighted rows after the type-`(d, 0)` repair"), adds the stated form
`WeightedStarDatum.polarization_identity` of `prop:polarization-identity`, proves `prop:kun-Fq-C`
(`KunFq.maxGenEigenspace_eq_bot_or_infinite`, new module `KunFq`) and `prop:R11` (iii)
(`R11.im_neg_logDeriv_value`, `R11.norm_hb_lt`).
Round 22 proves `prop:kun-orbits` (i)–(ii) and the counting core of (iii) on the periodic unit
`𝟙_p`, taken as the suspension of `(ℂ, 1)` (new module `KunOrbits`), and encodes `def:aw4-forms`
(a)–(b) at weight `j` for one degree, with `prop:aw4-forms` (i) (new module `AW4Forms`).
Round 23 proves `prop:aw4-forms` (ii) on spectral cores (`AW4Forms`: AW4-V ⇒ AW4-E, with
`End_ℂ(V')` as matrices in an `h`-orthonormal basis) and `prop:kun-torus` (i)–(iii) (new module
`KunTorus`).
Round 24 proves `prop:one-branch` without its determinant clause (new module `OneBranch`) and
`prop:aw5-contains` (i)–(ii) (new module `AW5Contains`: AW5 on `V^j` ⇒ AW4-V, purity and
orthogonality).
Round 25 completes `prop:kun-orbits` (iii) with the Kurokawa cone of `def:kurokawa-cone`
(`KunOrbits`) and proves `prop:aw4-forms` (iii) degree by degree (new module `AW4Star`: stars
`*'_j` from polarizations, with the given polarization as star form).
Round 26 starts `prop:hilbert` (new module `Hilbert`): the completion `𝓗` of `(V, h)`, a Hilbert
basis of `𝓗` consisting of eigenvectors in `V`, and the symmetric operator `T` with `Θ = j/2 + iT`
on `V`. Self-adjointness of `T` on `𝓗` and its spectrum remain open (obligation 18).
Round 27 adds `prop:R2-frob` (`R2.frob_counterexample`: `F = q^Θ` preserves `Ω` up to `q`, commutes
with `J`, and has eigenvalue moduli `q^{1/2±a}`), `prop:R17` (`R17.integral_reflect_mul_deriv_eq_zero`,
`R17.bump_spec`), `prop:kun-cone` (ii) for any spectral core (`KunOrbits.kurokawaCone_inf_antidiag`)
and `prop:R7` (i) for each local core, (iii) and (iv) (new module `LocalCores`).
Round 28 builds `V_𝒬 = ⨁_{p ∈ 𝒬} V_p` of `def:R7-local` (`R7.VQ`, `R7.thetaQ`) and completes
`prop:R7` (i)–(iii) for it: `spec Θ_𝒬 = ⋃_p (2πi / log p) ℤ` (`R7.mem_spec_thetaQ`), the
eigenvalue `0` has multiplicity `#𝒬` as a cardinal (`R7.rank_maxGenEigenspace_zero`), nonzero
eigenvalues are simple (`R7.mult_eq_one`), and for infinite `𝒬` it is not a spectral core
(`R7.not_spectralCore`). The trivial model of `def:trivial-model` was designed but not built
(obligation 20).
Round 29 builds the degree-one slice of the trivial model (`def:trivial-model`) as
`TrivialModel.model : WeightedStarDatum 1 0 1 V^1 V^1 ℂ` (new module `TrivialModel`) and proves
`prop:trivial-model` (i)–(iii) on it: the derivation rule in bidegree `(1, 1)`, the AW3 trace and
nondegeneracy of `B`, `Sp_1 = Σ` with multiplicities and the spectral-core condition; positivity of
`h_1` and `*_1² = -1` on the line; and the existence criterion (`TrivialModel.exists_datum_iff`).
Round 30 adds `prop:content` (ii) and the blocks of (iii) (new module `Content`): the trivial model
carries a positive definite Hermitian form on `V^1` with orthonormal basis vectors, which is not
`h_1` off the line and satisfies `(eq:inf-pol)` only if `Σ` lies on the line
(`Content.exists_stdForm`); the real-pair block `Content.pairDatum` is a Weil datum of type
`(1, 0)` with Hermitian, nondegenerate star form of signature `(1, 1)` satisfying `(eq:inf-pol)`;
and a degree-one datum with an eigenvalue off the line has no positive star form
(`Content.not_isPositive_of_re_ne`).
Round 31 assembles `prop:content` (iii) (new module `ContentAssembly`): one generic degree-one
datum `PairingModel.datum` covers all three kinds of block (eigenvalues `λ_x`, a pairing involution
`σ` of `B` with signs, and an involution `τ` with coefficients for the star), and
`ContentAssembly.content_indef` takes the direct sum of the line block, one real-pair plane per
unit and one `def:R2-block` quartet per unit: a Weil datum of type `(1, 0)` with `Sp_1 = Σ` with
multiplicities, `h_1` Hermitian, nondegenerate and satisfying `(eq:inf-pol)`, and indefinite as soon
as there is a real pair or a quartet. `ContentAssembly.R2_Ω`, `R2_S` and `R2_Θ` identify the quartet
block with `R2.Ω`, `R2.S` and `R2.Θ`.
Round 32 completes the trivial model in degrees `0` and `2` (new module `TrivialModelFull`): the
slices `TrivialModel.model0 : WeightedStarDatum 1 0 0 ℂ ℂ ℂ` and `model2 : WeightedStarDatum 1 0 2`
(`Θ_0 = 0`, `Θ_2 = 1`, `*_0(c) = c̄η`, `*_2(cη) = c̄`, unit products) with positive `h_0`, `h_2`; the
whole graded algebra `Tot = ℂ·1 ⊕ V^1 ⊕ ℂη` with associative (`mul_assoc'`), graded-commutative
(`mul_comm_graded`, `mul_anticomm_one`, `B_antisymm`) unital product and `Θ` a derivation of it
(`thetaTot_mul`); and AW3's blockwise perfectness, `V^1_{1-σ} → (V^1_σ)^*` bijective for finite
multiplicities (`blockPairing_bijective`) and `V^0_σ × V^2_{1-σ}` perfect
(`blockPairing_zero_bijective`).
**Nothing here proves RH.** `ArithmeticWeilCohomologyQ ⇒ RiemannHypothesis` is a conditional
theorem; `nonempty_arithmeticWeilCohomologyQ_iff` shows that the data encoded in the structure
is *equivalent* to RH, as the report warns in §5. The same holds for the multiplicity-faithful
structure `ArithmeticWeilCohomologyQMult` (`nonempty_arithmeticWeilCohomologyQMult_iff`): encoding
AW2's zero orders makes the structure more faithful, but its existence is still *equivalent* to RH.
The mathematical content of a Weil-cohomology proof of RH therefore lies entirely in constructing
such a structure from independent arithmetic data, which nothing here attempts.
Round 33 adds the self-adjoint operator of `prop:hilbert` (new module `HilbertSelfAdjoint`): the
diagonal operator `Hilbert.Diag.op b τ = diag(τ_k)` of `def:diag-op` on its maximal domain
`{x | (τ_k ⟪b_k, x⟫)_k ∈ ℓ²}` as a `LinearPMap` on a Hilbert space with Hilbert basis `b`, proved
symmetric with dense domain and self-adjoint (`Diag.isSelfAdjoint`, `T^† = T`), and
`Hilbert.exists_selfAdjoint`: for a polarized spectral core the eigenvector Hilbert basis of `𝓗`
makes `diag(τ_k)` self-adjoint and extends `-i(Θ - j/2)` on `V`. It also extends the
`prop:content` (iii) datum to degrees `0` and `2` (new module `ContentGraded`): the product
`u ∪ v = B(u, v)η` on `ℂ·1 ⊕ V^1 ⊕ ℂη` for any `PairingModel.Data` with alternating signs is
associative, graded-commutative and unital with `Θ` a derivation, and
`ContentAssembly.content_indef_graded` states this for the assembled datum together with the
positive degree-0/2 slices `model0`, `model2`.
Round 34 is a consistency audit prompted by the positive-weight obstruction of
`ai/2026-10-17-deninger-weighted-axiom-repair/report.md` (R1–R4): it adds nonzero positive models
of `WeightedStarDatum` for **every** type `(d, w)` and degree `j`
(`WeightedStarDatum.weightedLineModel`, `exists_positive_nontrivial`) and a `SurfaceDatum` line
model (`SurfaceDatum.lineModel`), and records which structures have instances in the section
below.
Round 35 closes that audit and obligations 20–21's packaging gap: `AW4EFDatum.scalarModel` is a
concrete AW4-E_F datum (`F = α·1` on `ℂ^n`, `|α|² = q^j`, `A = M_n(ℂ)` with trace and conjugate
transpose; `exists_nontrivial`), and the new module `TrivialModelGraded` packages the trivial model
in all three degrees as the single graded structure `WeightedAlgebraDatum (Tot ι) 1 0`
(`TrivialModel.gradedModel`, for finite `ι` on the line), with AW1's `V^0 ≅ 𝟙` as a unital,
multiplicative, flow-compatible isomorphism (`deg0Equiv`, `deg0Equiv_unit`) and `V^2 ≅ 𝟙(-1)`
(`deg2Equiv`, `deg2Equiv_twist`).
Round 36 removes the finiteness assumption and adds the indefinite packaging. A linear isomorphism
intertwining two operators now transports the spectral-core condition
(`Spectral.SpectralCore.of_equiv`), so the degree-one summand of the graded trivial model is a
spectral core whenever `(V^1, Θ_1)` is (`TrivialModel.spectralCore_G1`), and
`TrivialModel.gradedModelInf` is the graded trivial model for any divisor with finite
multiplicities and no finite accumulation point (`gradedModel` is now its finite case via
`gradedModelOf`). The new module `HermAlgebra` states `HermAlgebraDatum`, the graded package with
nondegenerate Hermitian (not positive) star forms, and shows that the assembled datum of
`prop:content` (iii) is an instance (`ContentAssembly.gradedDatum`, nonzero and with
`h_1`-values `2` and `-2` by `gradedDatum_indef`). It also formalizes the repaired remark after
`prop:weighted-algebra-obstruction`: only the trace weight minus the star shift enters the form
identity (`form_identity_sub`), a derivation kills the unit (`derivation_unit_eq_zero`), and with a
unit the two weights must agree (`trace_weight_eq_shift_of_unit`). Docstrings and this README now
state ruling R-1 on identity (1) of the Sept-19 record: only the divisor of `D₁` is encoded, and the
exact regularized value is `2^{-1/2} ξ/2π²`.
Round 37 proves the spectral-core condition for arbitrary block data
(`PairingModel.spectralCore_theta`: finite multiplicities and no finite accumulation point), so the
indefinite graded datum of `prop:content` (iii) now exists for any such divisor
(`ContentAssembly.gradedDatumInf`, `gradedDatumInf_indef`). It also completes `prop:hilbert`: the
self-adjoint `T = diag(τ_k)` has pure point spectrum `{τ_k}` with finite multiplicities and no finite
accumulation (`Hilbert.exists_spectral`), stated through eigenvectors and the resolvent because
Mathlib has no spectrum for unbounded operators (`Diag.op_eq_smul_iff`,
`Diag.mem_span_of_op_eq_smul`, `Diag.existsUnique_sub_smul_eq`, `Diag.spectral_clause`).
Round 38 formalizes `def:unit` and the remaining clauses of `prop:unit` in `Unit.lean`. The
arithmetic unit `𝟙 = (ℂ, 0)` (`Unit.arith`) is a spectral core with spectrum `{0}`, simple, and a
unit for the tensor of spectral cores: `TensorProduct.rid` gives `V ⊗ 𝟙 ≅ V` and
`V ⊗ 𝟙(-k) ≅ V(-k)` intertwining the generators (`tensorSum_arith`, `tensorSum_twist`), so `V ⊗ 𝟙`
is a spectral core iff `V` is. The `q`-periodic unit `𝟙_q` (`Unit.Periodic`, `periodicTheta`) is
built as the Laurent polynomials, so `vⁿvᵐ = v^{n+m}` is the algebra product and `Θ` is a derivation
of it (`periodicTheta_mul`); it is a spectral core with spectrum `(2πi/log q)ℤ`, every eigenvalue
simple, and no linear isomorphism intertwines it with `𝟙` (`not_equiv_arith`).
Round 39 closes the reachable items of round 38's inventory. `prop:algebra-form` (ii) over
`k = ℂ` (Kleiman's Corollary 1″) is `PositiveTrace.rep_isSemisimple`, `rep_norm_eq_rpow` and
`rep_iSup_eigenspace` in `AlgebraForm.lean`: for any unital algebra map `ι : A → End V`, `ι(g)` is
diagonalizable with eigenvalues of modulus `q^{j/2}`. `prop:R10` (new module `R10`) shows that an
abstract unitary between Hilbert spaces with `ℕ`-indexed bases carries no spectral information:
`diag(λ_n)` is self-adjoint with pure point spectrum and `dim ker(A - x) = #{n | λ_n = x}`
(`R10.diag_spectral`), and an intertwining bounded bijection forces equal counts
(`R10.not_exists_intertwiner`). `prop:bsd-spectral-rank` (new module `BsdRank`) is the conditional
rank-BSD argument (`BsdRank.bsd_spectral_rank`), and the algebraic part of `prop:bsd-picard-gap` is
`BsdRank.splitEquiv` and `BsdRank.picard_gap`.

Round 40 follows the Deninger unification of the notes. Every label cited from `lean/` still exists
uncommented in `notes.tex` (no stale citations). `prop:relative-structure` (new module
`RelativeStructure`) adds `DeningerStructure.Morphism`, a morphism between Deninger structures of
possibly different dimensions as in `def:deninger-structure` (b), and proves that `a • v = φ(a) ∪ v`
makes `V` a graded `A`-algebra on which `Θ` is a derivation (`Morphism.Θ_act`).
`prop:slice-not-full` (new module `SliceNotFull`) is proved in Mathlib's scheme category: over-
endomorphisms of `Spec 𝒪_K` are trivial, its scheme automorphisms are exactly the `Spec σ`,
`σ ∈ Aut(K)`, and the forgetful functor is not full when `Aut(K) ≠ 1`.

Round 41 starts the groundwork rounds. `prop:algebra-form` (i) over `k ∈ {ℚ, ℝ}` gets its
separability half (new module `AlgebraFormOrdered`): over any linearly ordered field, a positive trace
involution (`PositiveTraceOrd`, `def:pos-involution` for `k ≠ ℂ`) makes `S(a, b) = τ(a b†) + τ(b a†)`
an anisotropic form scaled by `L_g`, so `L_g` is semisimple (`isSemisimple_of_similitude`, valid over any
field) and the minimal polynomial of `g` over `k` is separable (`PositiveTraceOrd.minpoly_separable`).
No base change to `ℂ` is used. The modulus half of (i) and all of (ii) for `k ∈ {ℚ, ℝ}` stay open
(obligation 22).

Round 42 is a planning round for the Arakelov groundwork, and adds no Lean code. The plan is
[`ROADMAP-arakelov.md`](ROADMAP-arakelov.md). It is anchored on Neukirch, *Algebraic Number
Theory*, Ch. III and VII. Its result numbers were checked only through secondary sources, and
Sutherland's MIT 18.785 notes and Flach–Morin 2020 are used for checked pinpoints. Its targets
T1–T5 cover the arithmetic curve `X̄_K`:
- the pair with conjugation on `K →+* ℂ`;
- the category `\Schbar_1` (`prop:A1-number-fields`);
- `Λ_K`, `ξ_K` and `prop:xiK`, taking the Hecke continuation as a hypothesis;
- Flach–Morin's ζ(X̄_K, s) as a constant multiple of `Λ_K`;
- `prop:content` (i) and (iv).

The design choices it needs approved are listed under "Decisions for Taylor".

Round 43 replaces that plan. The roadmap is now anchored on Gillet–Soulé, "Arithmetic intersection
theory" (1990), which works in all dimensions; its §5.1.1 is the notes' `def:arakelov-pair` verbatim.
The companion textbook is Soulé et al., *Lectures on Arakelov Geometry*. The roadmap separates a
Flach–Morin path (Hodge data, Γ-factors, Deligne cohomology) from a Gillet–Soulé path (arithmetic Chow
groups, heights), with the dimension-one targets common to both. Still plan only.

Round 44 starts the approved Arakelov groundwork (Taylor, 2026-10-31: anchor Gillet–Soulé 1990 with
Soulé et al. as companion; minimum viable path, then the Flach–Morin path; general arithmetic rings).
Roadmap target A1 is done: `ArithmeticRing` is GS Definition 3.1.1, `ArithmeticRing.Hom` is 3.1.3,
and the instances are ℤ (`int`, which is initial: `int_hom`, `int_hom_unique`) and `𝓞 K` with
`S = Hom(𝓞 K, ℂ)` and the Frobenius `F_∞` of Example 3.1.2 (1) (`ringOfIntegers`,
`mem_embeddings`, `card_ringOfIntegers_S`). A2 is started: `ArithmeticVariety` is GS 3.2.1 (flat,
finite type, smooth generic fibre) with `Spec A` as instance; `X_∞` is next. Excellence of `A` is not
encoded (Mathlib has no excellent rings; see the fidelity note).

Round 45 finishes A2 and starts A3 (GS 1990 3.2.1 and 5.1.1, checked in the local copy
`refs/arakelov/gillet-soule-1990-arithmetic-intersection-theory.pdf`). The involution of an arithmetic
ring is forced: `ArithmeticRing.F_apply` proves `F_∞(x)_τ = conj (x_{τ̄})` and `conj_mem` that `S` is
closed under conjugation. `ArithmeticVariety.complexPoints` is `X_∞ = X_S(ℂ)` as a set (the ℂ-points
over each `σ ∈ S`) with the involution `Finf` (`Finf_Finf`); for `Spec 𝓞 K` it is `Hom(K, ℂ)` with
complex conjugation (`complexPointsSpecEquiv`, `complexPointsSpecEquiv_Finf`). `ArakelovVariety` is
GS 5.1.1 with the Kähler datum as an interface (`KahlerInterface`, roadmap D2) and "projective" weakened
to "proper"; `ArakelovVariety.ofRing` gives `Spec A`, so `Spec 𝓞 K` (`ringOfIntegers K`) and `Spec ℤ`
(`int`) are Arakelov varieties.

Round 46 does A4 and D1 (`WeilRH/CompactifiedScheme.lean`; notes `def:compactified-schemes`, which follows
Flach–Morin Notation 2.2 and pp. 520–521). `CompactifiedScheme` is (a): `X` separated of finite type over
`Spec ℤ`, `X_∞ = X(ℂ) = Hom(Spec ℂ, X)` with `F_∞` (`points`, `Finf`), and a Kähler datum (`KahlerDatum`,
through the D2 interface) on every object of Arakelov type (`IsArakelovType`: proper, flat, regular over
`ℤ`). `Schbar` is the category (b), as an `InducedCategory` over `Scheme`, so morphisms are morphisms of
schemes, the induced map on `X_∞` is `F_∞`-equivariant (`Schbar.infty_Finf`), Kähler forms are not
preserved, and the forgetful functor to schemes is fully faithful (`Schbar.forgetFullyFaithful`).
`Schbar.reg` and `Schbar.proj` are (c), (d); varieties over finite fields have `X(ℂ) = ∅`
(`isEmpty_points_of_finite`). For D1, `Xbar.obj K` is `X̄_K`, of Arakelov type and in `\Schbar^proj`;
`Xbar.pointsEquiv K : X_∞ ≃ Hom(K, ℂ)` carries `F_∞` to conjugation, the `F_∞`-orbits are exactly the
fibres of `Xbar.place : X_∞ → InfinitePlace K` (`place_surjective`, `place_eq_place_iff`), real places are
the fixed points (`isReal_place_iff`), each orbit has `mult w` points (`card_fiber_place`), and
`#X_∞ = [K : ℚ] = r₁ + 2r₂` (`card_points`).

Round 47 does D2 (`WeilRH/NumberFieldCurves.lean`; notes `prop:A1-number-fields` and the remark after it).
Every ring map `𝓞_K → 𝓞_L` is injective (`ringHom_injective`), restriction gives
`(K →+* L) ≃ (𝓞_K →+* 𝓞_L)` (`ringHomEquiv`), and with `Spec` fully faithful (`specHomEquiv`) the morphisms
`X̄_L → X̄_K` in `\Schbar` are exactly the field embeddings `K → L` (`homEquiv`; `endEquiv` for `End(X̄_K)`).
`NumberFieldCat` is the category `𝒩` of number fields; `NumberFieldCat.arith : 𝒩ᵒᵖ ⥤ \Schbar`,
`K ↦ X̄_K`, `α ↦ Spec(α|_{𝓞_K})`, is fully faithful (`arith_fullyFaithful`), and `arithEquiv` is the
equivalence of `𝒩ᵒᵖ` with its essential image: `prop:A1-number-fields` on connected objects.

Round 48 does C1 (`WeilRH/ArithmeticChow.lean`; Gillet–Soulé 1990 §3.4.3, p. 131). Arithmetic divisors on
`Spec 𝓞_K` are pairs `(Z, g)` of an invertible fractional ideal and an `F_∞`-invariant real vector on
`X_∞ = Hom(K, ℂ)` (`greenSpace`); `principal` is `div̂ f = (div f, (-log ‖σ f‖²)_σ)`, `ChowGroup` is
`ĈH¹(Spec 𝓞_K)`, and `degree`/`chowDegree` is GS's `deĝ (Z, g) = log #(Z) + ½ Σ_σ g_σ`. It vanishes on
principal divisors by the product formula (`deg_principal`, from `prod_norm_embeddings`:
`Π_σ ‖σ x‖ = |N_{K/ℚ} x|`), and `chowDegree_surjective` shows `deĝ` is onto `ℝ` for every `K`
(`deg_const`: `deĝ (0, c) = ½ c [K : ℚ]`).

Round 49 finishes C1 and starts D3. In `ArithmeticChow.lean`, GS 3.4.3's exact sequence
`𝓞_K^* → (⊕_σ ℝ)^{F_∞} → ĈH¹(Spec 𝓞_K) → Cl(𝓞_K) → 0` is formalized: `toClass` (`(Z, g) ↦ [Z]`) is
surjective (`toClass_surjective`); its kernel is the image of `ofGreen` (`g ↦ [(0, g)]`,
`toClass_eq_zero_iff`); and `[(0, g)] = 0` iff `g` is the Green vector of a unit of `𝓞_K`
(`ofGreen_eq_zero_iff`, `toPrincipalIdeal_eq_one_iff`). For `K = ℚ`, `deĝ` is injective
(`chowDegree_injective_rat`, using `Cl(ℤ) = 1` from Mathlib's `Rat.classNumber_eq`), giving
`chowDegreeEquivRat : ĈH¹(Spec ℤ) ≃+ ℝ` (GS 3.4.3). The new `XiK.lean` defines
`ξ_K = s (s − 1) Λ_K` from a `DedekindContinuation` (Hecke's theorem as a hypothesis, roadmap D4) and
proves `ξ_K(1 − s) = ξ_K(s)` (`xiK_one_sub`), independence of the continuation (`xiK_eqOn`),
`ξ_ℚ = 2ξ` (`xiK_rat`) and, for `ℚ`, that the zeros of `ξ_ℚ` off `{0, 1}` are the nontrivial zeros
of `ζ` (`xiK_eq_zero_iff_rat`): part of `prop:xiK`.

Round 50 finishes D3 as far as Mathlib allows and does D4. `XiK.lean` adds the hypothesis
`DedekindContinuation.SimplePoles C` (Hecke: the poles of `Λ_K` at `0, 1` are simple, i.e.
`s (s − 1) Λ_K(s)` extends to an entire `P.ξ`), satisfiable for `ℚ` (`SimplePoles.ofRat`). From it:
`ξ_K(1 − s) = ξ_K(s)` everywhere (`SimplePoles.one_sub`); `ξ_K(1) = |d_K|^{1/2} Γ_ℝ(1)^{r₁} Γ_ℂ(1)^{r₂}
Res_{s=1} ζ_K` by Mathlib's class number formula (`SimplePoles.xi_one`), hence `ξ_K(0) ξ_K(1) ≠ 0`
(`xi_one_ne_zero`, `xi_zero_ne_zero`) — only simplicity is assumed, the nonvanishing is proved; and the
zeros of `ξ_K` are the nontrivial zeros of `dedekindDatum` (`xi_eq_zero_iff`). The new
`ArakelovZeta.lean` (D4) defines Flach–Morin's `ζ(X̄_K, s) = ζ_K(s) Γ_ℝ(s)^{r₁+r₂} Γ_ℝ(s+1)^{r₂}` with
FM's `Γ_ℝ = 2^{-1/2} π^{-s/2} Γ(s/2)`, `Γ_ℂ = (2π)^{-s} Γ(s)` (FM p. 521 (1), checked), and proves
`ζ(X̄_K, s) = e^{a + b s} Λ_K(s)` for `Re s > 1` with `a = −(r₁/2 + r₂) log 2`, `b = −(log |d_K|)/2`
(`zetaFM_eq`; `e^{a+bs} = 2^{-1/2}` for `ℚ`, `exp_fmA_add_rat`, matching ruling R-1), and that
`e^{a+bs} ξ_K` and `ξ_K` have the same order at every point (`analyticOrderAt_xiFM`): same divisor.

Round 51 does D5 (`ContentXiK.lean`): `Σ_K = div ξ_K` and `prop:content` (i), (iv) in degree one, given
Hecke's continuation and simple poles. A generic part handles any entire `f` with `f(1 − s) = f(s)`,
`f ≢ 0`: `ord_{1−σ} f = ord_σ f` (`SymEntire.mult_one_sub`), `ord_{1/2} f` is even
(`SymEntire.even_mult_half`, the notes' "`t ↦ ξ_K(1/2 + t)` is even"), and a designated family of zeros
(`Re > 1/2`, or `Re = 1/2, Im > 0`, plus `ord_{1/2}/2` copies of `1/2`) whose trivial-model spectrum lists
`div f` with multiplicity (`SymEntire.card_fiber`) and is a spectral core (`SymEntire.spectralCore`: finite
multiplicities; no finite accumulation point by Mathlib's `preimage_zero_mem_codiscrete`). For `ξ_K`:
`content_free` ((i): the trivial model is a degree-one Weil datum, a spectral core, with
`Sp_1 = div ξ_K`) and `content_iff` ((iv): a positive degree-one datum with `Sp_1 = div ξ_K` exists iff
every zero of `ξ_K` has real part `1/2`, i.e. GRH for `ζ_K`).

Round 52 starts the Flach–Morin path (roadmap decision D8; step E1 with the degree-0 part of E2) in
`HodgeInfty.lean`. `HodgeDatum` is an interface for the real Hodge structure at infinity (FM pp. 520–521,
checked): finite-dimensional pieces `H^{p,q}`, zero above degree `top`, with `F_∞ : H^{p,q} ≃ H^{q,p}` an
involution. From it come FM's Hodge numbers `h^{p,q}`, `h^{p,±} = dim (H^{p,p})^{F_∞ = ±(−1)^p}` with
`h^{p,q} = h^{q,p}` (`h_symm`) and `h^{p,+} + h^{p,−} = h^{p,p}` (`hplus_add_hminus`, via
`involution_finrank_add`), FM's `L_∞(h^i, s)` (formula (1), `LInfty`) and `ζ(X_∞, s) = ∏ L_∞^{(−1)^i}`
(`zetaInfty`). For `X̄_K`, `Xbar.hodge K` has `H^{0,0} = ℂ^{Hom(K,ℂ)}` with `F_∞ f = f ∘ conj` and all other
pieces zero; its Hodge numbers are computed, not assumed: `h^{0,+} = r₁ + r₂` (`finrank_invariants`:
invariant functions are those factoring through the infinite places) and `h^{0,−} = r₂`
(`finrank_antiinvariants`). Hence `zetaInfty_hodge`: `ζ(X_∞, s)` from the Hodge datum equals round 50's
`zetaInftyFM`, which removes round 50's "Hodge numbers used as exponents" simplification.
`pointsPullback_Finf` matches `F_∞` on `ℂ^{X_∞}` (scheme points, round 46) with `f ↦ f ∘ conj`.

Round 54 starts FM path step E3 in `WeilArakelov.lean` (FM §3.1–3.4, pp. 523–524): `DeligneDatum` is
an interface for the long exact sequence of FM's fibre triangle `RΓ_c → RΓ → RΓ_D →` (regulator as data;
nonzero instance `DeligneDatum.idDatum`); `WeilArakelov.Har H i = H i × H (i−1)` and `theta` are FM (2)
and `∪θ` on cohomology, with `theta_comp` (`∪θ∘∪θ = 0`), `ker_theta_succ` (acyclicity, FM (3)),
`kerThetaEquiv` (FM (4): `ker ∪θ ≅ H^{i−1}`) and `cokerThetaEquiv` (FM (5): `coker ∪θ ≅ H^{i+1}`).

Round 55 builds the first genuine (non-degenerate) `DeligneDatum`, for `X̄_K` in degree one (`n = 1`),
in `DeligneDegreeOne.lean` (FM §3.1, p. 523): `H¹ = Λ_K ⊗ ℝ` (`unitsR`, `Λ_K` the unit lattice),
`H¹_D = ℝ^{InfinitePlace K}`, the regulator `⊗ ℝ` (`regR`, which is round 54's `regulatorMap` on
`1 ⊗ unitClass u`, `regR_tmul`), `H²_c = ℝ` with connecting map `∑_w`. From Dirichlet's unit theorem
(`logR_eq_equiv`: a `ℤ`-basis of the full-rank unit lattice is an `ℝ`-basis of the log space),
`regR_injective` and `range_regR` (image = sum-zero hyperplane) give `H¹_c = 0` and `H²_c ≅ ℝ`; the
datum `degreeOne K` has all three exactness conditions proved, and `degreeOne_conn_ne_zero`.
`regulatorMap K` is the Dirichlet regulator `𝒪_K^× → ℝ^{InfinitePlace K}` (degree one, `n = 1`), with image
in the sum-zero hyperplane (`sum_regulatorMap`) and kernel `μ(K)` (`regulatorMap_eq_zero_iff`).

Round 56 encodes FM §3.2 (p. 523) in `CompactifiedDeligne.lean`: `CompactifiedDatum` extends `DeligneDatum`
by the truncation `TDel = H^*(τ_{<2n} RΓ_D)`, the adjunction and the Kähler retraction (`ret ∘ adj = id`,
`adj` bijective below `2n`, `TDel = 0` from `2n` on) and the long exact sequence of
`RΓ(X̄, ℝ(n)) → RΓ(X, ℝ(n)) → τ_{<2n} RΓ_D →`. For `X̄_K`, `n = 1`, `compactOne K` is built from
`degreeOne K`: `H^i_D = 0` for `i ≥ 2`, so nothing is truncated and `H^i(X̄_K, ℝ(1)) = H^i_c`
(`compactOne_Hbar_one`: `H¹ = 0`; `compactOne_Hbar_two`: `H² ≅ ℝ`). Step E4: `harBar i = H^i(X̄_K) ⊕
H^{i−1}(X̄_K)` (FM (2)) is zero outside degrees `2, 3` and one-dimensional in both (`prop414_shape`), the shape
predicted by FM Prop. 4.14 (i) with `2n = 2`, and `1 = −ord_{s=1} ζ̂_K` (pole order not stated in Lean). The
non-compactified `harOpen` is `(r₁ + r₂ − 1)`-dimensional in degrees `1, 2` instead (`finrank_harOpen_one`,
`finrank_harOpen_two`).

Round 58 closes FM Prop. 4.14 (iii) for `X̄_K` at `n = 1` as an order equation in `ZetaOrder.lean`
(FM p. 534: `ord_{s=n} ζ(X̄, s) = -dim CH^n(X̄)`). With `ζ(X̄_K, s)` round 50's `zetaFMCont` and only Hecke's
simple poles assumed (`SimplePoles`), `meromorphicOrderAt_zetaFMCont_one` proves `ord_{s=1} ζ(X̄_K, s) = -1`
and `meromorphicOrderAt_zetaFMCont_zero` proves `ord_{s=0} = -1` (Mathlib's `meromorphicOrderAt`, from
`ξ_K(1), ξ_K(0) ≠ 0`). `fm414_iii` combines this with round 57's `chowDegreeREquiv` and round 56's
`finrank_hBar_two`: `ord_{s=1} ζ(X̄_K, s) = -dim_ℝ ĈH¹(X̄_K)_ℝ = -dim_ℝ H²(X̄_K, ℝ(1))`. FM's Conjecture 4.1 is
not used; in this model the statement is a theorem.

Round 59 gives the first `CompactifiedDatum` whose Kähler retraction is **not** the identity, in
`CompactifiedZero.lean`: `X̄_K` at twist `n = 0` (FM §3.1–3.2, p. 523). For `X(ℂ)` finite, `H^*_D(ℝ(n))`
sits in degree `1 < 2n` for `n ≥ 1` (nothing truncated) but in degree `0 ≥ 2n` for `n ≤ 0`, so `n ≤ 0` are
exactly the twists with `H^{≥2n}_D ≠ 0`. `zeroDatum K`: `H^0(X_K, ℝ(0)) = ℝ`, `H^0_D = ℝ^{InfinitePlace K}`,
regulator the diagonal, `H^1_c = ℝ^{places}/ℝ` of dimension `r₁ + r₂ − 1` (`finrank_Hc_one`).
`compactZero K`: `τ_{<0} RΓ_D = 0`, retraction `0`, `compactZero_adj_not_surjective`. Then
`H^i(X̄_K, ℝ(0)) = H^i(X_K, ℝ(0))` and `harZero` is `ℝ` in degrees `0, 1` and zero elsewhere
(`prop414_zero_shape`); `fm414_zero`: `ord_{s=0} ζ(X̄_K, s) = −1 = −dim H^0_ar(X̄_K, ℝ̃(0))`, AGREEING with FM
Prop. 4.14 (i), (iii) at `n = 0` (and with `CH^0(X̄_K) = ℤ`, not formalized). The retraction is still forced
(truncation of a complex in one degree); a metric-dependent retraction needs `dim X(ℂ) > 0` (e.g. `ℙⁿ`),
i.e. analytic input Mathlib lacks.

Round 60 completes the `X̄_K` part of the FM path with the negative twists `n < 0`, in `CompactifiedNeg.lean`
(FM §3.1, p. 523: "for `n < 0`, `RΓ(X, R(n)) = 0` and `R(n)_D = (2iπ)^n R`"). `H^0_D(X_K/ℝ, ℝ(n))` is the
`G_ℝ`-invariants of `((2πi)^n ℝ)^{X(ℂ)}`; conjugation acts on `(2πi)^n ℝ` by `(−1)^n`, so a real place
contributes only for `n` even: `finrank_twistInv` gives `r₁ + r₂` (`n` even) and `r₂` (`n` odd). With
`RΓ(X_K, ℝ(n)) = 0`, `H^1_c ≅ H^0_D` (`negDatum`, `finrank_negDatum_Hc_one`). Since `2n < 0`, `τ_{<2n}` kills
everything (`compactNeg`, retraction `0`; `compactNeg_adj_not_surjective` for even `n`), so every
`H^i(X̄_K, ℝ(n))` and every `H^i_ar(X̄_K, ℝ̃(n))` vanishes (`harNeg_subsingleton`, `finrank_harNeg`).
`meromorphicOrderAt_zetaFMCont_neg`: `ord_{s=n} ζ(X̄_K, s) = 0`, from `ξ_K(n) = ξ_K(1 − n)` and
`ξ_K ≠ 0` on `Re s > 1`; the latter (`NonvanishingRight`) is a hypothesis for general `K` (no Euler product of
`dedekindZeta` in Mathlib) and a theorem for `ℚ` (`nonvanishingRight_rat`). `fm414_neg` / `fm414_neg_rat`:
FM Prop. 4.14 (i), (iii) at every `n < 0` AGREE (`0 = −dim CH^n = −dim H^{2n}_ar`). The parity-dependent
dimension lives in the non-compact `H^1_c(X_K, ℝ(n))`, matching the trivial zeros of the uncompleted `ζ_K` at
`s = n` (classical; that order equation is not formalized). **Status:** with rounds 54–60 the `X̄_K` part of
FM §3 and Prop. 4.14 is complete (`n ≥ 2` needs Borel's higher regulators, outside the model); the next steps
of the FM path need analytic input for `dim X(ℂ) > 0`.

Round 61 is groundwork for the missing Euler product of `ζ_K`, in `DedekindZetaConv.lean`. Mathlib v4.34.1
defines `dedekindZeta K` as the `L`-series of `a_K(n) = #{I : N I = n}` and proves the class number formula, but
states no convergence on `Re s > 1` and no Euler product (its `EulerProduct` machinery is indexed by rational
primes and needs a multiplicative coefficient function; `a_K` is not shown multiplicative). Proved here: the
partial sums of `a_K` are `O(n)` (`sum_coeff_isBigO`, from Mathlib's ideal-counting asymptotics), so the
`L`-series converges absolutely on `Re s > 1` (`LSeriesSummable_coeff`, `abscissaOfAbsConv_coeff_le`);
`ζ_K(x) > 0` for real `x > 1` (`dedekindZeta_pos`); `dedekindGammaFactor_ne_zero` on `Re s > 0`; hence
`ξ_K(x) ≠ 0` for real `x > 1` unconditionally (`xi_ne_zero_of_real`), and `NonvanishingRight` reduces exactly
to `ζ_K(s) ≠ 0` on `Re s > 1` (`nonvanishingRight_of_dedekindZeta_ne_zero`). NOT proved: the Euler product
itself and complex nonvanishing on `Re s > 1`; the missing input is multiplicativity of `a_K` (unique
factorization of ideals plus CRT) or an Euler product indexed by prime ideals. So `NonvanishingRight` stays a
hypothesis for general `K` (theorem for `ℚ`). Mathlib fit: `LSeriesSummable` for `dedekindZeta` on `Re s > 1` and
real positivity are small, natural missing API and plausible Mathlib PRs.

Round 62 closes the first half of that gap, in `DedekindEuler.lean`. For coprime `m, n` the map
`I ↦ (I + (m), I + (n))` is a bijection from ideals of norm `mn` to pairs of ideals of norms `m` and `n`, with
inverse `(J, J') ↦ JJ'` (`splitEquiv`; it uses only `N I ∈ I`, multiplicativity of `absNorm`, and
`IJ = I ∩ J` for coprime ideals), so `a_K(mn) = a_K(m) a_K(n)` (`coeff_mul`). Mathlib's
`EulerProduct.eulerProduct_hasProd` then gives the **Euler product over rational primes**,
`ζ_K(s) = ∏'_p ∑'_e a_K(p^e) p^{-es}` for `Re s > 1` (`dedekindZeta_eulerProduct_hasProd`, `_tprod`). The
product's tails are summable, so `ζ_K(s) ≠ 0` as soon as every local factor is nonzero
(`dedekindZeta_ne_zero_of_localFactor_ne_zero`, via `tprod_one_add_ne_zero_of_summable`), and
`NonvanishingRight` reduces to that (`nonvanishingRight_of_localFactor_ne_zero`). NOT proved: nonvanishing of the
local factors, which equal `∏_{𝔭 ∣ p} (1 - p^{-f_𝔭 s})⁻¹` once the splitting of `p` into prime ideals is
formalized; so `NonvanishingRight` is still a hypothesis for general `K`. Mathlib fit: `coeff_mul` and the
Euler product are natural missing API for `dedekindZeta` and plausible Mathlib PRs.

Round 63 closes the gap, in `DedekindLocal.lean`. The primes over `p` are the support of the factorization of
`(p)` (`primesAbove`), with `N 𝔭 = p^{f_𝔭}` (`absNorm_eq_pow`); by unique factorization of ideals,
`k ↦ ∏_𝔭 𝔭^{k_𝔭}` is a bijection from exponent vectors onto the ideals of `p`-power norm
(`toSigma_bijective`). With the finite product-of-series lemma `piProdP_all`, this gives the local factor
`∑_e a_K(p^e) p^{-es} = ∏_{𝔭 ∣ p} (1 - N𝔭^{-s})⁻¹` on `Re s > 1` (`localFactor_eq_prod`), hence
`ζ_K(s) ≠ 0` on `Re s > 1` for every number field, unconditionally (`dedekindZeta_ne_zero`), and
`NonvanishingRight` for every `K` (`nonvanishingRight`). Rounds 50 and 60's results that assumed it now hold
from `SimplePoles` alone (`fm414_neg'`; the conditional versions are kept). Mathlib fit: `localFactor_eq_prod`
and `dedekindZeta_ne_zero` complete the Dedekind-zeta Euler-product API (with rounds 61–62) and are the most
PR-worthy pieces of this sequence; `piProdP_all` is a general lemma Mathlib also lacks in this form.

Round 64 checks whether the last analytic hypothesis, `SimplePoles` (Hecke), can be discharged from
Mathlib v4.34.1. It cannot: `NumberField/DedekindZeta.lean` defines `dedekindZeta` as an `L`-series with
only the class number formula (a limit along `(1, ∞)`); there is no completed Dedekind zeta, no
continuation or functional equation, and Poisson summation is only on `ℝ`, not for lattices in `ℝⁿ`.
This is an explicit Mathlib gap ("Hecke's theorem"). What round 64 proves, in `SimplePolesCrit.lean`, is
the exact reduction: for any continuation, `SimplePoles` is equivalent to boundedness of `(s - 1) Λ_K(s)`
on a punctured disc around `1` (`nonempty_simplePoles_iff`; the bound at `0` comes from the functional
equation, by Riemann's removable-singularity theorem applied at both poles). The bound holds for `ℚ`
(`boundedAtOne_rat`). So beyond the existence of the continuation, Hecke's theorem enters through one
statement at `s = 1`. Route to close the gap (not attempted): `WeakFEPair` from
`Mathlib.NumberTheory.LSeries.AbstractFuncEq` applied to the theta series of each ideal class over the
fundamental domain of the units (Mathlib already has `mixedEmbedding.fundamentalCone`), which needs
Poisson summation on a lattice in `ℝ^{r₁} × ℂ^{r₂}` (missing) — a multi-round, Mathlib-scale project.


Round 75 (2026-11-20) uses the new boxes for three results of obligation 33. `HbSum.lean` proves the symmetric
partial-fraction expansion `𝔪(z) = -F'/F = ½ Σ_ρ (1/(ρ - z) + 1/(-ρ - z))` for any even entire `F` with a
genus-one locally uniform Hadamard product (evenness cancels `b` and the non-absolutely-convergent `Σ 1/ρ`),
hence `Im 𝔪 > 0` above the zeros (`HbSum.im_neg_logDeriv_pos`), and applies it to `F(z) = ξ(1/2 - iz)`:
`prop:hb-high` second clause (`riemannXiUpper_im_neg_logDeriv_pos`, CONDITIONAL on B1 for `ℚ`, B3', B6;
closes obligation 30). `HbEquiv.lean` proves `prop:hb` as a `List.TFAE` (`Hb.hb_tfae`): RH for `F`, the Herglotz
condition, the weak Herglotz condition and the HB inequality for `E = F + iF'` are equivalent; only (i) ⇒ (ii)
uses the boxes, the other implications are unconditional (with `eq:hb-modulus`, `Hb.normSq_E_sub`, and the
unconditional reflection `ξ(s̄) = conj ξ(s)`, `Hb.completedXi_conj`). `XiKZerosInfinite.lean` proves that `ξ_K`
has infinitely many zeros for every number field (`Hecke.zeroIdx_infinite`, CONDITIONAL on B1 and B3): a finite
Hadamard product gives `‖ξ_K(x)‖ ≤ e^{A+Bx}` on `x ≥ 0`, while `‖ξ_K(2n)‖ ≥ (n-1)!/(2π)^{2n}`. Not reached:
`prop:xiK-asymp`, `N_K(T) = O(T log T)`, `kun-AW6`, `thm:ff-det`/`thm:det-K` and the determinant family, and
obligation 32 (obligation 34).

Round 76 (2026-11-20) proves three results that need no determinant work. `WindowPoisson.lean` proves
`thm:window` (i) for every complex-valued `φ ∈ C_c^∞(ℝ)` and `L > 0` (`WindowPoisson.window_poisson`), with
`def:window-objects` (a), (b) (`transform`, `cosetPt`, `cosetPt_injective`): the sum of `Φ` over the half-shifted
coset converges and equals `L ∑_k (-1)^k e^{kL/2} φ(kL)`, by Mathlib's Poisson summation for Schwartz functions
applied to `u ↦ ψ(Lu)`. `R15Mellin.lean` proves `prop:R15` (i) with `def:ccm-kernel` (`k0`): for `Re s > 0`,
`M_{k₀}` converges absolutely and equals `(1/8) s(s-1) π^{-s/2} Γ(s/2)` (`R15Mellin.hasMellin_k0`), from the
Gaussian moments `hasMellin_gauss`. `NKCount.lean` proves `N_K(T) = O(T log T)` for every number field,
CONDITIONAL on B1 (`NKCount.zeroCount_le`), by Mathlib's Jensen inequality on discs about `2` and the strip
clause of round 71. Not reached: `prop:xiK-asymp`, obligation 32, `prop:kun-diag`/`prop:kun-AW6`, `prop:R15`
(ii)–(iii), `prop:beta` integral, `prop:schwartz`, `q^Θ = F`, `prop:arch-window-limit` (obligation 35). The
determinant family was left untouched while the `def:regdet` manuscript change is pending.

Round 77 (2026-11-20) brings `RegDet.lean` in line with the revised `def:regdet` in `notes.tex`
(`regdet-canonical`, approved by Taylor): item (c) now asks for continuation to a half-plane `Re w > -ε(s)`.
`Regularization.OnHalfPlane` records this, `IsZetaRegularizable` is the revised (c), and
`detreg_eq_of_onHalfPlane` proves the new paragraph after the definition: any two half-plane regularizations of
one cut give the same `det_reg`, so `canonicalDetreg` depends only on the cut (`detreg_eq_canonical`). Finite
spectra are zeta-regularizable in the revised sense (`ofFinite_onHalfPlane`, `isZetaRegularizable_finite`), and
adding a finite spectrum preserves it (`addFinite_onHalfPlane`). `HbNoRvM.lean` removes B6 from `prop:hb-high`
(second clause) and `prop:hb` (`riemannXiUpper_im_neg_logDeriv_pos'`, `Hb.hb_tfae'`, CONDITIONAL on B1 for `ℚ` and
B3' only): the zero of `F` now comes from `Hecke.zeroIdx_infinite` at `K = ℚ`. The round-75 statements are kept
as wrappers of the new `_of_zero` forms. The B4' docstring cites DLMF (5.11.1) and §5.11(ii) (checked online)
instead of an unchecked Olver chapter. The determinant family stays open: `thm:ff-det` needs the Hurwitz zeta
function `ζ_H(w, z)` for complex `z`, its continuation in `w` and Lerch's formula `∂_w ζ_H(0, z) =
log Γ(z) − ½ log 2π` (`thm:imp-hurwitz`); Mathlib's `HurwitzZeta` has only real parameters in `[0, 1)`. Everything
downstream (`thm:det-K`, `det-K-rf`, `Zpm`, `prop:ff-cut`, `prop:N-count` (ii), the detreg clause of
`prop:one-branch`) waits on it (obligation 36).

Round 78 (2026-11-20) applies the `fidelity-76-77.md` fixes and adds four modules. The round-73 `def:regdet` row now
says that `Regularization` alone is the *superseded* (c); `R2.det_sum_onHalfPlane` restates `prop:R3` (iii) for the
revised `def:regdet` (half-plane regularization in and out, so the identity is about the canonical determinant of
the combined cut); `NKCount.zeroSet_finite` proves that the zeros counted by `N_K(T)` form a finite set
(`zeroCount_eq_sum`, `zeroCount_pos`), so `zeroCount` is a genuine finite count; and the B1 row lists the B6-free
round-77 forms. `R15Tail.lean` proves `prop:R15` (iii) (`R15Tail.tail`) and `R15Periodization.lean` proves
`prop:R15` (ii) (`R15Periodization.R15_ii`: the integral of `𝓔k₀(u) u^{s−1/2} du/u` converges absolutely for
`Re s > 1` and equals `ζ(s) M_{k₀}(s) = ξ(s)/4`), so `prop:R15` is complete. `KunDiag.lean` formalizes the
counting core of `prop:kun-diag` on diagonal entries: (iii) `Nsum_le`, `Nsum_finite`; (iv) `zero_infinite`;
(v) the two counterexamples `sharp_one`, `sharp_two`; (i), (ii) (self-adjointness, compact resolvent as an operator
property) are not modelled. `KunAW6.lean` proves `prop:kun-AW6` (`KunAW6.kun_AW6`, CONDITIONAL on B1 and B3)
from the output of `thm:rh`/`prop:hilbert` taken as hypotheses on the diagonal entries of `T₁`
(`ξ_K(1/2 + iτ_i) = 0`, every zero arises), following the manuscript's proof with `ξ_K(s̄) = conj ξ_K(s)` and
infinitely many zeros (`KunAW6.zeroSet_infinite`, from `Hecke.zeroIdx_infinite`).

Round 81 (2026-11-20) is a fix-only round from the round-79 review (`ai/2026-11-20-notes-lean-finish/fidelity-79.md`). The round-72 `prop:beta` claim row is marked superseded by the round-79 row; the two instances in `KunArchGal.lean` (`NeZero ((4 : ℕ) : ℚ)`, `IsCyclotomicExtension {4} ℚ QI`) are now `local`, so they no longer leak to importing modules; and `kun_arch_gal_divisors` bundles `kun_arch_gal` with the pole divisors of `L_∞(χ, s)` and `L_∞(χ², s)`. No new manuscript targets.

Round 80 (2026-11-20) adds three modules. `SchemeZeta.lean` defines the zeta function of a scheme
`ζ(X, s) = ∏_{x ∈ X₀}(1 - N(x)^{-s})^{-1}` (`SchemeZeta.zeta`, a `tprod` over Mathlib's `closedPoints`, with
`N(x) = #κ(x)`), proves `ℤ` Jacobson (`isJacobsonRing_int`), that residue fields at closed points of a scheme
locally of finite type over `Spec ℤ` are finite (`finite_residueField`, `one_lt_norm`), `prop:zeta-intrinsic`
(`relClosedPoints_eq`, `zetaRel_eq`: over a Jacobson base such as `Spec ℤ` or `Spec 𝒪_K`, the points closed in
their fibre over a closed point are the closed points of `X`, so the relative and absolute Euler products agree),
and `ζ(Spec ℤ, s) = ζ(s)` for `Re s > 1` (`zeta_specInt`). `XiKPrimeSum.lean` bounds the prime sum of
`def:deninger-gamma` (e): `‖Σ_𝔭 Σ_k N𝔭^{-kz}/k‖ ≤ 2^{2 - Re z} S_K` for `Re z ≥ 2` (`norm_primeSum_le`), via
`(𝔭, k) ↦ 𝔭^k` injective and `Σ_I N I^{-σ} < ∞` (`summable_idealNorm_rpow`). `XiKAsymp.lean` proves the first
expansion of `prop:xiK-asymp`, CONDITIONAL on B4': `stdBranch_asymp`, `f(z) = Az log z + Bz + C log z + E +
O(|z|^{-1})` along `z = s + x`, `x → ∞`, from the exact identity `stdBranch_sub_main`; `logGamma_eq_real`
shows B4''s `L` is the branch of `log Γ` real on `(0, ∞)`. The expansions of `f'` and `G_ξ = -f''`, and the
product formulas `prop:P1Z`, `prop:kun-tate` (i), remain open (obligation 39).

Round 79 (2026-11-20) adds two modules. `BetaIntegral.lean` completes `prop:beta`: `integral_pos` computes
`∫_0^∞ x^{1-w}(x + r)^{-2} dx = Γ(2 - w)Γ(w) r^{-w}` for `r > 0` (writing `(x + r)^{-2} = ∫_0^∞ u e^{-(x+r)u} du` and
exchanging the integrals); `P_mul_Gamma` gives `P(w)Γ(2 - w)Γ(w) = 1` on `0 < Re w < 2`; `differentiableOn_integral`
proves the integral holomorphic in `a` on the slit plane (`lower_bound`: `‖x + a‖ ≥ c(1 + x)` locally uniformly,
as in the manuscript's proof); `beta_identity` is the identity `a^{-w} = P(w) ∫_0^∞ x^{1-w}(x + a)^{-2} dx` for
every `a ∈ ℂ ∖ (-∞, 0]` (identity theorem); and `expansion` is `(2π)^w P(w) = w + (1 + log 2π)w² + O(w³)`.
`KunArchGal.lean` instantiates `prop:kun-arch` at `Gal(ℚ(i)/ℚ)`, with `ℚ(i)` encoded as `CyclotomicField 4 ℚ`:
`card_gal` (order two), `chi`/`chi_ne_one` (the nontrivial character `χ₄ ∘ (Gal ≃* (ZMod 4)ˣ)`), and
`kun_arch_gal` (for every complex embedding `φ`, complex conjugation `c` for `φ` is `≠ 1`, generates the group,
and `L_∞(χ, s) = Γ_ℝ(s + 1)`, `L_∞(χ², s) = Γ_ℝ(s)`).

Round 74 (2026-11-20) adopts the second black-box set (B3', B4', B6; see "Black boxes"), applies the fixes of
the independent review of rounds 70–73 (`ai/2026-11-20-notes-lean-finish/fidelity-70-73.md`), and uses B6.
`BlackBoxes2.lean` states B3' `HadamardOrderOneLU` (supersedes B3 via `hadamardOrderOne_of_LU`), B4'
`LogGammaStirling` (supersedes B4, which is kept but has no consumers) and B6 `RiemannVonMangoldt`.
`RegDet.lean` adds `detreg_eq_of_common_domain` / `detreg_eq_of_dom_eq`: two regularizations of one cut give
the same `det_reg` when their continuation domains share a preconnected open set containing `0` and a point
right of both abscissae (identity theorem). `AW5Spectral.lean` adds the multiplicity clause of
`prop:aw5-contains` (iii) (`aw5_spectral_mult`: `#{k : τ_k = μ} = dim V_{(j/2+iμ)}`). Under B6:
`ZetaZerosRvM.lean` proves `N(T) → ∞`, zeros of `ζ` in the open strip of arbitrarily large height, and that
the zeros with `Im ρ > 0` form an infinite set; `KunOverZ.lean` proves `prop:kun-over-Z`; `P1ZZeros.lean`
proves the zero clauses of `prop:P1Z` for `ζ(s)ζ(s-1)` (description of the zeros and the strip clauses
unconditionally, nonemptiness and the vertical-line clause under B6; the product formula is obligation 32).
Not reached: `prop:xiK-asymp` (B4'+B1+B3'), infinitude of zeros of `ξ_K`, `N_K(T) = O(T log T)`,
`prop:hb-high` second clause / `prop:hb` / `kun-AW6` under B3', `thm:det-K` (obligation 33).

Round 73 (2026-11-20) closes `prop:F0` unconditionally, formalizes `def:regdet` and `prop:R3` (iii), and proves
`prop:rouche-route`. `EtaZeta.lean`: the paired alternating zeta function `η(s) = Σ_k ((2k+1)^{-s} - (2k+2)^{-s})`
is holomorphic on `Re s > 0` (`differentiableOn_eta`, mean-value bound), equals `(1 - 2^{1-s})ζ(s)` there
(`eta_eq_of_one_lt`, then the identity theorem on a convex region avoiding `s = 1`: `eta_eq_on_region`), and is
a positive real on `(0, 1)`; hence `ζ(σ)` is real and negative for `0 < σ < 1` (`riemannZeta_neg_of_mem_Ioo`),
`ζ(1/2) < 0` and `F(0) = ξ(1/2) > 0` (`F_zero_pos`). `RegDet.lean` encodes `def:regdet` (a)–(d) for a spectrum
with multiplicities (`SpectralCut`, `specZeta`, `Regularization`, `detreg`), proves uniqueness of the entire
extension (`Regularization.D_unique`) and, for finite spectra, that every cut is regularizable
(`Regularization.ofFinite`) with `det_reg = ∏ ((s - ρ)/2π)^{m(ρ)}` for every cut and regularization
(`detreg_finite`). `RegDetSum.lean` adds a finite spectrum to a regularizable one on a smaller cut domain
(`Regularization.addFinite`, `detreg_addFinite`) and gives `prop:R3` (iii) (`R2.det_sum`, with
`∏_{ρ ∈ spec Θ}(s - ρ)/2π = (2π)^{-4}p(s)`: `R2.finDet_eigs`). `Hurwitz.lean` proves Hurwitz's theorem by the
maximum-modulus argument (`Hurwitz.exists_zero`) and the zero-reality step (`im_eq_zero_of_tendsto`).
`RoucheRoute.lean` proves that `ĝ` is entire for `g ∈ L²([-ℓ, ℓ])` (`Gap.differentiable_hat`), that every zero
of `F` lies in `|Im z| < 1/2` (`riemannXiUpper_eq_zero_mem_strip`), and `prop:rouche-route` (`rouche_route`).
No black box was added.

Round 72 (2026-11-20) builds the split-signature datum of `def:split-datum` and proves `prop:kun-hodge-strict`
(`KunHodgeStrict.lean`): `splitDatum γ` is a `SurfaceDatum` on `ℂ⁴` (AW1 + AW3 and the algebraic part of AW4 in
degree one) at `ρ = 1/2 + iγ`; it satisfies AW4-V and AW4-E in degree one (`aw4V_splitDatum`, `aw4E_splitDatum`),
`h₁` is indefinite on `V_ρ` (`not_definiteOn`), and `h_⊗` is not positive definite on `V_ρ ⊗ V_{ρ̄}`
(`not_posDef_blockGram`), so the Hodge index clause fails (`not_hodgeIndex`). `R12Kernels.lean` completes
`prop:R12`: all zeros `(2m + 1)π ± ia` of `μ̂_a` (`muHat_eq_zero_iff`), their simplicity (`deriv_ne_zero`), none
real (`im_ne_zero`), and for the Gaussian kernel `k_{a,σ}` smoothness, integrability, positivity and
`∫ e^{izt} k_{a,σ} = e^{-σz²}(cos z + cosh a)` for all `z ∈ ℂ` (`fourier_k`); it reuses the round-1 `R12.μ` and
`R12.fourier_eq`. `BetaP.lean` proves the `P` clauses of `prop:beta`: `P` is entire, `P(1) = 1`, and
`P(w) = sin(πw)/(π(1 - w))` off `w = 1`. No black box was added.

Round 71 (2026-11-20) applies the independent fidelity review of rounds 65–69
(`ai/2026-11-20-notes-lean-finish/fidelity-65-69.md`). `XiKStrip.lean` proves the strip clause of `prop:xiK`
(every zero of `ξ_K` lies in `0 ≤ Re s ≤ 1`: `re_mem_Icc_of_xi_eq_zero`, from the round 61–63 Euler product and
the functional equation) and its order clause (`analyticOrderAt_zetaCont_eq`: for `0 ≤ Re s`, `s ∉ {0, 1}`,
`ord_s ζ_K = ord_s ξ_K`, with `ζ_K` continued as `zetaCont C = Λ_K · (|d_K|^{s/2}Γ_ℝ^{r₁}Γ_ℂ^{r₂})⁻¹`, which equals
`dedekindZeta K` on `Re s > 1` and is holomorphic off `{0, 1}`), and their B1 forms `Hecke.xiK_strip`,
`Hecke.xiK_order`. `XiKConj.lean` proves `ξ_K(s̄) = conj ξ_K(s)` (`XiKConj.xi_conj`), `ord_{σ̄} = ord_σ` for any
real-on-real entire function (`analyticOrderAt_conj`), and hence the conjugation clause of `prop:N-count` (i) for
`ξ_K` (`NCount.xi_conj`, `Hecke.nCount_conj`). `R2Block.lean` restates `prop:R2` (i) about `gradedBlock` itself
(`R2.axioms_block`: on the basis `eb 0, …, eb 3` of `V¹` the generator, pairing and star are `Θ`, `Ω`, `S`).
`KunArchOrderTwo.lean` discharges the hypotheses of `prop:kun-arch` for every group of order two with its
nontrivial element and character (`KunArch.orderTwo`) and instantiates it at `Multiplicative (ZMod 2)` with the
sign character (`KunArch.zmod2`). B2''s docstring now cites Weil II (3.3.9) for the proper case. Claim-table
labels for `thm:kun-square` and `prop:N-lines` now state their conditions. No black box was added.

Round 70 (2026-11-20) closes `prop:gap`, `prop:R16` and `prop:R9`, adds the diagonal model of
`prop:aw5-contains` (iii) and the zero-free clause of `prop:hb-high`. `GapStrip.lean` proves `eq:gap-l2` for a
symmetric map on any finite-dimensional inner product space (`Gap.gap_l2`) and, on `L²([-ℓ, ℓ])` with the
Fourier transform of `def:weil-form` (a), the Cauchy–Schwarz strip bound `|ĝ(z)| ≤ C(ℓ, b)‖g‖₂` for
`|Im z| ≤ b` (`Gap.norm_hat_le`, equality of the kernel norm `Gap.norm_kernel_eq`), hence `eq:gap-strip`
(`Gap.gap`). `R16.lean` proves all of `prop:R16` (`R16.norm_A_k`, `norm_k_sub_proj`, `f_even`, `norm_f`,
`Fminus_f`, `tendsto_Fminus_f`, `isGreatest_Fminus`, `tendsto_norm_x`, `norm_A_x`). `AW5Spectral.lean` proves
`prop:aw5-contains` (iii) for the diagonal operator of `prop:hilbert` (`AW5Spectral.aw5_spectral`), without the
identification with AW5's generator. `R9.lean` proves `prop:R9` (i)–(ii) and (iii) for bounded operators
(`R9.reflect_companion`, `order_companion`, `order_reflect_companion`, `example_E`, `example_Esharp`,
`example_order`, `ker_le_span`). `HbHigh.lean` proves that `F(z) = ξ(1/2 - iz)` has no zero with `Im z ≥ 1/2`
(`riemannXiUpper_ne_zero`). Not done: `prop:aw5-contains` (iv), `q^Θ = F` (obligation 13), the positivity
clause of `prop:hb-high`, `prop:beta`, `prop:ff-cut`, `prop:zeta-intrinsic`, `prop:P1Z`, `prop:kun-tate` (i),
`thm:kun-hodge`, `prop:kun-hodge-strict` (obligation 29). No black box was added.

Round 69 (2026-11-20) closes four leftovers. `LefschetzTrace.lean` proves `Tr(F^k) = ∑_{α ∈ roots χ_F} α^k`
for any endomorphism of a finite-dimensional complex space (`trace_pow_eq_sum_roots`) and hence that the
round-5 Lefschetz numbers of the eigenvalue multisets are the alternating traces `∑_j (-1)^j Tr(F^k | V^j)`
(`lefschetzNumber_eq_sum_trace`; the linear-algebra step of `thm:ff-lefschetz`). `R11Pole.lean` proves
`prop:R11` (iv) (`R11.im_neg_logDeriv_lt_zero`). `UnitProduct.lean` builds the product of `def:susp-datum` (a)
on the degree-zero suspension `unitSpace q` and an isomorphism `unitSpace q ≃ₗ 𝟙_q` that is multiplicative,
unital and intertwines `Θ` (`prop:unit`, first clause). `AlgebraFormReal.lean` proves `prop:algebra-form` (i)
(moduli) and (ii) over any ordered field `K` with positive algebra maps `K → ℝ → ℂ`, covering `ℚ` and `ℝ`
(`PositiveTraceOrd.norm_eq_rpow_of_isRoot`, `rep_isSemisimple`, `rep_norm_eq_rpow`, `rep_iSup_eigenspace`).
Not done: `q^Θ = F` (obligation 13), `prop:aw5-contains` (iii)–(iv), `prop:gap`, `prop:R16`, `thm:kun-hodge`,
`prop:kun-hodge-strict` (obligation 28). No black box was added.

Round 68 (2026-11-20) adopts four black boxes (new section "Black boxes" below; Taylor's approval:
"Yes, check then adopt", and for B2' "Adopt, flag unchecked"). `BlackBoxes.lean` states B1
`HeckePackage K`, B2' `WeilConjectures`, B3 `HadamardOrderOne` and B4 `StirlingBox` as `Prop`s (never
`axiom`s), with the bridges `HeckePackage.continuation : HeckePackage K → DedekindContinuation K` and
`HeckePackage.simplePoles`. `HeckeCorollaries.lean` restates every headline Hecke-conditional result for
every number field `K : Type` under B1 alone (`prop:xiK`, `prop:content` (i), (iv), `prop:N-count` (i),
`thm:main-number-fields` first sentence, `thm:A` (i), FM's `ζ(X̄_K, s) = e^{a+bs}Λ_K(s)`, FM Prop. 4.14 at
`n = 1`, `n = 0`, `n < 0`); the hypothesis-form theorems are kept. `XiKHadamard.lean` proves the Hadamard
product of `ξ_K` (`thm:imp-stirling` (ii)–(iii) applied to `ξ_K`) under B1 + B3. `NLinesWeil.lean` gives
`prop:N-lines` under B2' for any smooth proper geometrically irreducible curve times `ℙ¹_F` (multiset form
`zetaXM`, zeros on `Re s = 1/2, 3/2`, possible poles on `Re s ∈ {0, 1, 2}`; the `ℙ¹` point identification `e`
remains a hypothesis), and the remark after `prop:formal-curve` (`exists_count_ne_zero`: no such curve has
`N_n = 0` for all `n ≥ 1`). B4 has no consumer yet (`prop:xiK-asymp`, `thm:det-K`: obligation 27).

Round 67 (2026-11-20) formalizes four Künneth-section claims. `KunOpen.lean` proves `prop:kun-open` in full:
for an exact sequence `0 → E⁰ → F⁰ → G⁰ → E¹ → F¹ → G¹ → E² → F² → 0` of spectral cores with intertwining
maps (`KunOpen.KunSeq`), the alternating spectral divisors satisfy the identity coefficient by coefficient
(`KunSeq.altDiv_eq`), whatever the maps (`altDiv_eq_of_same`), and `Sp(E⁰)` is `0` or `[0]` in the two special
cases (`mult_E0_of_injective`, `mult_E0_of_zero`); the proof restricts the sequence to generalized
eigenspaces (`range_res_eq_ker_res`) and uses the Euler characteristic of an exact sequence (`euler_eight`).
`KunArch.lean` proves `prop:kun-arch`: `L_∞(χ, s) = Γ_ℝ(s + 1)` and `L_∞(χ ⊗ χ, s) = Γ_ℝ(s)` from `def:artin` (b)
(`LInftyChar_of_ne_one`, `LInftyChar_sq`), the pole divisors `Σ_n [-2n]` and `Σ_n [-1-2n]` of `Γ_ℝ(s)` and
`Γ_ℝ(s + 1)` as meromorphic orders (`meromorphicOrderAt_Gammaℝ`, `meromorphicOrderAt_Gammaℝ_add_one`), and the
self-sum `Σ_k (k + 1)[-2-2k]` (`conv_D₁_neg_two_sub`, `conv_D₁_eq_zero`). `KunSquare.lean` closes obligation 9:
infinitely many contributing pairs make `(V ⊗ W)_{Θ∼λ}` infinite-dimensional (`not_finite_of_pairs_infinite`),
which gives `thm:kun-square` (iv) for any injective intertwining `κ : V ⊗ W → H`
(`not_spectralCore_of_inter_infinite`, `not_spectralCore_self`) and the last step of (iii)
(`add_mem_spec`, `exists_accPt_of_infinite_bounded`). `NCount.lean` proves `prop:N-count` (i): the enlarged
divisor `Σ' = div f + Σ_k ([1/2 + i eᵏ] + [1/2 − i eᵏ])` of a symmetric entire `f ≢ 0` is the spectrum of a
spectral core (`NCount.spectralCore`, `rank_maxGenEigenspace`), symmetric (`mult_one_sub`, `mult_conj`), with
count `N_{Σ'}(T) = N_Σ(T) + ⌊log T⌋` (`card_count`); `NCount.xi` is the case `f = ξ_K`, conditional on
`SimplePoles` as in `prop:content`. `prop:N-count` (ii) and the round-4 Künneth/Hodge targets are open
(obligation 26).

Round 66 (2026-11-20) proves the order formula. `MainGeneral.lean` encodes `def:graded-realization` as
`MainGeneral.GradedRealization d w Z` (spectral cores `V^j` with `div Z = ∑_j (-1)^{j+1} ∑_ρ m_j(ρ)[ρ]`, Mathlib's
`MeromorphicOn.divisor`) and `MainGeneral.Polarization` (positive infinitesimal polarizations of weight `w + j`),
and proves `thm:main-general` in full: diagonalizability and purity in each degree, and
`ord_ρ Z = (-1)^{j+1} dim ker(Θ_j − ρ)` on the line `2 Re ρ − w = j ∈ {0, …, 2d}`, `0` off the lines
(`meromorphicOrderAt_eq_of_line`, `meromorphicOrderAt_eq_zero_of_off`), with zeros on odd and poles on even lines
and each `Sp_j` determined by `Z` (`exists_odd_of_divisor_pos`, `exists_even_of_divisor_neg`, `mult_eq_of_line`).
`thm:A-schemes` (ii)–(iii) follow for a positive datum `WeightedAlgebraDatum V d 0` (derivation rule, trace
equivariance, AW4) satisfying AW2 (`aschemes_ord`, `aschemes_ord_off`, `aschemes_zero`, `aschemes_pole`,
`aschemes_mult`; `ofDeninger` for polarized Deninger structures). The first sentence of `thm:main-number-fields`
is `re_eq_half_of_xi_eq_zero`, conditional on `DedekindContinuation K` with simple poles as elsewhere, and
unconditional for `K = ℚ` (`riemannHypothesis_of_realization`). `XiZetaOrder.lean` removes round 65's caveat on
`prop:converse`: `ord_ρ ζ = ord_ρ ξ` at every nontrivial zero (`analyticOrderAt_riemannZeta_eq_completedXi`), so
`PositiveZetaCore.mult_eq_zeta` counts each nontrivial zero with its `ζ`-multiplicity. `NoPositivityCancel.lean`
proves the first clause of `prop:no-positivity-cancel` (`DeningerStructure.exists_eta`, any `d`); the adjunction
itself is obligation 25. `prop:F0`'s `ζ(1/2) < 0` remains obligation 24.

Round 65 (2026-11-20) closes five small manuscript claims and relabels old claim IDs.
`prop:converse` is restated on the current definitions in `ConverseCore.lean`: `PositiveZetaCore` is a
spectral core (`def:spectral-core` (b)) with a `PosHermForm` satisfying `IsInfPol h Θ 1` and
`mult Θ ρ = ord_ρ ξ` for every `ρ`, and `riemannHypothesis_iff_nonempty_positiveZetaCore` proves RH ⟺
such a core exists; on the way, `ArithmeticWeilCohomologyQMult.spectralCore` shows the
multiplicity-faithful structure is a spectral core (`not_accPt_zeros_completedXi`: the zeros of the entire
`ξ ≢ 0` do not accumulate). `prop:R1` (i)–(ii) are in `R1.lean` (`R1.dual`, `R1.dual_off_line`, `R1.split`).
`prop:R2` (i)–(iii) and `prop:R3` (i)–(ii) are in `R2Block.lean`: (i) packages the quaternionic block as a
`HermAlgebraDatum _ 1 0` (`R2.gradedBlock`, the `prop:content` (iii) assembly with one quartet), with
`J² = -1` and `h₀`, `h₂` positive (`R2.axioms`); (ii) adds the signature `(2, 2)` (`R2.signature`); (iii) is
`R2.re_of_eigen`; `prop:R3` (i) is `R2.cone_acyclic` and (ii) is `R2.poly` (with `pPoly` of degree four).
`prop:R3` (iii) needs `def:regdet` (obligation 1). `prop:F0` is reduced in `XiHalf.lean` to the sign of
`ζ(1/2)`: `ξ(1/2) = -(π^{-1/4}Γ(1/4)/8) ζ(1/2)` is real, `0 < ξ(1/2) ↔ ζ(1/2) < 0`
(`completedXi_half_pos_iff`), and `F(0) > 0` is proved under `ζ(1/2) < 0`
(`F_zero_pos_of_zeta_half_neg`); `ζ(1/2) < 0` itself needs the Dirichlet eta function and its continuation
to `Re s > 0`, which Mathlib v4.34.1 lacks (obligation 24). The claim table now also maps the old IDs C-PUR,
Q1-L4.2, C-A, C-B, C-CONV, R2 and R3 to the manuscript labels `thm:main-general`, `thm:A-schemes`, `thm:A`,
`thm:B`, `prop:converse`, `prop:R2` and `prop:R3`, with the clauses each covers.

Round 57 identifies `H²(X̄_K, ℝ(1)) ≅ ĈH¹(X̄_K)_ℝ` in `ArakelovChowReal.lean` (the case `n = 1` of the
isomorphism `CH^n(X̄)_C ≃ H^{2n}(X̄, C(n))` used in the proof of FM Prop. 4.14, p. 535, citing FM's 2018 paper
[13, Prop. 2.11]). `ChowR K` is the arithmetic Chow group of `Spec 𝓞_K` **with real coefficients** (FM
Notation 4.13, p. 534): real divisors and real Green vectors modulo the `ℝ`-span of round 48's principal
divisors. The arithmetic degree extends `ℝ`-linearly (`chowDegreeR`, restricting to `chowDegree` by
`chowDegreeR_comp`) and is an isomorphism `chowDegreeREquiv : ChowR K ≃ₗ[ℝ] ℝ`: surjective from round 48,
injective by finiteness of the class group (`exists_green_of_div`) and Dirichlet's theorem through round 55's
`range_regR` (`mem_relR_of_halfSumR_eq_zero`: degree-zero real Green vectors are `ℝ`-combinations of unit
Green vectors). Composing with round 56's `compactOne_Hbar_two` gives `chowRToH2 : ChowR K ≃ₗ[ℝ] H²(X̄_K, ℝ(1))`,
which is the degree under `H² ≅ ℝ` (`compactOne_Hbar_two_chowRToH2`).

Round 53 continues the Flach–Morin path (E2 in all degrees) in `HodgeProj.lean`: `ProjSpace.hodge K n` is
the Hodge datum of `ℙⁿ_{𝓞_K}`, with `H^{k,k} = ℂ^{Hom(K,ℂ)}` for `0 ≤ k ≤ n`, other pieces zero, and
`F_∞ = (−1)^k (f ↦ f ∘ conj)` on `H^{k,k}` (the sign is the orientation reversal of conjugation on `ℙ¹(ℂ)`;
modelled, not derived). Its Hodge numbers are computed: `h^{k,k} = [K:ℚ]`, `h^{k,+} = r₁ + r₂`,
`h^{k,−} = r₂` for `k ≤ n` (`hplus_eq`, `hminus_eq`; the sign `(−1)^k` cancels the one in FM's definition),
so `L_∞(h^{2k}, s) = Γ_ℝ(s−k)^{r₁} Γ_ℂ(s−k)^{r₂}` (`LInfty_two_mul`), odd `L_∞` are `1` (`LInfty_eq`), and
`ζ(X_∞, s) = ∏_{k=0}^n Γ_ℝ(s−k)^{r₁} Γ_ℂ(s−k)^{r₂}` (`zetaInfty_eq`; `zetaInfty_zero` recovers round 50 for
`n = 0`). With the definitional `ζ(ℙⁿ_{𝓞_K}, s) := ∏_k ζ_K(s−k)` (`zetaPn`), FM's completed zeta is
`ζ(ℙ̄ⁿ, s) = ∏_{k=0}^n e^{a + b(s−k)} Λ_K(s−k)` for `Re s > n + 1` (`ProjSpace.zetaFM_eq`), matching the
proof of Theorem D in `ai/2026-10-31-conditional-dynamical-cohomology/report.md`.

## Black boxes

Round 68. Four published theorems missing from Mathlib at this pin, stated in `WeilRH/BlackBoxes.lean` as
`Prop`s. **None is an `axiom`**: a result using one takes it as an explicit hypothesis (`hB`, `hW`, `hH`), so
its type shows the dependence, `#print axioms` stays standard, and its status is CONDITIONAL on the named
box. Each box is satisfiable because a Lean proof of it exists at another pin; the checks are in
`ai/2026-11-20-notes-lean-finish/checks/report.md`. Selection: survey of Mathlib, Tau Ceti, AxiomMath,
lana-agents and Palomar (`ai/2026-11-20-notes-lean-finish/blackboxes.md`).

| Box | Statement | Proved by (source) | Verification | Claims depending on it |
| --- | --- | --- | --- | --- |
| B1 `HeckePackage K` (`K : Type`) | Hecke: `Λ_K` holomorphic on `ℂ ∖ {0,1}`, `Λ_K(1-s) = Λ_K(s)`, Euler form on `Re s > 1` (notes normalization), `ξ_K = s(s-1)Λ_K` entire with `log‖ξ_K(s)‖ ≤ C‖s‖log‖s‖`, `ξ_K(0)ξ_K(1) ≠ 0` | `NumberField.exists_completedDedekindZeta_package_core`, AxiomMath/RiemannJensen@99f4e82 | kernel-checked at source pin (Lean v4.36.0), standard axioms | `prop:xiK`, `prop:content` (i), (iv), `prop:N-count` (i) (with the conjugation clause), `thm:main-number-fields` (first sentence), `thm:A` (i), FM `ζ(X̄_K)` comparison, FM 4.14 (`n ≤ 1`), `ζ(ℙ̄ⁿ)`, Hadamard product of `ξ_K` (with B3), infinitude of the zeros of `ξ_K` (with B3, round 75); `prop:kun-AW6` (with B3, round 78); for `K = ℚ` (growth of `ξ`): `prop:hb-high` second clause and `prop:hb` (i) ⇒ (ii) (with B3', B6, round 75; and B6-free with B3' only, round 77: `riemannXiUpper_im_neg_logDeriv_pos'`, `Hb.hb_tfae'`) |
| B2' `WeilConjectures` | Deligne (Weil I for projective `X`; Weil II (3.3.9) for proper `X`, pinpoint via a secondary citation): Frobenius multisets `A i` with `A 0 = {1}`, duality, Galois stability, integrality, purity `‖α‖ = q^{i/2}`, Lefschetz point count | `weil_conjectures`, AxiomMath/Weil@27cdb20 (= LeanEval problem, lean-eval@7c03706) | **NOT kernel-checked here** (Weil + Stacks build did not fit on disk); statement compared verbatim; source scan found no `sorry`/`axiom`; axiom set per source README only | `prop:N-lines` (geometric input, any curve), remark after `prop:formal-curve` |
| B3 `HadamardOrderOne` (superseded by B3' in round 74; kept, its users go through `hadamardOrderOne_of_LU`) | Hadamard: entire `f ≢ 0` with `log‖f z‖ ≤ C‖z‖^{3/2}` has `∑‖ρ‖^{-2} < ∞` and `f = e^{a+bs} s^m ∏(1 - s/ρ)e^{s/ρ}` | derived from `Complex.Hadamard.hadamard_factorization_of_growth`, AxiomMath fork of PrimeNumberTheoremAnd@d71f7b4 | kernel-checked at source pin (Lean v4.35.0-rc2), standard axioms | Hadamard product of `ξ_K` (`thm:imp-stirling` (iii) for `ξ_K`), infinitude of the zeros of `ξ_K` (round 75) |
| B4 `StirlingBox` (superseded by B4' in round 74; kept, no consumers) | Stirling: `Γ(s) = √(2π) s^{s-1/2} e^{-s} e^R`, `‖R‖ ≤ 7/(2‖s‖)`, for `Re s ≥ 0`, `‖s‖ ≥ 2` | `StirlingScratch.Gamma_stirling_exp_form`, AxiomMath/RiemannJensen@99f4e82 | kernel-checked at source pin, standard axioms | none yet (intended: `prop:xiK-asymp`, `thm:det-K`; obligation 27) |
| B3' `HadamardOrderOneLU` (round 74) | Hadamard in genus ≤ 1 with the product converging **locally uniformly** and `(log g)' = Σ(1/(s-ρ) + 1/ρ)` off the zeros; implies B3 | `hadamard_factorization_of_growth`, `hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ`, `logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne`, AxiomMath fork of PrimeNumberTheoremAnd@d71f7b4 | kernel-checked at source pin (Lean v4.35.0-rc2), standard axioms (`checks2/report.md`) | everything under B3 (via the bridge); `prop:hb-high` second clause and `prop:hb` (i) ⇒ (ii) (round 75) |
| B4' `LogGammaStirling` (round 74) | holomorphic `L` on the slit plane, `exp ∘ L = Γ`, `L 2 = 0`, `O(1/‖s‖)` Stirling remainder on each sector `|arg s| ≤ π - δ` | `logGamma`, `differentiableOn_logGamma`, `exp_logGamma`, `logGamma_two`, `exists_norm_logGamma_sub_stirling_le`, TauCeti@8794ab3 | kernel-checked at source pin (Lean v4.37.0-rc1), standard axioms | `prop:xiK-asymp`, expansion of `f` (round 80, `XiKAsymp.stdBranch_asymp`); still intended: the `f'`, `f''` expansions, `thm:det-K` family |
| B6 `RiemannVonMangoldt` (round 74) | `N(T) = (T/2π)log(T/2π) - T/2π + O(log T)` for `T ≥ 4` | `ZetaZeros.riemannVonMangoldt`, AxiomMath/ZetaZerosV2@1d7edeb | kernel-checked at source pin (Lean v4.34.0-rc2), standard axioms | zeros of `ζ` of arbitrarily large height and their infinitude (`ZetaZerosRvM`), `prop:kun-over-Z`, `prop:P1Z` (nonemptiness of `Z`, vertical-line clause), `prop:hb-high` second clause and `prop:hb` (i) ⇒ (ii) in their round-75 forms only (to know that `F` has a zero; round 77's `'` forms do without B6) |

Round 74 adds B3', B4', B6 (`WeilRH/BlackBoxes2.lean`), chosen by Taylor from the second survey
(`ai/2026-11-20-notes-lean-finish/blackboxes-2.md`); the Weil explicit formula (B5) was declined. Citation
pinpoints for B3', B4', B6 are chapter/section level as given by the sources, not re-verified against the books.

## Consistency of the structures

The repair report shows that the *unital* weighted package (AW1 derivation with a unit, AW3 trace
of weight `d + w`, AW4 positive star) has no nonzero model when `w ≠ 0`, and that dropping the unit
still forces every internal product, hence every `V^j`, to vanish. This tree contains that package
as `WeightedAlgebraDatum` and proves exactly this (`WeightedAlgebraDatum.eq_bot`,
`eq_zero_of_unit`); its `w = 0` case is inhabited by a nonzero unital model (`trivialModel`).

**`WeightedStarDatum` is not affected, for any `w`.** It is a single degree slice: a pairing
`V^j × V^{2d-j} → V^{2d}` into a *separate* top space, with no unit and no product inside one
algebra, so the R1/R2 arguments have nothing to act on. `weightedLineModel d w j τ` is a positive
datum of type `(d, w)` in degree `j` on `ℂ` with eigenvalue `(w + j)/2 + iτ`
(`exists_positive_nontrivial`). Hence none of its general-`w` results (`derivation_law`,
`B_equivariant`, `B_eq_zero_of_mem_maxGenEigenspace`, `re_eq_of_hasEigenvalue`, `isSemisimple`) is
vacuous for `w ≠ 0`. What the obstruction does say is that such slices cannot be assembled into one
nonzero *unital* graded algebra with internal products unless `w = 0`; the manuscript's repaired
`def:aw` (type `(d, 0)`) is the case used by the arithmetic models here (`lineModel`,
`TrivialModel.model`, `model0`, `model2`, `AW4Star.exists_weightedStarDatum`, the `prop:content`
data). Separately (repair R12), no structure here imposes a normalization `∗² = ±1`; where the trivial
model has `∗₁² = −1` that is proved, not assumed.

| Structure | Nonzero / nontrivial instance in Lean | Status |
| --- | --- | --- |
| `WeightedStarDatum d w j` + `IsPositive` | `weightedLineModel` (all `d, w, j`), `lineModel`, `TrivialModel.model`, `model0`, `model2` | inhabited for every weight |
| `WeightedAlgebraDatum V d w` | `trivialModel` (`w = 0`), `TrivialModel.gradedModel` (`d = 1`, `w = 0`, all three degrees nonzero; round 35), `TrivialModel.gradedModelInf` (infinite divisors; round 36) | `w ≠ 0` forces `V = 0` (`eq_bot`): results with `w ≠ 0` hold only for the zero object |
| `HermAlgebraDatum V d w` | `WeightedAlgebraDatum.toHerm` of any positive datum; `ContentAssembly.gradedDatum` (indefinite, `gradedDatum_indef`; round 36); `ContentAssembly.gradedDatumInf` (infinite divisors, given finite multiplicities and no finite accumulation point; round 37) | inhabited, including by indefinite data |
| `SurfaceDatum` | `SurfaceDatum.lineModel` (round 34) | inhabited |
| `Unit.arith`, `Unit.periodicTheta` (`def:unit`) | `𝟙 = (ℂ, 0)`; `𝟙_q` on the Laurent polynomials (`periodic_nontrivial`; round 38) | inhabited |
| `PairingModel.Data` | `ContentAssembly.data` (any divisor `Σ`) | inhabited |
| `PositiveTrace` | `matrixTrace` | inhabited |
| `PositiveTraceOrd` | `PositiveTraceOrd.self` (`K` itself, `τ = † = id`) | inhabited |
| `AW4EAddDatum` | `AW4Forms.nonempty_aw4EAddDatum` (from any positive infinitesimal polarization in finite dimension), `AW4EFDatum.truncation` | existence theorem; no named concrete instance |
| `AW4EFDatum` | `AW4EFDatum.scalarModel`, `satisfiesAW4EF_scalar`, `exists_nontrivial` (round 35; `AW4EFDatum.dual` of it is a second) | inhabited for every `q > 0`, `j` |
| `SpectralCore` | `spectralCore_of_finiteDimensional`, `Suspension.spectralCore_nonvacuous`, `spectralCore_theta`, `spectralCore_zero/two` | inhabited |
| `IsFrobPol` | `isFrobPol_assemble`, `exists_frobPol_iff` | inhabited whenever `F` is diagonalizable with eigenvalues of modulus `q^{j/2}` |
| `IsInfPol` | `isInfPol_suspForm` (from `IsFrobPol`), `isInfPol_of_aw5` | inhabited |
| `PosHermForm` | `PosHermForm.ofBasis` | inhabited |
| `LFunctionDatum` | `LFunctionDatum.riemannZeta`, `dedekindDatum`, `dirichletDatum` | inhabited |
| `DedekindContinuation K` | `DedekindContinuation.rat` | inhabited for `K = ℚ` only |
| `DedekindContinuation.SimplePoles C` | `SimplePoles.ofRat C` (`ξ = 2 completedXi`) | inhabited for every continuation over `ℚ`; general `K` needs Hecke |
| `Arakelov.HodgeDatum` (round 52; FM path) | `Xbar.hodge K` for every number field (`h_zero_zero`: `h^{0,0} = [K:ℚ] > 0`) | inhabited, by the finite `X_∞` of `X̄_K` only; no positive-dimensional instance (needs analytification and Hodge theory) |
| `Arakelov.ProjSpace.hodge` (round 53; FM path) | `ProjSpace.hodge K n` for every number field and `n` (`h_diag`: `h^{k,k} = [K:ℚ] > 0`, `k ≤ n`) | inhabited, a positive-dimensional instance of `HodgeDatum` (pieces and sign of `F_∞` modelled) |
| `Arakelov.DeligneDatum` (round 54; FM path) | `DeligneDatum.idDatum R` (`Mot = Del = R`, `reg = id`, `Hc = 0`; `idDatum_reg_ne_zero`); round 55: `degreeOne K` for `X̄_K`, `n = 1` (`degreeOne_conn_ne_zero`, `degreeOne_Hc_two : Hc 2 ≃ ℝ`) | inhabited, nonzero; genuine instance in degree one for every number field (groups modelled: `H¹ = Λ_K ⊗ ℝ`, `H¹_D = ℝ^{places}`; exactness proved) |
| `Arakelov.CompactifiedDatum` (round 56; FM §3.2) | `compactOne K` for `X̄_K`, `n = 1` (`compactOne_connBar_ne_zero`, `compactOne_Hbar_two : H² ≃ ℝ`) | inhabited, nonzero for every number field (inherits round 55's modelled groups; retraction forced to be the identity) |
| `Arakelov.CompactifiedDatum` with nontrivial retraction (round 59; FM §3.2, `n = 0`) | `TwistZero.compactZero K` (`compactZero_adj_not_surjective`, `finrank_harZero_zero = 1`) | inhabited for every number field; retraction is the zero map, not the identity |
| `Arakelov.CompactifiedDatum` at `n < 0` (round 60; FM §3.1–3.2) | `TwistNeg.compactNeg K n hn` (`compactNeg_adj_not_surjective` for even `n`; `H^0_D` of dimension `r₁ + r₂` or `r₂` by parity, `finrank_twistInv`) | inhabited for every number field and `n < 0`; all `H^*(X̄_K, ℝ(n))` vanish; truncation nontrivial for even `n` |
| `ArithChowReal.ChowR K` (round 57; FM Notation 4.13) | every number field: `chowDegreeREquiv : ChowR K ≃ₗ[ℝ] ℝ` (in particular `ChowR K` is one-dimensional, hence nonzero) | inhabited, nonzero for every number field |
| `Flow.Obj` (`def:flow-category`) | any `SpectralCore`; kernels and cokernels of morphisms (`spectralCore_ker`, `spectralCore_coker`) | inhabited |
| `DeningerStructure V d U ΘU` + `Polarizable` (`def:deninger-structure`, `def:polarizable`) | `TrivialModel.deningerStructure` (`d = 1`, unit `𝟙`), `deningerPolarization`, `polarizable`, `deningerStructure_nontrivial` | inhabited, polarizable |
| `DeningerModule` (`def:deninger-module`) | none named | definition only |
| `DeningerStructure.Morphism` (proposed `Den^natural` repair, any dimensions and units) | `Morphism.id`, `Hom.toMorphism`, `Morphism.comp` | identity and composition checked; no bundled category instance |
| `Arakelov.ArithmeticRing A` (GS 3.1.1) | `ArithmeticRing.int` (ℤ), `ArithmeticRing.ringOfIntegers K` (`𝓞 K`, any number field; round 44) | inhabited |
| `Arakelov.ArithmeticRing.Hom` (GS 3.1.3) | `Hom.id`, `int_hom` (ℤ → any arithmetic ring) | inhabited |
| `Arakelov.ArithmeticVariety R` (GS 3.2.1, first part) | `ArithmeticVariety.base R` (`Spec A`), e.g. `Spec 𝓞 K` | inhabited |
| `Arakelov.ArithmeticVariety.complexPoints V` (`X_∞`, GS 3.2.1; round 45) | for `Spec A`: `≃ S`, nonempty (`complexPointsBaseEquiv`); for `Spec 𝓞 K`: `≃ Hom(K, ℂ)` | inhabited |
| `Arakelov.KahlerInterface P F` (roadmap D2; round 45) | `KahlerInterface.zeroDim` (0-dimensional `X_∞`) | inhabited, but only by the degenerate 0-dimensional interface; no positive-dimensional instance (needs Tier B) |
| `Arakelov.ArakelovVariety R` (GS 5.1.1; round 45) | `ArakelovVariety.ofRing R` (`Spec A`), `.ringOfIntegers K`, `.int` | inhabited (dimension one only) |
| `Arakelov.KahlerDatum P F` (round 46) | `KahlerDatum.zeroDim` (0-dimensional `X_∞`) | inhabited, only by the degenerate 0-dimensional datum |
| `Arakelov.CompactifiedScheme`, category `Arakelov.Schbar` (notes `def:compactified-schemes` (a), (b); round 46) | `Xbar.obj K` (`X̄_K`) for every number field `K` | inhabited (dimension one only; no positive-dimensional Arakelov-type object yet) |
| `Schbar.proj`, `Schbar.reg` (notes (c), (d); round 46) | `Xbar.mem_proj` (`X̄_K ∈ \Schbar^proj`); `X̄_K` is regular (`Xbar.isArakelovType`) | inhabited |
| `Arakelov.NumberFieldCat` (category `𝒩`; round 47) | `ℚ` and every number field; `arith.obj` gives `X̄_K` | inhabited |
| `Arakelov.ArithChow.ChowGroup K` (`ĈH¹(Spec 𝓞_K)`, GS 3.4.3; round 48) | the class of `(0, constGreen K c)`, with `deĝ = ½ c [K : ℚ]` | nonzero for every number field (`chowDegree_surjective`) |
| `ArithmeticWeilCohomologyQ`, `…QMult` | `diagonalModel`, `multDiagonalModel` (both *from* RH) | inhabited **iff RH** (`nonempty_arithmeticWeilCohomologyQ_iff`, `…QMult_iff`): neither consistent nor inconsistent as far as Lean knows |
| `ArithmeticWeilCohomology D` | only `ArithmeticWeilCohomologyQ.toArithmeticWeilCohomology` (needs RH) | no unconditional instance |

## Build

| Item | Value |
| --- | --- |
| Toolchain | `leanprover/lean4:v4.34.1` (`lean-toolchain`) |
| Mathlib | tag `v4.34.1`, rev `d13f23b723b8a846827a245b89c10fc7d3f11612` (`lake-manifest.json`) |
| Library | `WeilRH` (default target), modules `Purity`, `RH`, `Converse`, `Negative`, `Completed`, `Multiplicities`, `Flow`, `Hermitian`, `Duality`, `AlgebraForm`, `Dedekind`, `Calibration`, `Kronecker`, `Kunneth`, `Phantom`, `Lefschetz`, `MultiplicativeForm`, `EilenbergMoore`, `Spectral`, `Jordan`, `WeilConverse`, `NLines`, `NLinesGeometry`, `FormalCurve`, `Suspension`, `SuspConverse`, `SuspObject`, `WeightedAlgebra`, `LinearGaps`, `ElementaryGaps`, `KunFq`, `KunOrbits`, `AW4Forms`, `KunTorus`, `OneBranch`, `AW5Contains`, `AW4Star`, `Hilbert`, `LocalCores`, `TrivialModel`, `Content`, `ContentAssembly`, `TrivialModelFull`, `HilbertSelfAdjoint`, `ContentGraded`, `TrivialModelGraded`, `HermAlgebra`, `Unit`, `R10`, `BsdRank`, `FlowCategory`, `Deninger`, `RelativeStructure`, `SliceNotFull`, `AlgebraFormOrdered`, `ContentXiK`, `HodgeInfty`, `HodgeProj`, `WeilArakelov`, `DeligneDegreeOne`, `CompactifiedDeligne`, `ArakelovChowReal`, `ZetaOrder`, `CompactifiedZero`, `CompactifiedNeg`, `DedekindZetaConv`, `DedekindEuler`, `DedekindLocal`, `SimplePolesCrit`, `ConverseCore`, `R1`, `R2Block`, `XiHalf`, `MainGeneral`, `XiZetaOrder`, `NoPositivityCancel`, `KunOpen`, `KunArch`, `KunSquare`, `NCount`, `BlackBoxes`, `HeckeCorollaries`, `NLinesWeil`, `XiKHadamard`, `LefschetzTrace`, `R11Pole`, `UnitProduct`, `AlgebraFormReal`, `GapStrip`, `R16`, `AW5Spectral`, `R9`, `HbHigh`, `XiKStrip`, `XiKConj`, `KunArchOrderTwo`, `KunHodgeStrict`, `R12Kernels`, `BetaP`, `EtaZeta`, `RegDet`, `RegDetSum`, `Hurwitz`, `RoucheRoute`, `BlackBoxes2`, `ZetaZerosRvM`, `KunOverZ`, `P1ZZeros`, `HbSum`, `HbEquiv`, `XiKZerosInfinite`, `WindowPoisson`, `R15Mellin`, `NKCount`, `HbNoRvM`, `R15Tail`, `R15Periodization`, `KunDiag`, `KunAW6`, `BetaIntegral`, `KunArchGal`, `SchemeZeta`, `XiKPrimeSum`, `XiKAsymp` (and the Arakelov modules listed in the claim table) |

```sh
cd lean
lake exe cache get        # Mathlib oleans
lake build                # builds WeilRH (all one hundred and thirty-six modules)
lake env lean scripts/PrintAxioms.lean   # axioms of every target
lake env lean scripts/PrintTypes.lean    # full types of every target
```

`lean/.lake/` is gitignored. Every target depends only on `propext`, `Classical.choice`,
`Quot.sound`; there is no `sorry`, `axiom`, or `native_decide` in the tree. Results that use a black box
(section "Black boxes") take it as an explicit hypothesis and are conditional on it.

## Conventions

The report's Hermitian forms are linear in the **first** argument; Mathlib's `⟪x, y⟫_ℂ` is
linear in the second. `WeilRH.hForm u v := ⟪v, u⟫_ℂ` is the report-convention form, and all
hypotheses are stated with it (`hForm_add_iff_inner`: for real `j` the identity (P) is the same
in either convention). "Positive definite Hermitian form" = a complex `InnerProductSpace`
(completeness is *not* assumed). Nontrivial zeros are transcribed verbatim from Mathlib's
`RiemannHypothesis`: `ζ ρ = 0`, `¬∃ n : ℕ, ρ = -2 * (n + 1)`, `ρ ≠ 1`.

## Claim ↔ declaration table

| Claim | Declaration(s) | File |
| --- | --- | --- |
| C-PUR (eigenvalues) | `WeilRH.re_eq_half_of_hasEigenvalue` | `WeilRH/Purity.lean` |
| C-PUR (semisimple) | `WeilRH.isSemisimple_of_additive`, `WeilRH.maxGenEigenspace_eq_eigenspace_of_additive` | `Purity` |
| C-PUR multiplicative | `WeilRH.norm_sq_eq_of_hasEigenvalue_mul`, `norm_eq_of_hasEigenvalue_mul`, `isSemisimple_of_mul`, `maxGenEigenspace_eq_eigenspace_of_mul` | `Purity` |
| C-WEIL | `WeilRH.norm_eq_rpow_of_weil`, `WeilRH.isSemisimple_of_weil` | `Purity` |
| C-RH (structure; `thm:rh`; name historical: the degree-one slice of a polarized Deninger structure satisfying AW2) | `WeilRH.ArithmeticWeilCohomologyQ`, `WeilRH.IsNontrivialZetaZero` | `WeilRH/RH.lean` |
| C-RH (theorem) | `WeilRH.ArithmeticWeilCohomologyQ.riemannHypothesis`, `WeilRH.riemannHypothesis_of_nonempty` | `RH` |
| C-RH (Prop. 1 on blocks) | `ArithmeticWeilCohomologyQ.re_eq_half_of_hasEigenvalue`, `ArithmeticWeilCohomologyQ.isSemisimple_restrict` | `RH` |
| C-GRH scaffold | `WeilRH.LFunctionDatum`, `LFunctionDatum.GRH`, `LFunctionDatum.riemannZeta`, `LFunctionDatum.grh_riemannZeta_iff`, `WeilRH.ArithmeticWeilCohomology`, `ArithmeticWeilCohomology.grh`, `WeilRH.LFunctionClass`, `WeilRH.grh_of_forall_mem`, `riemannHypothesis_of_grh_scaffold`, `ArithmeticWeilCohomologyQ.toArithmeticWeilCohomology` / `ofArithmeticWeilCohomology` | `RH` |
| C-CONV | `WeilRH.diagonalModel`, `WeilRH.nonempty_arithmeticWeilCohomologyQ_iff` | `WeilRH/Converse.lean` |
| R2 | `WeilRH.R2.counterexample` (+ `duality`, `quaternionic`, `commutes`, `H_isHermitian`, `H_sq`, `H_trace`, `P_matrix`, `P`, `h_neg`, `h_pos`, `eigen`, `lam_re_ne`) | `WeilRH/Negative.lean` |
| R3 | `WeilRH.R2.det_eq`, `p_one_sub`, `p_real_ne_zero`, `isUnit_sub_intCast` | `Negative` |
| ξ datum (AW2, §2) | `WeilRH.completedXi`, `differentiable_completedXi`, `completedXi_eq`, `completedXi_one_sub`, `completedXi_eq_zero_iff`, `analyticOrderAt_completedXi_ne_top`, `analyticOrderNatAt_completedXi_pos_iff`, `completedRiemannZeta_neg_two_mul_nat_add_one_ne_zero` | `WeilRH/Completed.lean` |
| C-RH with multiplicities (AW2 order condition; `prop:rh-positive-zero`; name historical) | `WeilRH.ArithmeticWeilCohomologyQMult`, `…QMult.riemannHypothesis`, `…QMult.hasEigenvalue_iff`, `…QMult.finrank_maxGenEigenspace`, `…QMult.toArithmeticWeilCohomologyQ`, `WeilRH.maxGenEigenspace_eq_eigenspace_of_P` | `WeilRH/Multiplicities.lean` |
| C-CONV with multiplicities | `WeilRH.multDiagonalModel`, `WeilRH.nonempty_arithmeticWeilCohomologyQMult_iff` (+ generic `WeilRH.GenDiag.*`, `finrank_eigenspace`) | `Multiplicities` |
| (P) flow form | `WeilRH.flow`, `WeilRH.P_iff_flow`, `WeilRH.P_iff_flow_of_finiteDimensional`, `WeilRH.ArithmeticWeilCohomologyQ.flow_restrict` | `WeilRH/Flow.lean` |
| R2 (`J₊`) | `WeilRH.R2.Jplus`, `Jplus_sq`, `Ω_mul_Jplus`, `commDefect_eq`, `norm_commDefect_apply`, `Jplus_not_commute` | `Negative` |
| Abstract positive forms | `WeilRH.PosHermForm`, `PosHermForm.re_eq_half`, `.isSemisimple`, `.norm_eq_rpow`, `.isSemisimple_of_weil` | `WeilRH/Hermitian.lean` |
| Q1-L4.2 (AW3+AW4 ⇒ derivation law; type `(d, w)` of the Q1 report, which the manuscript's `def:aw` now restricts to `w = 0`) | `WeilRH.WeightedStarDatum`, `.B`, `.h`, `.B_equivariant`, `.derivation_law`, `.IsPositive`, `.re_eq_of_hasEigenvalue`, `.isSemisimple`, `.re_eq_half_of_curve`, `.lineModel`, `.lineModel_isPositive` | `WeilRH/Duality.lean` |
| Q2-T1′ (algebra form AW4-E) | `WeilRH.PositiveTrace`, `.form`, `.star_mul_self_eq`, `.form_mulLeft_mulLeft`, `.norm_eq_rpow_of_mulLeft`, `.isSemisimple_mulLeft`, `.minpoly_mulLeft`, `.minpoly_squarefree`, `.norm_eq_rpow_of_isRoot_minpoly`, `.form_P_mulLeft`, `.re_eq_half_of_mulLeft`, `.isSemisimple_mulLeft_of_add_star`, `WeilRH.matrixTrace`, `matrix_norm_eq_rpow`, `matrix_isSemisimple` | `WeilRH/AlgebraForm.lean` |
| C-A (Q1 Theorem A, Dedekind class) | `WeilRH.DedekindContinuation`, `.eqOn`, `.rat`, `WeilRH.dedekindGammaFactor`, `dedekindDatum`, `dedekindDatum_isNontrivialZero_iff`, `dedekindDatum_grh_iff`, `grh_dedekind_of_awc_object`, `grh_dedekind_of_awc`, `card_ideal_rat_eq_one`, `dedekindZeta_rat`, `completedRiemannZeta_eq_zero_iff`, `dedekindDatum_rat_isNontrivialZero_iff`, `dedekindDatum_rat_grh_iff`, `riemannHypothesis_of_awc_dedekind_rat`, `riemannHypothesis_of_grh_dedekind_class` | `WeilRH/Dedekind.lean` |
| C-A (Dirichlet members of 𝒞) | `WeilRH.dirichletDatum`, `grh_dirichlet_of_awc` | `Dedekind` |
| C-B (Q2 Prop. 6.2 / Thm 6.5(4) calibration) | `WeilRH.suspEigen`, `exp_suspEigen`, `re_suspEigen`, `re_suspEigen_of_norm`, `suspPoly`, `suspension`, `suspension_apply_of_apply_eq_smul`, `iSup_eigenspace_eq_top`, `suspension_P`, `suspension_isSemisimple`, `flow_apply_of_apply_eq_smul`, `flow_suspension`, `weil_of_P_of_flow`, `suspension_P_iff_weil` | `WeilRH/Calibration.lean` |
| Q1 Cor. 5.2 (AW1–AW3 + indefinite (P) ⇏ purity) | `WeilRH.R2.counterexample` (existing; see fidelity note) | `Negative` |
| C-K6 (tensor positivity, Künneth Prop. 5 / Thm 6(ii)) | `WeilRH.pureTensor`, `star_dotProduct_kronecker_mulVec`, `posDef_iff_re`, `neg_posDef_iff_re`, `posDef_kronecker_iff`, `posDef_kronecker_self_iff` | `WeilRH/Kronecker.lean` |
| `prop:kun-tensor` (PARTIAL: AW4 positivity of `h_a ⊗ h̃_b`; AW3 block structure) | `WeilRH.posDef_kronecker_iff`, `posDef_kronecker_self_iff` (`Kronecker`); `Spectral.isInternal_block_maxGenEigenspace`, `cupTrace_eq_zero_of_mem_maxGenEigenspace` (`Spectral`, `Duality`) | `Kronecker`, `Spectral`, `Duality` |
| C-K6 (Künneth Theorem 6, Hodge index on the arithmetic surface ⟺ AW4-E) | `WeilRH.SurfaceDatum`, `.h`, `.Vρ`, `.toWeightedStarDatum`, `.derivation_law`, `.h_star_star`, `.h_eq_zero_of_pow`, `.h_eq_zero_of_mem_maxGenEigenspace`, `.h_eq_zero_of_re_ne_half` (6(i)), `.hS_block_eq_zero`, `.star_mem_iff`, `.hasEigenvalue_one_sub`, `.DefiniteOn`, `.PureDefinite`, `.HodgePure`, `.re_eq_half_of_hodgePure`, `.definiteOn_of_hodgePure`, `.hodgePure_iff_pureDefinite`, `.maxGenEigenspace_eq_eigenspace`, `.isSemisimple_of_pureDefinite`, `.gram`, `.gram_posDef_iff`, `.neg_gram_posDef_iff`, `.blockGram`, `.HodgeIndex`, `.hodgeIndex_iff_hodgePure`, `.hodgeIndex_iff_pureDefinite` (6(iii) ⟺), `.re_eq_half_of_hodgeIndex`, `.isSemisimple_of_hodgeIndex` (6(iii) ⟹), `.blockForm`, `.re_eq_half_of_definiteOn`, `.isSemisimple_restrict_of_definiteOn`, `.toWeightedStarDatum_re_eq_half`; `WeilRH.isSemisimple_of_maxGenEigenspace_eq_eigenspace` | `WeilRH/Kunneth.lean` |
| `def:aw4-EF` (AW4-E_F, sheets, interpolation polynomial) | `WeilRH.AW4EFDatum`, `WeilRH.SatisfiesAW4EF`, `WeilRH.IsSheet`, `WeilRH.progression`, `AW4EFDatum.sheetPoly`, `AW4EFDatum.sheetElem`, `WeilRH.isSheet_suspEigen`, `WeilRH.isSheet_add_int` | `WeilRH/MultiplicativeForm.lean`, `WeilRH/Phantom.lean` |
| `prop:aw4-EF`(i) | `AW4EFDatum.mul_inv`, `.inv_mul`, `.isUnit`, `.isSemisimple`, `.iSup_eigenspace_eq_top`, `.norm_eq` | `MultiplicativeForm` |
| `prop:aw4-EF`(ii) | `AW4EFDatum.ι_sheetElem_apply`, `.star_sheetElem` (+ `WeilRH.star_aeval`) | `MultiplicativeForm` |
| `prop:aw4-EF`(ii) on `V̂`, `def:aw4-EF` (c) sheet map | `AW4EFDatum.theta_sheetMap`; `Suspension.sheetMap`, `isSheet_of`, `thetaBlock_eq_of_semisimple`, `theta_lof_of_semisimple`, `theta_sheetCopy`, `genProj_apply_of_act` | `SuspObject` |
| `prop:aw4-EF`(iii) | `WeilRH.AW4EAddDatum`, `AW4EAddDatum.re_eq_half`, `.isSemisimple`, `WeilRH.PositiveTrace.pi`, `WeilRH.piRep`, `piRep_injective`, `AW4EFDatum.truncTheta`, `.truncTheta_apply`, `.truncation`, `.truncTheta_re_eq_half` | `MultiplicativeForm` |
| `prop:aw4-EF`(iii) on `V̂` | `AW4EFDatum.exists_aw4EAdd_suspension`, `AW4EFDatum.theta_sheetSum`; `Suspension.sheetSum`, `sheetSum_apply`, `sheetSum_injective`, `lof_mem_range`, `sheetMap_injective`, `sheetMap_apply`, `sheetCopy_apply`, `sheetIdx_eq_iff`, `eigOf`; `AW4EAddDatum.congr`, `AW4EAddDatum.nonempty_range` | `SuspObject` |
| `def:aw4-EF`(c) and the remark after (d) (sheet spaces, `V̂ = ⨁_m V̂_{σ_m}`) | `Suspension.sheetSpace`, `mem_sheetSpace_iff`, `vanishOn`, `sheetMap_coe`, `range_sheetMap`, `sheetEquiv`, `sheetEquiv_apply`, `shiftSheet`, `isSheet_shiftSheet`, `existsUnique_shift`, `isInternal_sheetSpace` | `SuspObject` |
| `prop:aw4-EF`(iv) | `WeilRH.PositiveTrace.op`, `AW4EFDatum.transposeRep`, `.transposeRep_injective`, `.dual` | `MultiplicativeForm` |
| `prop:rosati-EF` | `WeilRH.rosati_aw4EF` (iii), `WeilRH.rosati_gram_posDef`, `WeilRH.rosati_trace_pos` (linear-algebra core of (ii)) | `MultiplicativeForm` |
| `prop:ff-phantom` | `WeilRH.phantom`, `phantomSet`, `halfCoset`, `phantom_injOn`, `sum_phantomSet_pow_eq_zero`, `sum_phantomSet_pow_self`, `norm_of_mem_phantomSet`, `div_eq_conj_of_mem_phantomSet`, `div_mem_phantomSet` (i); `spectrum_suspension_phantom` (ii) | `WeilRH/Phantom.lean` |
| `prop:ff-phantom` (ii) on `V̂` | `Suspension.phantomF`, `Suspension.spec_theta_phantom` | `SuspObject` |
| `thm:ff-lefschetz` (finite-dimensional core) | `WeilRH.Lefschetz.sum_mul_pow_eq_zero`, `lefschetzNumber`, `altCount`, `lefschetzNumber_eq_sum`, `altCount_eq_of_lefschetzNumber_eq`, `linFactor`, `detFactor`, `zetaRat`, `zetaRat_eq_prod`, `zetaRat_eq_of_altCount_eq`, `zetaRat_eq_of_lefschetzNumber_eq` | `WeilRH/Lefschetz.lean` |
| `prop:EM` (abstract core) | `WeilRH.EM.ThickClosure`, `thickClosure_le`, `mapTriangleHom`, `isoLocus`, `isIso_app_of_mem_thickClosure`, `isIso_comp_of_mem_thickClosure` | `WeilRH/EilenbergMoore.lean` |
| `prop:EM-criterion` (abstract core) | `ThickClosure.ext₁`, `.ext₃`, `.biprod`, `.pow`, `.of_iso`, `.shift`, `.ext₂` | `EilenbergMoore` |
| `prop:B-support` | `WeilRH.Spectral.pairing_eq_zero_of_mem_maxGenEigenspace`, `pairing_eq_zero_of_pow` | `WeilRH/Spectral.lean` |
| `prop:B-support` (from AW1 + AW3) | `WeilRH.cupTrace_eq_zero_of_mem_maxGenEigenspace`, `WeilRH.WeightedStarDatum.B_eq_zero_of_mem_maxGenEigenspace` | `WeilRH/Duality.lean` |
| `prop:tensor-eigen` (first display), `def:spectral-core` (a) | `WeilRH.Spectral.tensorSum`, `block`, `pow_tmul_eq_zero`, `block_le`, `iSup_block_eq_top`, `maxGenEigenspace_tensorSum_eq` | `Spectral` |
| `prop:tensor-eigen` (direct sum, stable finite blocks, dimension formula) | `WeilRH.Spectral.iSupIndep_block`, `isInternal_block`, `isInternal_block_maxGenEigenspace`, `mapsTo_block`, `blockEquiv` (+ `FiniteDimensional` instance on `block`), `rank_maxGenEigenspace_tensorSum`; helpers `rTensor_sub_smul`, `lTensor_sub_smul`, `block_le_rTensor`, `block_le_lTensor` | `Spectral` |
| `prop:N-jordan`, `def:frob-pol` | `WeilRH.Jordan.jordanF`, `hermForm`, `norm_eq_of_hasEigenvalue`, `not_exists_polarization`, `hasEigenvalue_jordanF` | `WeilRH/Jordan.lean` |
| `def:spectral-core` (b)–(c); `prop:tensor-eigen` for spectral cores (finite dimension formula) | `WeilRH.Spectral.spec`, `SpectralCore`, `mult`, `SpectralCore.tensor_eigen`, `pairs`, `maxGenEigenspace_tensorSum_eq_pairs`, `finrank_maxGenEigenspace_tensorSum`; helpers `block_eq_bot_of_left`, `block_eq_bot_of_right` | `Spectral` |
| `prop:N-jordan` (via `prop:weil-converse` (i)) | `WeilRH.Jordan.eq_of_hasEigenvalue`, `iSup_eigenspace_ne_top`, `not_exists_frobPol` | `Jordan` |
| `prop:weil-converse` (i)–(ii), `def:frob-pol` | `WeilRH.IsFrobPol`, `IsFrobPol.eq_zero_of_ne`, `isFrobPol_iff_orthogonal` (ii), `basisForm`, `exists_frobPol_iff` (i) | `WeilRH/WeilConverse.lean` |
| `prop:weil-converse` (ii) as stated (orthogonal sums `⊕_α h_α`) | `WeilRH.assemble`, `isFrobPol_iff_exists_assemble`, `isFrobPol_assemble`, `restrict_assemble`, `eq_assemble_restrict`, `assemble_apply_of_mem`, `assemble_eq_zero_of_ne`; projections `isInternal_eigenspace`, `eigenEquiv`, `eigenProj`, `eigenProj_of_mem`, `eigenProj_of_mem_ne`, `eigenProj_eq_zero_of_not`, `eigenFinset`, `sum_eigenProj`; `PosHermForm.ext`, `.restrict`, `.sum_left`, `.sum_right` | `WeilConverse` |
| `prop:N-lines` (i)–(iii), `def:hasse-weil-zeta`(a), `def:suspension`, `eq:elliptic-zeta` | `WeilRH.NLines.qpow`, `zetaOfCounts`, `zetaOfCounts_product` (i), `zetaOfCounts_elliptic`, `zetaOfCounts_eq_zetaX`, `num`, `den`, `zetaX`, `shift1`, `num_eq_zero_iff`, `den_eq_zero_iff`, `re_of_num_eq_zero`, `re_of_den_eq_zero`, `den_ne_zero_of_num_eq_zero`, `progression_infinite`, `zeros_zetaX` (ii), `poles_zetaX` (iii) | `WeilRH/NLines.lean` |
| `prop:N-lines` (i)–(iii), geometric and analytic bridge over finite extensions | `WeilRH.NLines.zetaOfCounts_product_pos`, `zetaOfCounts_eq_zetaX` (positive-degree hypothesis); `WeilRH.NLinesGeometry.KPoints`, `pointsPullbackEquiv`, `pointCount_pullback`, `projectiveLine_card`, `pointCount_projectiveLine_of_equiv`, `countSequence`, `zetaOfCounts_product_of_geometry`, `zetaOfCounts_product_of_projectiveLine`, `finiteExtensionFamily`, `card_finiteExtensionFamily`, `zetaOfCounts_product_finiteExtensions`, `zetaOfCounts_finiteExtensions_eq_zetaX` | `WeilRH/NLines.lean`, `WeilRH/NLinesGeometry.lean` |
| `prop:N-lines`, concrete projective-line factor | `WeilRH.NLinesGeometry.projectiveLineGrading`, `projectiveLineScheme`, `projectiveLineToSpec`, `projectiveLineToSpec_isProper`, `zetaOfCounts_projectiveLineScheme_eq_zetaX` | `WeilRH/ProjectiveLineScheme.lean` |
| `def:hasse-weil-zeta` (a), `prop:N-lines` (i), formal power series | `WeilRH.NLinesFormal.logCountSeries`, `zetaSeries`, `formalExp_add`, `formalExp_rescale`, `zetaSeries_product`, `zetaSeries_product_of_geometry`, `zetaSeries_product_finiteExtensions`, `zetaSeries_projectiveLineScheme_product` | `WeilRH/NLinesFormal.lean` |
| `prop:polarization-identity` (type `(d, 0)`, weight `j`; = Q1-L4.2 at `w = 0`) | `WeilRH.WeightedStarDatum.polarization_identity` (from `.derivation_law`) | `Duality` |
| `def:suspension`, `def:log-susp` (a) | `WeilRH.Suspension.qpow`, `logSusp`, `mem_logSusp_iff` (explicit form, links `WeilRH.suspEigen`), `Idx`, `Summand`, `SuspSpace`, `restrictF`, `logNil`, `isNilpotent_logNil`, `thetaBlock`, `theta`, `suspFun`, `suspForm` | `WeilRH/Suspension.lean` |
| `prop:suspension` (i) | `mem_logSusp_iff_zero`, `hasDerivAt_one_sub`, `deriv_ne_zero`; multiplicities `mult_theta`, `mult_theta_eq`, `spec_theta`; determinant `det_one_sub_smul_eq_prod` (+ `det_one_sub_smul_eq_multiset`), zero orders `analyticOrderAt_det` (+ `analyticOrderAt_one_sub`, `analyticOrderAt_fun_prod`, `analyticAt_one_sub`) | `Suspension` |
| `prop:suspension` (ii) | `spectralCore_theta`, `mem_maxGenEigenspace_theta`, `maxGenEigenspaceThetaEquiv`, `noAccPt_idx`; generic `diag`, `mem_maxGenEigenspace_diag`, `iSup_maxGenEigenspace_diag`, `spec_diag_subset`, `mult_diag`, `spectralCore_diag` | `Suspension` |
| `def:inf-pol`, `prop:suspension` (iii) | `IsInfPol`, `isInfPol_suspForm` | `Suspension` |
| `prop:suspension` (iv) | `re_eq_of_mem_spec`, `re_eq_of_hasEigenvalue`, `iSup_eigenspace_theta` | `Suspension` |
| `def:spectral-core` nonvacuity | `spectralCore_nonvacuous` | `Suspension` |
| `def:log-susp` (b), `def:aw4-EF` (b) (sheets) | `WeilRH.Suspension.Eig`, `IsSheet`, `sheetIdx`, `sheetCopy`, `restrictedForm`; projections `isInternal_maxGenEigenspace`, `genProj`, `genProj_of_mem`, `genProj_of_mem_ne`, `maxGenEigenspace_eq_bot`, `genProj_eq_zero_of_not`, `sum_genProj`, `genProj_apply_of_smul`; `WeilRH.PosHermForm.comap` | `WeilRH/SuspConverse.lean` |
| `prop:susp-converse` | `isFrobPol_restrictedForm`; steps `thetaBlock_eq_of_infPol` (`Θ = ρ` on `V̂_ρ`, via `prop:purity`), `re_eq_of_infPol`, `eq_zero_of_logSeries_eq_zero` (log injective on unipotents), `restrictF_eq_of_logNil`, `theta_lof`, `blockForm` | `SuspConverse` |
| `prop:formal-curve` (i)–(iv), `def:formal-curve` | `WeilRH.FormalCurve.H`, `mul`, `one`, `tr`, `F₁`, `F`, `q`; (i) `F_mul`, `F_one`, `F_bijective`, `B`, `B_apply`, `B_self`, `B_antisymm`, `B_perfect`, `B_F`, `lefschetz`, `lefschetz_eq_zero`, `P₁`, `P₁_eq`, `P₁_eval`, `Z`, `Z_eq`, `P₁_funct`; (ii) `hasEigenvalue_F₁_iff`, `norm_ne_sqrt_of_hasEigenvalue`; (iii) `hermForm`, `FrobCompatible`, `frobCompatible_iff`, `shape_of_frobCompatible`, `det_ne_zero_of_frobCompatible`, `exists_pos_of_frobCompatible`, `exists_neg_of_frobCompatible`, `not_posDef_of_frobCompatible`; (iv) `alg`, `algPair`, `algPair_eq_tr_mul`, `algPair_nondegenerate`, `Falg`, `F_alg`, `algPair_F`, `hasEigenvalue_Falg_iff`, `iSup_eigenspace_Falg` | `WeilRH/FormalCurve.lean` |
| `prop:weighted-algebra-obstruction` | `WeilRH.WeightedAlgebraDatum`, `.h`, `.Θr`, `.polarization` (weight-`w + j` identity), `.form`, `.form_P`, `.re_eq_of_hasEigenvalue`, `.iSup_eigenspace`, `.hasEigenvalue_of_mem`, `.mul_eigen_eq_zero`, `.mul_eq_zero`, `.eq_bot`, `.eq_zero_of_unit`; `WeilRH.PosHermForm.maxGenEigenspace_eq_eigenspace` | `WeilRH/WeightedAlgebra.lean` |
| `prop:R5` (Serre) | `WeilRH.LinearGaps.isEmpty_antihom`; `not_anticomm` | `WeilRH/LinearGaps.lean` |
| `prop:bsd-positive-gap` | `WeilRH.LinearGaps.bsd_positive_gap` | `LinearGaps` |
| `prop:bsd-jordan-gap` | `WeilRH.LinearGaps.jordanJ`, `charpoly_jordanJ`, `rootMultiplicity_charpoly_jordan`, `ker_jordan_sub_one`, `finrank_ker_jordan_sub_one` | `LinearGaps` |
| `prop:R2-star` (i)–(ii) | existing `WeilRH.R2.Jplus_sq`, `Ω_mul_Jplus`, `commDefect_eq`, `Jplus_not_commute` (row "R2 (`J₊`)") | `Negative` |
| `prop:R2-star` (iii) | `WeilRH.R2.starForm`, `starForm_P`, `not_exists_posStar` | `Negative` |
| `prop:bsd-coefficient-gap` | `WeilRH.ElementaryGaps.bsd_coefficient_gap`, `lattice_gap` | `WeilRH/ElementaryGaps.lean` |
| `prop:bsd-primary-gap` | `WeilRH.ElementaryGaps.G`, `primaryComponent_finite`, `G_infinite` | `ElementaryGaps` |
| `prop:R11` (i)–(ii) (`def:R11-quartet`) | `WeilRH.R11.quartet`, `quartetC`, `root`, `quartetC_eq`, `coeff_quartetC_im`, `eval_quartetC_neg`, `eval_quartetC_eq_zero_iff`, `root_im_ne_zero`, `neg_logDeriv_eq`, `im_neg_logDeriv_pos` | `ElementaryGaps` |
| `prop:R11` (iii) | `WeilRH.R11.im_neg_logDeriv_value`, `.norm_hb_lt`; helpers `.norm_add_I_mul_lt`, `.ne_root_value` | `ElementaryGaps` |
| `prop:kun-Fq-C` (K-N5) | `WeilRH.KunFq.maxGenEigenspace_eq_bot_or_infinite`; core `.maxGenEigenspace_eq_bot_or_infinite_of_shift`; helpers `.shift`, `.qpow_add_shift`, `.qpow_sub_shift`, `.shift_injective`, `.block_ne_bot`, `.mem_spec_theta_add_shift`, `.mem_spec_theta_sub_shift` | `WeilRH/KunFq.lean` |
| `def:unit` (b) via `prop:unit` | `WeilRH.KunOrbits.unitSpace`, `.unitTheta`, `.mem_spec_unit_iff`, `.mult_unit`; helpers `.hasEigenvalue_one_iff`, `.qpow_eq_one_iff`, `.shift_eq`, `.mem_spec_shift` | `WeilRH/KunOrbits.lean` |
| `def:unit` (a)–(c); `𝟙` as tensor unit (round 38) | `WeilRH.Unit.arith`, `.twist`, `.arith_mul`, `.tensorSum_arith`, `.tensorSum_twist`, `.spectralCore_tensor_arith_iff`, `.spectralCore_arith`, `.spec_arith`, `.mult_arith`; `𝟙_q`: `.Periodic`, `.periodicTheta`, `.periodicTheta_single`, `.single_mul_single`, `.periodicTheta_mul`, `.spectralCore_periodic`, `.periodic_nontrivial` | `WeilRH/Unit.lean` |
| `prop:unit` (spectrum `(2πi/log q)ℤ`, simple; not isomorphic to `𝟙`; round 38) | `WeilRH.Unit.mem_spec_periodic`, `.mult_periodic`, `.not_equiv_arith` | `WeilRH/Unit.lean` |
| `prop:algebra-form` (i) over `k = ℂ` (= Q2-T1′, rounds 3 and 39) | `WeilRH.PositiveTrace.minpoly_squarefree`, `.norm_eq_rpow_of_isRoot_minpoly` | `WeilRH/AlgebraForm.lean` |
| `prop:algebra-form` (ii) over `k = ℂ` (round 39) | `WeilRH.PositiveTrace.rep_isSemisimple`, `.rep_norm_eq_rpow`, `.rep_iSup_eigenspace` | `WeilRH/AlgebraForm.lean` |
| `prop:algebra-form` (i) over `k ∈ {ℚ, ℝ}`, separability (round 41) | `WeilRH.PositiveTraceOrd`, `.symForm`, `.symForm_self_pos`, `.dag_mul_self_eq`, `.symForm_mulLeft`, `.minpoly_separable`; `WeilRH.isSemisimple_of_similitude` | `WeilRH/AlgebraFormOrdered.lean` |
| `prop:R10` (i)–(iii) (round 39) | `WeilRH.R10.exists_unitary`, `.diag_spectral`, `.not_exists_intertwiner`; helpers `.eigSub`, `.mem_eigSub`, `.map_eigSub`, `.finrank_eigSub_eq`, `.eigSub_op_eq_span`, `.finrank_eigSub_op`, `.finite_eq_of_tendsto`, `.not_accPt_of_tendsto` | `WeilRH/R10.lean` |
| `prop:bsd-spectral-rank` (round 39) | `WeilRH.BsdRank.bsd_spectral_rank`; helpers `.ker_sub_one_eq_top`, `.finrank_ker_eq` | `WeilRH/BsdRank.lean` |
| `prop:bsd-picard-gap`, algebraic part (round 39) | `WeilRH.BsdRank.splitEquiv`, `.picard_gap`; helpers `.retract`, `.retract_comp_subtype`, `.baseChange_subtype_injective` | `WeilRH/BsdRank.lean` |
| `prop:kun-orbits` (i) (K-N6) | `WeilRH.KunOrbits.kun_orbits_same` | `KunOrbits` |
| `prop:kun-orbits` (ii) | `WeilRH.KunOrbits.kun_orbits_dense`; helpers `.int_mul_log_eq`, `.shift_add_shift_injective`, `.pairs_unit` | `KunOrbits` |
| `def:kurokawa-cone` | `WeilRH.KunOrbits.kurokawaCone`, `.mapsTo_kurokawaCone` | `KunOrbits` |
| `prop:kun-orbits` (iii) | `WeilRH.KunOrbits.kun_orbits_cone`; generic `.finrank_cone_inf`, `.finrank_maxGenEigenspace_restrict`, `.biSup_inf_biSup_of_isInternal`, `.finrank_biSup_block`; helpers `.card_cone`, `.cone_pairs`, `.shift_add`, `.im_shift` | `KunOrbits` |
| `def:aw4-forms` (a)–(b) (one degree, weight `j`) | `WeilRH.AW4Forms.AW4V`, `WeilRH.AW4Forms.AW4E` | `WeilRH/AW4Forms.lean` |
| `prop:aw4-forms` (i) | `WeilRH.AW4Forms.maxGenEigenspace_eq_eigenspace`, `.re_eq_half`, `.aw4V_of_aw4E`; helpers `.iSup_eigenspace_eq_top`, `WeilRH.PosHermForm.ofBasis`, `.coordSum`, `.coordSum_eq_of_subset`, `.ofBasis_apply_basis` | `AW4Forms` |
| `prop:aw4-forms` (ii) (on a spectral core) | `WeilRH.AW4Forms.aw4E_of_aw4V`, `.nonempty_aw4EAddDatum`; helpers `WeilRH.AW4Forms.HSpace` (+ `.core`, `.innerProductSpace`), `WeilRH.PosHermForm.re_nonneg` | `AW4Forms` |
| `prop:aw4-forms` (iii) (degree `j`, on a spectral core) | `WeilRH.AW4Star.exists_star`, `.exists_weightedStarDatum`; `.blockPairing` (AW3 perfectness), helpers `.hFun`, `.toFun_eq_zero_of_ne` | `WeilRH/AW4Star.lean` |
| `prop:kun-torus` (i) | `WeilRH.KunTorus.eq_zero_of_flow_eq_self`; `.Torus`, `.flow`, `.flow_eq_self_iff` | `WeilRH/KunTorus.lean` |
| `prop:kun-torus` (ii) | `WeilRH.KunTorus.exists_flow_eq_self`, `.not_isolated` | `KunTorus` |
| `prop:kun-torus` (iii) | `WeilRH.KunTorus.log_div_log_mem_rat_iff` | `KunTorus` |
| `prop:one-branch` (without the `detreg` clause) | `WeilRH.OneBranch.one_branch`; `.spec_scalar`, `.mult_scalar`, `.maxGen_scalar_eq_bot`, `.maxGen_scalar_self` | `WeilRH/OneBranch.lean` |
| `prop:hilbert` (PARTIAL: basis, `Θ = j/2 + iT`, symmetry) | `WeilRH.Hilbert.Completion`, `.exists_hilbertBasis`, `.inner_eq_zero_of_ne`, `.T`, `.theta_eq`, `.T_apply_of_eq`, `.T_symm` | `WeilRH/Hilbert.lean` |
| `def:diag-op`, `prop:hilbert` (self-adjointness) | `WeilRH.Hilbert.Diag.op`, `.domain`, `.coef`, `.repr_op`, `.inner_op`, `.op_symm`, `.basis_mem_domain`, `.op_basis`, `.dense_domain`, `.isSelfAdjoint`; `WeilRH.Hilbert.incl`, `.inner_incl`, `.exists_selfAdjoint` | `WeilRH/HilbertSelfAdjoint.lean` |
| `prop:hilbert` (spectral clause: pure point spectrum `{τ_k}`, finite multiplicities, no finite accumulation; round 37) | `WeilRH.Hilbert.Diag.op_eq_smul_iff`, `.mem_span_of_op_eq_smul`, `.existsUnique_sub_smul_eq`, `.spectral_clause`; `WeilRH.Hilbert.fin_disc_of_basis`, `.exists_spectral` | `WeilRH/HilbertSelfAdjoint.lean` |
| `prop:aw5-contains` (i) | `WeilRH.AW5Contains.isInfPol_of_aw5`; `.AW5Local`, `.LocFin`, `.gen`, `.inner_gen_add`, `.defect_eq_zero` | `WeilRH/AW5Contains.lean` |
| `prop:aw5-contains` (ii) | `WeilRH.AW5Contains.aw5_pure`, `.locFin_of_spectralCore` | `AW5Contains` |
| `prop:R14` (i)–(ii) | `WeilRH.R14.compact_and_eigenvalue`, `WeilRH.R14.shift` | `ElementaryGaps` |
| `def:R14-sources` (`c_f`), `prop:R14` (iii)–(iv) | `WeilRH.R14.corr`, `support_subset_Ioo`, `corr_eq_zero`, `corr_pos` (iii); `corr_log_eq_zero`, `exists_corr_log_pos` (iv) | `ElementaryGaps` |
| `prop:weighted-algebra-obstruction` (nonvacuity, `w = 0`) | `WeilRH.WeightedAlgebraDatum.trivialModel`, `.trivialModel_nontrivial`; `WeilRH.Spectral.spectralCore_of_finiteDimensional` | `WeightedAlgebra` |
| `prop:R2-frob` (Q2 N1) | `WeilRH.R2.frob_counterexample`; `.frobDiag`, `.F`, `.F_transpose_mul_Ω`, `.F_mul_S`, `.norm_frobDiag`, `.hasEigenvalue_F`, `.eq_frobDiag_of_hasEigenvalue`, `.conj_cpow_real`, `.cpow_mul_one_sub` | `Negative` |
| `prop:R17` (i) | `WeilRH.R17.reflect`, `.integral_reflect_mul_deriv_eq_zero` | `ElementaryGaps` |
| `def:bump`, `prop:R17` (ii) | `WeilRH.R17.bump`, `.bump_eq`, `.bump_spec` | `ElementaryGaps` |
| `prop:kun-cone` (ii) (PARTIAL: generic spectral core, (i) not formalized) | `WeilRH.KunOrbits.kurokawaCone_inf_antidiag`, `.finiteDimensional_kurokawaCone_inf_antidiag` | `KunOrbits` |
| `def:R7-local` | `WeilRH.R7.VQ`, `WeilRH.R7.thetaQ` | `WeilRH/LocalCores.lean` |
| `prop:R7` (i) | `WeilRH.R7.spec_local`, `.shift_eq_shift_iff` (each `V_p`); `.mem_spec_thetaQ`, `.re_eq_zero_of_mem_spec`, `.rank_maxGenEigenspace_zero`, `.mult_zero`, `.mult_eq_one` (`V_𝒬`); generic `⨁ T_i` helpers `.mem_maxGenEigenspace_diag_iff`, `.spec_diag`, `.maxGenEquiv`, `.rank_maxGenEigenspace_diag`, `.maxGenEquivSingle` | `LocalCores` |
| `prop:R7` (ii) | `WeilRH.R7.not_spectralCore` | `LocalCores` |
| `prop:R7` (iii) | `WeilRH.R7.completedXi_ne_zero_of_re_eq_zero`, `.completedXi_ne_zero_of_mem_spec`, `.completedXi_ne_zero_of_mem_specQ` | `LocalCores` |
| `prop:R7` (iv) | `WeilRH.R7.summable_iff`; helpers `.norm_cpow_neg`, `.one_sub_ne_zero`, `.norm_term` | `LocalCores` |
| `def:trivial-model` (degree-one slice) | `WeilRH.TrivialModel.model`; `.lam`, `.swap`, `.sgn`, `.V1`, `.theta`, `.B`, `.B_e_f`, `.starLine`, `.star1`, `.conjV`, `.swapSign` | `WeilRH/TrivialModel.lean` |
| `prop:trivial-model` (i) | `WeilRH.TrivialModel.B_theta`, `.model_cup_derivation` (AW1, bidegree `(1, 1)`), `.model_tr_equivariant`, `.B_nondegenerate` (AW3), `.rank_maxGenEigenspace_theta`, `.spec_theta` (`Sp_1 = Σ`), `.spectralCore_theta` — PARTIAL (degree-one slice) | `TrivialModel` |
| `prop:trivial-model` (ii) | `WeilRH.TrivialModel.model_isPositive`, `.h_eq_sum`, `.theta_starLine` (star law), `.star_star`, `.model_star_star` (`*_1² = -1`) — PARTIAL (degree-one slice) | `TrivialModel` |
| `prop:trivial-model` (iii) | `WeilRH.TrivialModel.exists_datum_iff` | `TrivialModel` |
| `def:trivial-model` (degrees `0`, `2`, full product) | `WeilRH.TrivialModel.model0`, `.model2`, `.conjL`, `.Tot`, `.mul`, `.one`, `.thetaTot` | `WeilRH/TrivialModelFull.lean` |
| `prop:trivial-model` (i), degrees `0`, `2` and the product | `WeilRH.TrivialModel.mul_assoc'` (associativity), `.mul_comm_graded`, `.mul_anticomm_one`, `.B_antisymm` (graded commutativity), `.one_mul'`, `.mul_one'` (unit), `.thetaTot_mul` (derivation), `.spectralCore_zero`, `.spectralCore_two`, `.blockPairing_bijective` (AW3 perfectness on `V^1_σ × V^1_{1-σ}`), `.blockPairing_zero_bijective` (AW3 on `V^0 × V^2`), `.lam_eq_of_mem`, `.lof_mem` | `TrivialModelFull` |
| `def:trivial-model` as one graded datum; AW1 `V^0 ≅ 𝟙`, `V^2 ≅ 𝟙(-1)` | `WeilRH.TrivialModel.gradedModel` (`WeightedAlgebraDatum (Tot ι) 1 0`), `.mulL`, `.thetaL`, `.G`, `.st`, `.trT`, `.deg0Equiv`, `.deg0Equiv_unit`, `.deg2Equiv`, `.deg2Equiv_twist`, `.gradedModel_nontrivial` — finite `ι`; for any divisor with finite multiplicities and no finite accumulation point: `.gradedModelOf`, `.gradedModelInf`, `.gradedModelInf_nontrivial`, `.deg1Equiv`, `.spectralCore_G1` (round 36), via `WeilRH.Spectral.SpectralCore.of_equiv`, `.map_maxGenEigenspace_of_equiv` | `WeilRH/TrivialModelGraded.lean` |
| `prop:content` (iii) as one graded datum (indefinite) | `WeilRH.HermAlgebraDatum`, `.h`, `.polarization`, `WeilRH.WeightedAlgebraDatum.toHerm`, `WeilRH.PairingModel.gradedDatum`, `.gradedDatum_h_one`, `.spectralCore_G1`, `WeilRH.ContentAssembly.gradedDatum`, `.gradedDatum_indef`; any divisor with finite multiplicities and no finite accumulation (round 37): `.gradedDatumInf`, `.gradedDatumInf_indef` | `WeilRH/HermAlgebra.lean` |
| `prop:content` (iii) degree one, spectral-core condition for block data (round 37) | `WeilRH.PairingModel.spec_theta`, `.spectralCore_theta` | `WeilRH/ContentAssembly.lean` |
| Remark after `prop:weighted-algebra-obstruction` (trace weight vs star shift; the unit) | `WeilRH.form_identity_sub`, `WeilRH.derivation_unit_eq_zero`, `WeilRH.trace_weight_eq_shift_of_unit` | `HermAlgebra` |
| `def:aw4-EF` (a), a concrete datum | `WeilRH.AW4EFDatum.scalarModel`, `.satisfiesAW4EF_scalar`, `.exists_nontrivial`, `.rpow_half_mul_star` | `MultiplicativeForm` |
| `prop:trivial-model` (ii), degrees `0`, `2` | `WeilRH.TrivialModel.model0_isPositive`, `.model2_isPositive` (`h_0`, `h_2` positive; star laws are the fields `star_comm` of `model0`, `model2`) | `TrivialModelFull` |
| `prop:content` (ii) | `WeilRH.Content.exists_stdForm`, `.re_eq_half_of_isInfPol`, `.model_h_of_not`, `.stdBasis`, `.hasEigenvalue_theta` | `WeilRH/Content.lean` |
| `prop:content` (iii) | `WeilRH.Content.pairDatum` (real-pair block), `.pair_h`, `.pair_conj_symm`, `.pair_nondegenerate`, `.pair_infPol`, `.pair_h_pos`, `.pair_h_neg`, `.pair_hasEigenvalue`; quartet block `WeilRH.R2.*`; `.not_isPositive_of_re_ne` | `Content`, `Negative` |
| `prop:content` (iii), assembly | `WeilRH.ContentAssembly.content_indef`, `.D`, `.data`, `.lamX`, `.R2_Ω`, `.R2_S`, `.R2_Θ`, `.π_π`, `.conj_g`; generic block `WeilRH.PairingModel.Data`, `.datum`, `.B_theta`, `.B_nondegenerate`, `.theta_star`, `.h_eq_sum`, `.h_lof_lof`, `.h_conj_symm`, `.h_nondegenerate`, `.h_pair`, `.rank_maxGenEigenspace_theta` — degree-one slice | `WeilRH/ContentAssembly.lean` |
| `prop:content` (iii), degrees `0`, `2` | `WeilRH.ContentAssembly.content_indef_graded`, `.sgn_swp`; `WeilRH.PairingModel.B_lof_lof`, `.B_antisymm`, `.Tot`, `.mul`, `.one`, `.mul_assoc'`, `.mul_comm_graded`, `.one_mul'`, `.mul_one'`, `.thetaTot`, `.thetaTot_mul`; degree slices `TrivialModel.model0`, `.model2` | `WeilRH/ContentGraded.lean` |
| `def:flow-category` | `WeilRH.Flow.Obj`, `.Hom`, `.instCategoryObj` | `WeilRH/FlowCategory.lean` |
| `prop:flow-exact` (a) | `WeilRH.Flow.map_maxGenEigenspace_le`, `.maxGenEigenspace_inf_range`, `.exact_maxGenEigenspace`, `.kerΘ`, `.cokerΘ`, `.spectralCore_ker`, `.spectralCore_coker`, `.exists_fd_stable`, `.iSup_maxGenEigenspace_of_fd_stable` | `FlowCategory` |
| `prop:flow-exact` (b) | `WeilRH.Flow.alternating_finrank_eq_zero`, `.alternating_mult_eq_zero` | `FlowCategory` |
| `def:deninger-structure` | `WeilRH.DeningerStructure`, `.nondeg_right`, `.Hom`, `.Hom.id`, `.Hom.comp` | `WeilRH/Deninger.lean` |
| `def:polarizable` | `WeilRH.DeningerStructure.Polarization`, `.Polarizable` | `Deninger` |
| `def:polarizable` ⇒ `def:graded-realization` (b) (via `prop:polarization-identity`) | `WeilRH.DeningerStructure.Polarization.toWeightedAlgebraDatum`, `.infPol`, `.re_eq_of_hasEigenvalue`, `.iSup_eigenspace`; `WeilRH.WeightedAlgebraDatum.eigen_of_mem`, `.nondeg` | `Deninger` |
| `def:deninger-module` | `WeilRH.DeningerModule`, `.Hom` | `Deninger` |
| `def:deninger-structure` (b), cross-component morphisms (`Den^natural` repair) | `WeilRH.DeningerStructure.Morphism`, `.Morphism.id`, `.Morphism.comp`, `.Morphism.comp_id`, `.Morphism.id_comp`, `.Morphism.comp_assoc`, `.Morphism.map_eq_zero_of_gt`, `.Hom.toMorphism` | `WeilRH/RelativeStructure.lean` |
| `prop:relative-structure` (round 40) | `WeilRH.DeningerStructure.Morphism.act`, `.act_one`, `.act_act`, `.act_mem`, `.act_add_left`, `.act_add_right`, `.act_mul_left`, `.act_mul_right`, `.Θ_act` | `RelativeStructure` |
| GS 1990 Def. 3.1.1, arithmetic ring (Arakelov A1; round 44) | `WeilRH.Arakelov.ArithmeticRing`, `.delta`, `.delta_injective`, `.F_const` | `WeilRH/ArithmeticRing.lean` |
| GS 1990 3.1.2 (1), (2): ℤ and `𝓞 K` (round 44) | `ArithmeticRing.int`, `.ringOfIntegers`, `.embeddings`, `.mem_embeddings`, `.ringOfIntegers_hom_injective`, `.exists_extend`, `.conjEmb`, `.card_ringOfIntegers_S` | `ArithmeticRing` |
| GS 1990 3.1.3, homomorphisms; ℤ initial (round 44) | `ArithmeticRing.Hom`, `.Hom.id`, `.Hom.f_injective`, `.int_hom`, `.int_hom_unique` | `ArithmeticRing` |
| GS 1990 Def. 3.2.1, arithmetic variety, first part (round 44; `def:arakelov-pair` prerequisite) | `WeilRH.Arakelov.ArithmeticVariety`, `.base`, `genericPoint` | `WeilRH/ArithmeticVariety.lean` |
| GS 1990 Def. 3.1.1: `F_∞` is forced, `S` closed under conjugation (round 45) | `ArithmeticRing.exists_eval`, `.conj_mem`, `.conjS`, `.conjS_conjS`, `.F_apply` | `WeilRH/ComplexPoints.lean` |
| GS 1990 Def. 3.2.1, `X_∞ = X_S(ℂ)` with `F_∞` (round 45; Arakelov A2) | `ArithmeticVariety.complexPoints`, `.Finf`, `.Finf_Finf`, `.complexPointsBaseEquiv`, `.complexPointsBaseEquiv_Finf`, `.embeddingsEquiv`, `.complexPointsSpecEquiv`, `.complexPointsSpecEquiv_Finf` | `ComplexPoints` |
| GS 1990 Def. 3.2.1, topology on `X_∞` for `Spec 𝓞_K` (2026-11-13; zero-dimensional case) | `ArithmeticVariety.embeddingsTopology`, `.embeddingsTopology_discrete`, `.complexPointsSpecTopology`, `.complexPointsSpecTopology_discrete`, `.complexPointsSpecHomeomorph`, `.complexPointsSpec_Finf_continuous` | `ComplexPointsTopology` |
| notes `X̄_K(ℂ)` topology (2026-11-13; pointwise evaluation model) | `Xbar.pointsTopology`, `.pointsTopology_discrete`, `.pointsHomeomorph`, `.Finf_continuous` | `ComplexPointsTopology` |
| GS 1990 5.1.1, Arakelov variety; notes `def:arakelov-pair` (round 45; Arakelov A3, interface) | `WeilRH.Arakelov.ArakelovVariety`, `IsRegularScheme`, `isRegularScheme_spec`, `KahlerInterface`, `KahlerInterface.zeroDim`, `ArakelovVariety.ofRing`, `.ringOfIntegers`, `.int` | `WeilRH/ArakelovVariety.lean` |
| notes `def:compactified-schemes` (a), (b), (c), (d): compactified schemes and the category `\Schbar` (round 46; Arakelov A4) | `WeilRH.Arakelov.points`, `Finf`, `Finf_Finf`, `mapPoints`, `mapPoints_Finf`, `KahlerDatum`, `IsArakelovType`, `CompactifiedScheme`, `Schbar`, `Schbar.forget_faithful`, `Schbar.forgetFullyFaithful`, `Schbar.infty`, `Schbar.infty_Finf`, `Schbar.reg`, `Schbar.proj`, `isEmpty_points_of_finite`, `Schbar.isEmpty_points_of_smProj` | `WeilRH/CompactifiedScheme.lean` |
| notes `def:compactified-schemes` (e) object `X̄_K`, `def:arakelov-pair`; orbits of `F_∞` and infinite places (round 46; Arakelov D1) | `Xbar.obj`, `Xbar.isArakelovType`, `Xbar.mem_proj`, `Xbar.pointsEquiv`, `Xbar.pointsEquiv_Finf`, `Xbar.place`, `Xbar.place_surjective`, `Xbar.place_eq_place_iff`, `Xbar.isReal_place_iff`, `Xbar.card_fiber_place`, `Xbar.card_points` | `CompactifiedScheme` |
| notes `prop:A1-number-fields` and the remark after it: morphisms `X̄_L → X̄_K` are field embeddings (round 47; Arakelov D2) | `NumberFieldCurves.ringHom_injective`, `ringHomEquiv`, `specHomEquiv`, `homEquiv`, `endEquiv`, `ofRingHom`, `homEquiv_ofRingHom`, `ofRingHom_id`, `ofRingHom_comp` | `WeilRH/NumberFieldCurves.lean` |
| notes `prop:A1-number-fields`: `𝒩ᵒᵖ` ≃ connected objects (round 47; on the essential image of `K ↦ X̄_K`) | `NumberFieldCat`, `NumberFieldCat.arith`, `arith_fullyFaithful`, `arithEquiv` | `NumberFieldCurves` |
| GS 1990 §3.4.3: `ĈH¹(Spec 𝓞_K)` and the arithmetic degree (round 48; Arakelov C1) | `ArithChow.greenSpace`, `principal`, `ChowGroup`, `degree`, `prod_norm_embeddings`, `deg_principal`, `chowDegree`, `deg_const`, `chowDegree_surjective` | `WeilRH/ArithmeticChow.lean` |
| GS 1990 §3.4.3: the exact sequence `𝓞_K^* → (⊕ ℝ)^{F_∞} → ĈH¹ → Cl(𝓞_K) → 0` and `ĈH¹(Spec ℤ) ≅ ℝ` (round 49; Arakelov C1) | `ArithChow.toClass`, `toClass_surjective`, `ofGreen`, `toClass_eq_zero_iff`, `ofGreen_eq_zero_iff`, `toPrincipalIdeal_eq_one_iff`, `chowDegree_injective_rat`, `chowDegreeEquivRat` | `WeilRH/ArithmeticChow.lean` |
| notes `def:zeta`, `prop:xiK` (part; round 49; Arakelov D3, given Hecke's continuation) | `xiK`, `xiK_one_sub`, `xiK_eqOn`, `xiK_rat`, `xiK_eq_zero_iff_rat` | `WeilRH/XiK.lean` |
| notes `prop:xiK` (entire part, `ξ_K(0)ξ_K(1) ≠ 0`, zeros; round 50; Arakelov D3, given Hecke's continuation and simple poles) | `DedekindContinuation.SimplePoles`, `SimplePoles.one_sub`, `xi_one`, `xi_one_ne_zero`, `xi_zero_ne_zero`, `xi_eq_zero_iff`, `ofRat` | `WeilRH/XiK.lean` |
| FM 2020 p. 520–521 (1): `ζ(X̄_K, s) = e^{a+bs} Λ_K(s)`, same divisor (round 50; Arakelov D4) | `GammaRFM`, `GammaCFM`, `GammaRFM_mul_add_one`, `zetaInftyFM_eq`, `zetaFM`, `zetaFM_eq`, `exp_fmA_add_rat`, `zetaFMCont_eq_zero_iff`, `analyticOrderAt_xiFM` | `WeilRH/ArakelovZeta.lean` |
| notes `prop:content` (i) (degree one, `Σ_K = div ξ_K`; round 51; Arakelov D5, given simple poles) | `content_free`, `xiFamily`, `SymEntire.card_fiber`, `SymEntire.spectralCore`, `SymEntire.mult_one_sub`, `SymEntire.even_mult_half` | `WeilRH/ContentXiK.lean` |
| notes `prop:content` (iv) (degree one; round 51; Arakelov D5) | `content_iff` | `WeilRH/ContentXiK.lean` |
| FM 2020 pp. 520–521: Hodge numbers `h^{p,q}`, `h^{p,±}`, formula (1) `L_∞(h^i,s)`, `ζ(X_∞,s)` (round 52; FM path E1, E2 in degree 0) | `HodgeDatum`, `.h_symm`, `.hplus_add_hminus`, `.LInfty`, `.zetaInfty`, `involution_finrank_add` | `WeilRH/HodgeInfty.lean` |
| FM p. 521 for `X̄_K`: `h^{0,+} = r₁ + r₂`, `h^{0,−} = r₂`, `ζ(X_∞,s)` (round 52) | `Xbar.hodge`, `Xbar.finrank_invariants`, `Xbar.finrank_antiinvariants`, `Xbar.zetaInfty_hodge`, `Xbar.pointsPullback_Finf` | `WeilRH/HodgeInfty.lean` |
| FM pp. 520–521 for `ℙⁿ_{𝓞_K}`: Hodge numbers, `L_∞(h^{2k},s) = Γ_ℝ(s−k)^{r₁}Γ_ℂ(s−k)^{r₂}`, `ζ(X_∞,s)` (round 53; FM path E2) | `ProjSpace.hodge`, `.h_diag`, `.h_offdiag`, `.hplus_eq`, `.hminus_eq`, `.LInfty_eq`, `.LInfty_two_mul`, `.zetaInfty_eq`, `.zetaInfty_zero` | `WeilRH/HodgeProj.lean` |
| FM p. 520 for `ℙⁿ_{𝓞_K}`: `ζ(ℙ̄ⁿ,s) = ∏_k e^{a+b(s−k)}Λ_K(s−k)` (round 53; `ζ(ℙⁿ_{𝓞_K},s)` definitional) | `ProjSpace.zetaPn`, `.zetaFMPn`, `.zetaFMPn_eq_prod`, `.zetaFM_eq` | `WeilRH/HodgeProj.lean` |
| FM §3.1 (p. 523): fibre triangle `RΓ_c → RΓ → RΓ_D →` as a long exact sequence; FM §3.3 (2) and §3.4 (3)–(5) (p. 524) on cohomology (round 54; FM path E3) | `DeligneDatum`, `.idDatum`, `WeilArakelov.Har`, `.theta`, `.theta_comp`, `.ker_theta_succ`, `.kerThetaEquiv`, `.cokerThetaEquiv` | `WeilRH/WeilArakelov.lean` |
| Dirichlet regulator of `X̄_K` in degree one (`n = 1`, FM §3.1 regulator, before `⊗ℝ`) (round 54) | `regulatorMap`, `sum_regulatorMap`, `regulatorMap_eq_zero_iff` | `WeilRH/WeilArakelov.lean` |
| Degree-one regulator `⊗ ℝ` of `X̄_K`: injective, image the sum-zero hyperplane (Dirichlet) (round 55; FM §3.1) | `unitsR`, `logR`, `logR_eq_equiv`, `logR_bijective`, `hyperplane`, `range_hyperplane`, `sumMap_surjective`, `regR`, `regR_tmul`, `regR_injective`, `range_regR` | `WeilRH/DeligneDegreeOne.lean` |
| Degree-one Deligne datum of `X̄_K` (`n = 1`): `H¹_c = 0`, `H²_c = ℝ` (round 55; FM §3.1, p. 523) | `degSub`, `degMap`, `degreeOne`, `degreeOne_Hc_two`, `degreeOne_Del_one_nontrivial`, `degreeOne_conn_ne_zero` | `WeilRH/DeligneDegreeOne.lean` |
| Cohomology of the Arakelov compactification (FM §3.2, interface) and its `X̄_K` instance, `n = 1`: `H¹(X̄_K, ℝ(1)) = 0`, `H²(X̄_K, ℝ(1)) ≅ ℝ` (round 56) | `CompactifiedDatum`, `degSub_subsingleton`, `compactOne`, `compactOne_ret`, `compactOne_Hbar_one`, `compactOne_Hbar_two`, `compactOne_connBar_ne_zero` | `WeilRH/CompactifiedDeligne.lean` |
| Weil–Arakelov cohomology of `X̄_K`, `n = 1` (FM (2)): zero outside degrees 2, 3 and one-dimensional there, the shape of FM Prop. 4.14 (i); non-compactified contrast in degrees 1, 2 (round 56) | `hBar`, `harBar`, `harBar_subsingleton`, `finrank_hBar_two`, `finrank_hBar_of_ne`, `finrank_harBar_two`, `finrank_harBar_three`, `prop414_shape`, `finrank_unitsR`, `hOpen`, `harOpen`, `finrank_hOpen_one`, `finrank_hOpen_of_ne`, `finrank_harOpen_one`, `finrank_harOpen_two` | `WeilRH/CompactifiedDeligne.lean` |
| FM Prop. 4.14 (iii) for `X̄_K`, `n = 1`: `ord_{s=1} ζ(X̄_K, s) = -1 = -dim ĈH¹(X̄_K)_ℝ = -dim H²(X̄_K, ℝ(1))`, and `ord_{s=0} = -1` (round 58) | `zetaFMCont_eq`, `g1`, `g0`, `analyticAt_g1`, `analyticAt_g0`, `g1_one_ne_zero`, `g0_zero_ne_zero`, `eventually_eq_one`, `eventually_eq_zero`, `meromorphicAt_model`, `meromorphicOrderAt_zetaFMCont_one`, `meromorphicOrderAt_zetaFMCont_zero`, `finrank_chowR`, `fm414_iii` | `WeilRH/ZetaOrder.lean` |
| `X̄_K` at twist `n = 0` (FM §3.1–3.2): nontrivial truncation, `H^i(X̄_K, ℝ(0))`, Weil–Arakelov groups in degrees `0, 1`, and FM Prop. 4.14 (i), (iii) at `n = 0` (round 59) | `TwistZero.diag`, `diag_injective`, `zeroDatum`, `finrank_Hc_one`, `compactZero`, `compactZero_ret`, `compactZero_adj_not_surjective`, `finrank_hBar0_zero`, `finrank_hBar0_of_ne`, `harZero_subsingleton`, `finrank_harZero_zero`, `finrank_harZero_one`, `prop414_zero_shape`, `fm414_zero` | `WeilRH/CompactifiedZero.lean` |
| `X̄_K` at twists `n < 0` (FM §3.1–3.2): `H^0_D` with the parity of `n`, `H^1_c`, all `H^*(X̄_K, ℝ(n))` and `H^*_ar` zero, `ord_{s=n} ζ(X̄_K, s) = 0`, FM Prop. 4.14 (i), (iii) at `n < 0` (round 60) | `TwistNeg.sgn`, `conjR`, `eig`, `twistInv`, `finrank_eig_add`, `placePullbackR`, `range_placePullbackR`, `finrank_eig_one`, `finrank_eig_neg_one`, `finrank_twistInv`, `negDatum`, `finrank_negDatum_Hc_one`, `compactNeg`, `compactNeg_ret`, `compactNeg_adj_not_surjective`, `harNeg_subsingleton`, `finrank_harNeg`, `fm414_neg`, `fm414_neg_rat`; `ZetaOrder.NonvanishingRight`, `gx`, `meromorphicOrderAt_zetaFMCont_of_ne`, `meromorphicOrderAt_zetaFMCont_neg`, `nonvanishingRight_rat` | `WeilRH/CompactifiedNeg.lean` |
| Convergence of `ζ_K` on `Re s > 1`, real positivity, `ξ_K(x) ≠ 0` for real `x > 1`, reduction of `NonvanishingRight` to `ζ_K ≠ 0` (round 61; Euler-product groundwork) | `DedekindZetaConv.coeff`, `coeff_one`, `dedekindZeta_eq`, `tendsto_sum_coeff_div`, `sum_coeff_isBigO`, `LSeriesSummable_coeff`, `abscissaOfAbsConv_coeff_le`, `dedekindZeta_pos`, `dedekindZeta_ne_zero_of_real`, `Gammaℂ_ne_zero_of_re_pos`, `dedekindGammaFactor_ne_zero`, `xi_ne_zero_of_dedekindZeta_ne_zero`, `nonvanishingRight_of_dedekindZeta_ne_zero`, `xi_ne_zero_of_real` | `WeilRH/DedekindZetaConv.lean` |
| Multiplicativity of `a_K(n) = #{I : N I = n}`; Euler product of `ζ_K` over rational primes on `Re s > 1`; reduction of `ζ_K ≠ 0` and `NonvanishingRight` to the local factors (round 62) | `DedekindEuler.splitEquiv`, `sup_mul_sup_eq`, `mul_sup_eq`, `absNorm_sup_eq`, `coeff_zero`, `coeff_mul`, `summand_mul`, `dedekindZeta_eulerProduct_hasProd`, `dedekindZeta_eulerProduct_tprod`, `localFactor_eq`, `summable_norm_localTail`, `dedekindZeta_ne_zero_of_localFactor_ne_zero`, `nonvanishingRight_of_localFactor_ne_zero` | `WeilRH/DedekindEuler.lean` |
| Local Euler factor `∑_e a_K(p^e) p^{-es} = ∏_{𝔭∣p} (1 - N𝔭^{-s})⁻¹`; `ζ_K(s) ≠ 0` on `Re s > 1` unconditionally; `NonvanishingRight` for every `K`; FM Prop. 4.14 at `n < 0` from `SimplePoles` alone (round 63) | `DedekindLocal.piProdP_all`, `primesAbove`, `mem_primesAbove`, `two_le_absNorm`, `absNorm_eq_pow`, `idealOf`, `idealOf_injective`, `absNorm_idealOf`, `exists_idealOf`, `toSigma_bijective`, `wt`, `norm_wt_lt_one`, `localFactor_eq_prod`, `localFactor_ne_zero`, `dedekindZeta_ne_zero`, `nonvanishingRight`, `fm414_neg'` | `WeilRH/DedekindLocal.lean` |
| `SimplePoles` ⟺ `(s - 1) Λ_K(s)` bounded near `1`, for any continuation (round 64; Hecke itself is a Mathlib gap) | `DedekindContinuation.BoundedAtOne`, `differentiableOn_xiK`, `simplePolesOfBoundedAtOne`, `boundedAtOne_of_simplePoles`, `boundedAtOne_rat`, `nonempty_simplePoles_iff` | `WeilRH/SimplePolesCrit.lean` |
| `ĈH¹(Spec 𝒪_K)_ℝ ≅ ℝ` via the arithmetic degree, and `H²(X̄_K, ℝ(1)) ≅ ĈH¹(X̄_K)_ℝ` (FM Notation 4.13; the `n = 1` case of FM [13, Prop. 2.11] as used on FM p. 535) (round 57) | `greenR`, `DivR`, `arithDivR`, `inc`, `relR`, `ChowR`, `logNormR`, `halfSumR`, `degreeR`, `degreeR_inc`, `chowDegreeR`, `toChowR`, `chowDegreeR_comp`, `chowDegreeR_surjective`, `exists_green_of_div`, `unit_green_mem`, `greenR_eq_embedding`, `sum_greenR`, `greenOfUnitsR`, `greenOfUnitsR_tmul`, `greenOfUnitsR_mem`, `mem_relR_of_halfSumR_eq_zero`, `ker_degreeR`, `chowDegreeR_injective`, `chowDegreeREquiv`, `chowRToH2`, `compactOne_Hbar_two_chowRToH2` | `WeilRH/ArakelovChowReal.lean` |
| `prop:slice-not-full` (round 40) | `WeilRH.SliceNotFull.faithful`, `.over_endo_eq_id`, `.specAut`, `.specAut_injective`, `.exists_of_iso`, `.not_full`; helpers `.eq_of_restrict_eq`, `.specAut_refl` | `WeilRH/SliceNotFull.lean` |
| `def:deninger-structure`, non-vacuity | `WeilRH.TrivialModel.deningerStructure`, `.deningerPolarization`, `.polarizable`, `.deningerStructure_nontrivial` | `Deninger` |
| `def:deninger-theory` (core and full, axioms F1–F4), `def:compactified-schemes`, `prop:finite-field-calibration`, `prop:calibration-cancel` | not formalized: Mathlib has no Arakelov-compactified schemes, and a functor on an abstract source would reintroduce the retired zeta setting; objectwise F2 is AW2, formalized above | — |
| `prop:converse` (round 65; C-CONV on `def:spectral-core`, `def:inf-pol`) | `WeilRH.PositiveZetaCore`, `.riemannHypothesis`, `positiveZetaCore`, `riemannHypothesis_iff_nonempty_positiveZetaCore`; `ArithmeticWeilCohomologyQMult.spectralCore`, `.map_maxGenEigenspace_restrict_le`, `not_accPt_zeros_completedXi`, `PosHermForm.ofInner` | `WeilRH/ConverseCore.lean` |
| `def:R1-forms`, `prop:R1` (i)–(ii) (round 65) | `WeilRH.R1.thetaDual`, `.hDual`, `.thetaSplit`, `.hSplit`, `.IsHermNondeg`, `.InfPol`, `.dual`, `.dual_off_line`, `.split`; helpers `.hDual_isHermNondeg`, `.hSplit_isHermNondeg`, `.infPol_dual`, `.infPol_split`, `.hasEigenvalue_dual`, `.mem_ker_split_iff` | `WeilRH/R1.lean` |
| `prop:R2` (i) (round 65, restated round 71; PARTIAL: AW3 perfectness, associativity and graded commutativity are not fields of `HermAlgebraDatum`) | `WeilRH.R2.gradedBlock`, `.gradedBlock_h_zero`, `.gradedBlock_h_two`, `.gradedBlock_h_pos`, `.axioms`, `.eb`, `.eb_mem`, `.eq_sum_eb`, `.theta_eb`, `.pairing_eb`, `.star_eb`, `.axioms_block`; existing `ContentAssembly.R2_Θ`, `R2_Ω`, `R2_S`, `R2.quaternionic`, `R2.duality`, `R2.commutes` | `WeilRH/R2Block.lean` |
| `prop:R2` (ii) (round 65) | `WeilRH.R2.form`, `.signature`, `.sigBasis`; existing `R2.H_eq`, `H_isHermitian`, `H_sq`, `h_neg` | `WeilRH/R2Block.lean` |
| `prop:R2` (iii) (round 65) | `WeilRH.R2.re_of_eigen`, `.re_ne_half_of_eigen`; existing `R2.eigen`, `lam_re_ne` | `WeilRH/R2Block.lean` |
| `prop:R3` (i)–(ii) (round 65; = old R3 completed) | `WeilRH.R2.cone_acyclic`, `.poly`, `.p_eq_mul`, `.p_real_pos`, `.pPoly`, `.eval_pPoly`, `.natDegree_pPoly`; existing `R2.det_eq`, `p_one_sub`, `isUnit_sub_intCast` | `WeilRH/R2Block.lean` |
| `def:regdet` (a), (b), (d) and the *superseded* (c) (any preconnected continuation domain), with the finite-spectrum remark after it (round 73; relabelled round 78). The revised (c) and (d) are `IsZetaRegularizable` and `canonicalDetreg` (round 77, row below) | `WeilRH.RegDet.SpectralCut`, `SpectralCut.pow`, `zetaTerm`, `specZeta`, `ConvergesAt`, `Regularization`, `detreg`, `Regularization.D_unique`, `finZeta`, `finDet`, `Regularization.ofFinite`, `detreg_finite` | `WeilRH/RegDet.lean` |
| `prop:R3` (iii) (round 73; PARTIAL: that `(V' ⊕ V, Θ' ⊕ Θ)` is a spectral core with spectrum `S' ∪ spec Θ` is not stated. Round 78, revised `def:regdet`: `det_sum_onHalfPlane` takes a half-plane regularization and returns one, so by `detreg_eq_of_onHalfPlane` the identity is about *the* determinant for the combined cut extending `c'`; `det_sum` (old (c)) is kept) | `WeilRH.RegDet.combCut`, `combCut_L_of_mem`, `U₀_subset`, `addMult`, `specZeta_comb`, `converges_comb`, `Regularization.addFinite`, `detreg_addFinite`; `WeilRH.R2.eigs`, `eigs_card`, `finDet_eigs`, `det_sum`, `det_sum_onHalfPlane` | `WeilRH/RegDetSum.lean` |
| `def:zeta` (d), `prop:F0` (round 65, conditional on `ζ(1/2) < 0`; **unconditional since round 73**: `F_zero_pos`) | `WeilRH.riemannXiUpper`, `riemannXiUpper_zero`, `gammaRHalf`, `gammaRHalf_pos`, `Gammaℝ_half`, `riemannZeta_half_im`, `completedXi_half`, `completedXi_half_pos_iff`, `F_zero_pos_of_zeta_half_neg`; `WeilRH.EtaZeta.term`, `eta`, `norm_term_le`, `summable_norm_term`, `differentiableOn_eta`, `eta_eq_of_one_lt`, `region`, `isPreconnected_region`, `eta_eq_on_region`, `eta_ofReal_pos`, `riemannZeta_neg_of_mem_Ioo`, `riemannZeta_half_re_neg`, `WeilRH.F_zero_pos` | `WeilRH/XiHalf.lean`, `WeilRH/EtaZeta.lean` |
| `prop:rouche-route` (round 73), with Hurwitz's theorem | `WeilRH.Hurwitz.exists_zero`, `im_eq_zero_of_tendsto`; `WeilRH.Gap.differentiable_hat`, `hat_smul`; `WeilRH.riemannXiUpper_neg`, `riemannXiUpper_eq_zero_mem_strip`, `strip`, `rouche_route` | `WeilRH/Hurwitz.lean`, `WeilRH/RoucheRoute.lean` |
| `thm:main-general` (round 66; C-PUR, Q1-L4.2) | `WeilRH.MainGeneral.GradedRealization`, `Polarization`, `iSup_eigenspace`, `re_eq_of_hasEigenvalue`, `mult_eq_finrank_eigenspace`, `mult_eq_zero`, `divisor_eq_of_line`, `divisor_eq_zero_of_off`, `meromorphicOrderAt_eq_divisor`, `meromorphicOrderAt_eq_of_line`, `meromorphicOrderAt_eq_zero_of_off`, `exists_odd_of_divisor_pos`, `exists_even_of_divisor_neg`, `mult_eq_of_line`; also the C-PUR and Q1-L4.2 rows | `WeilRH/MainGeneral.lean`, `Purity`, `Duality` |
| `thm:A-schemes` (i) (relabel, round 65) | Q1-L4.2 rows at `w = 0` (`WeightedStarDatum.derivation_law`, `.re_eq_of_hasEigenvalue`, `.isSemisimple`) | `Duality` |
| `thm:A-schemes` (ii)–(iii) (round 66) | `WeilRH.MainGeneral.ofWeightedAlgebraDatum`, `ofWeightedAlgebraDatum.polarization`, `aschemes_ord`, `aschemes_ord_off`, `aschemes_zero`, `aschemes_pole`, `aschemes_mult`, `ofDeninger` | `WeilRH/MainGeneral.lean` |
| `thm:main-number-fields`, first sentence (round 66; **conditional** on `DedekindContinuation K` + `SimplePoles`; unconditional for `ℚ`) | `WeilRH.MainGeneral.meromorphicOn_Λ`, `analyticAt_Λ`, `exists_meromorphicOrderAt_Λ_ne_top`, `divisor_Λ_pos`, `re_eq_half_of_xi_eq_zero`, `riemannHypothesis_of_realization` | `WeilRH/MainGeneral.lean` |
| `prop:converse`, `ζ`-multiplicities (round 66) | `WeilRH.ne_zero_of_isNontrivialZetaZero`, `Gammaℝ_ne_zero_of_isNontrivialZetaZero`, `riemannZeta_eq_mul_completedXi`, `analyticOrderAt_riemannZeta_eq_completedXi`, `analyticOrderNatAt_riemannZeta_eq_completedXi`, `analyticOrderNatAt_completedXi_eq`, `PositiveZetaCore.mult_eq_zeta` | `WeilRH/XiZetaOrder.lean` |
| `prop:no-positivity-cancel`, existence of `η` (round 66; the adjunction is obligation 25) | `WeilRH.DeningerStructure.Θ_one`, `Θ_top`, `one_ne_zero`, `exists_eta` | `WeilRH/NoPositivityCancel.lean` |
| `prop:kun-open` (round 67) | `WeilRH.KunOpen.KunSeq`, `KunSeq.altDiv_eq`, `KunSeq.altDiv_eq_of_same`, `KunSeq.mult_E0_of_injective`, `KunSeq.mult_E0_of_zero`; helpers `mapsTo_maxGenEigenspace`, `exists_mem_maxGenEigenspace_of_map_eq`, `res`, `res_injective`, `res_surjective`, `range_res_eq_ker_res`, `euler_eight` | `WeilRH/KunOpen.lean` |
| `prop:kun-arch` (round 67; hypotheses `χ c ≠ 1`, `c² = 1` discharged in round 71 for every group of order two and at `Multiplicative (ZMod 2)`; `Gal(ℚ(i)/ℚ)` itself instantiated in round 79, `KunArchGal.lean`) | `WeilRH.KunArch.kun_arch_gal`, `kun_arch_gal_divisors` (round 81: the group-theoretic clauses together with both pole divisors), `card_gal`, `chi`, `chi_ne_one`, `galEquiv`, `LInftyChar_sq'`, `orderTwo_hyp`, `orderTwo`, `signChar`, `zmod2`, `LInftyChar`, `LInftyChar_of_ne_one`, `LInftyChar_sq`, `inv_Gammaℝ_eq`, `inv_Gammaℝ_eq_prod`, `analyticOrderAt_inv_Gammaℝ_add`, `analyticOrderAt_inv_Gammaℝ_add_eq_zero`, `meromorphicOrderAt_Gammaℝ_add`, `meromorphicOrderAt_Gammaℝ`, `meromorphicOrderAt_Gammaℝ_add_one`, `D₁`, `conv`, `conv_D₁_neg_two_sub`, `conv_D₁_eq_zero` | `WeilRH/KunArch.lean` |
| `thm:kun-square` (iv), (iii) last step (round 67; **conditional on part (i)**: the injective intertwining `κ : V ⊗ W → H` is a hypothesis; abstract spectral cores, surface datum not modelled; the consequence "no surface datum is a Weil datum of type (2, 0)" is not formalized) | `WeilRH.KunSquare.not_finite_of_pairs_infinite`, `not_finite_of_pairs_infinite_of_inj`, `not_spectralCore_of_inter_infinite`, `not_spectralCore_self`, `add_mem_spec`, `exists_accPt_of_infinite_bounded` | `WeilRH/KunSquare.lean` |
| `prop:N-count` (i) (round 67; for `ξ_K` **conditional** on `SimplePoles`; conjugation clause for `ξ_K` added round 71) | `WeilRH.NCount.xi_conj`, `WeilRH.XiKConj.xi_conj`, `analyticOrderNatAt_xi_conj`, `WeilRH.analyticOrderAt_conj`, `WeilRH.NCount.added`, `lam_added_injective`, `family'`, `rank_maxGenEigenspace`, `spectralCore`, `mult_one_sub`, `mult_conj`, `card_added_count`, `card_count`, `NCount.xi` | `WeilRH/NCount.lean` |
| `thm:A` (i) (relabel, round 65; **conditional** on `DedekindContinuation K`) | C-A rows (`grh_dedekind_of_awc`, `riemannHypothesis_of_awc_dedekind_rat`); (ii)–(iii) not formalized; (iv) only for `K = ℚ` (`ArithmeticWeilCohomologyQMult.finrank_maxGenEigenspace`) | `Dedekind`, `Multiplicities` |
| `thm:B` (relabel, round 65): linear core only | C-B rows (`suspension_P_iff_weil` and helpers): the suspension of an abstract `(E, F)` with a Weil form; no `ℓ`-adic cohomology, no AW-det | `Calibration` |
| B1–B4 statements and bridges (round 68; black boxes, see "Black boxes") | `WeilRH.HeckePackage`, `.continuation`, `.simplePoles`, `.growth`, `WeilRH.WeilConjectures`, `WeilRH.HadamardOrderOne`, `WeilRH.StirlingBox` | `WeilRH/BlackBoxes.lean` |
| B3', B4', B6 statements and the bridge B3' ⇒ B3 (round 74) | `WeilRH.HadamardOrderOneLU`, `WeilRH.hadamardOrderOne_of_LU`, `WeilRH.LogGammaStirling`, `WeilRH.RiemannVonMangoldt`, `WeilRH.RvM.nontrivialZeros`, `RvM.zeroCount`, `RvM.mainTerm` | `WeilRH/BlackBoxes2.lean` |
| `def:regdet`: independence of the regularization (round 74; under a common-domain condition) and, for the revised (c) (half-plane continuation, round 77), the paragraph after the definition: `det_reg` depends only on the cut | `WeilRH.RegDet.detreg_eq_of_common_domain`, `detreg_eq_of_dom_eq`; `Regularization.OnHalfPlane`, `IsZetaRegularizable`, `detreg_eq_of_onHalfPlane`, `canonicalDetreg`, `detreg_eq_canonical`, `Regularization.ofFinite_onHalfPlane`, `isZetaRegularizable_finite`, `Regularization.addFinite_onHalfPlane` | `WeilRH/RegDet.lean` |
| Zeros of `ζ` from Riemann–von Mangoldt (round 74; CONDITIONAL on B6) | `WeilRH.RvM.tendsto_mainTerm_sub`, `tendsto_zeroCount`, `nontrivialZeros_eq_of_no_zero`, `exists_zero_im_gt`, `nontrivialZeros_infinite`, `exists_nontrivial_zero` | `WeilRH/ZetaZerosRvM.lean` |
| `prop:kun-over-Z` (round 74; CONDITIONAL on B6; tensor square encoded as `V¹ × V¹` with `Θ ⊕ Θ`; the encoding builds in two proof steps instead of deriving them: `V⁰ = ℂ`, `Θ₀ = 0`, and `Sp₁ = div ξ` with multiplicity (the `finrank_eigenspace` field), round 77) | `WeilRH.KunOverZ.finrank_eigenspace_eq_zero`, `kun_over_Z` | `WeilRH/KunOverZ.lean` |
| `prop:P1Z`, zero clauses (round 74; for `ζ(s)ζ(s-1)`, product formula open; nonemptiness and vertical-line clause CONDITIONAL on B6) | `WeilRH.P1ZZeros.zetaP1`, `re_mem_Ioo`, `not_trivial_of_re_pos`, `zetaP1_eq_zero_iff`, `re_mem_Ioo_add_one`, `nonempty`, `no_vertical_line` | `WeilRH/P1ZZeros.lean` |
| `prop:xiK` for every `K : Type` (round 68, completed round 71; **conditional** on B1) | `WeilRH.Hecke.xi`, `WeilRH.Hecke.xiK`, `Hecke.xiK_strip`, `Hecke.xiK_order` | `WeilRH/HeckeCorollaries.lean`, `WeilRH/XiKStrip.lean` |
| `prop:xiK`, strip and order clauses, given `C`, `P` (round 71) | `WeilRH.XiKStrip.xi_ne_zero_of_one_lt_re`, `xi_ne_zero_of_re_neg`, `re_mem_Icc_of_xi_eq_zero`, `gammaFactorInv`, `differentiable_gammaFactorInv`, `gammaFactorInv_ne_zero`, `zetaCont`, `zetaCont_eq`, `differentiableOn_zetaCont`, `analyticOrderAt_zetaCont_eq`, `xi_eq_zero_of_zetaCont_eq_zero` | `WeilRH/XiKStrip.lean` |
| `prop:content` (i), (iv), `prop:N-count` (i), `thm:main-number-fields` (first sentence), `thm:A` (i) for every `K : Type` (round 68; **conditional** on B1) | `WeilRH.Hecke.content_free`, `content_iff`, `nCount`, `nCount_conj`, `xi_conj`, `re_eq_half_of_realization`, `grh_of_awc` | `WeilRH/HeckeCorollaries.lean` |
| FM `ζ(X̄_K, s) = e^{a+bs}Λ_K(s)`, `ζ(ℙ̄ⁿ_{𝓞_K})`, FM Prop. 4.14 at `n = 1, 0, < 0` for every `K : Type` (round 68; **conditional** on B1) | `WeilRH.Hecke.zetaFM_eq`, `zetaFM_proj_eq`, `fm414_one`, `fm414_zero`, `fm414_neg` | `WeilRH/HeckeCorollaries.lean` |
| `thm:imp-stirling` (ii)–(iii) for `ξ_K`: Hadamard product (round 68; **conditional** on B1 + B3) | `WeilRH.Hecke.ZeroIdx`, `zero`, `growth_three_halves`, `fiberEquiv`, `xi_hadamard` | `WeilRH/XiKHadamard.lean` |
| `prop:N-lines` (ii)–(iii), multiset form; curve count from B2' (round 68; geometric part **conditional** on B2', not kernel-checked; `#A₁ = 2` and the manuscript's two-term `zetaX` for `E` are **not** derived, and no elliptic curve is instantiated as `X`: Mathlib has no scheme-level elliptic curve) | `WeilRH.NLines.numM`, `zetaXM`, `zetaXM_pair`, `numM_eq_zero_iff`, `re_of_numM_eq_zero`, `den_ne_zero_of_numM_eq_zero`, `zetaXM_zeros_poles`, `zetaOfCounts_curve`, `zetaOfCounts_eq_zetaXM`; `WeilRH.NLinesGeometry.kPointsEquivOver`, `curve_count`, `nLines_of_weil` | `WeilRH/NLinesWeil.lean` |
| Remark after `prop:formal-curve` (no curve has all `N_n = 0`; round 68; **conditional** on B2') | `WeilRH.NLinesGeometry.exists_count_ne_zero` | `WeilRH/NLinesWeil.lean` |
| `thm:ff-lefschetz`, linear step `Tr(F^k) = ∑ α^k` (round 69) | `WeilRH.LefschetzTrace.trace_pow_eq_sum_roots`, `lefschetzNumber_eq_sum_trace`; helpers `isNilpotent_pow_sub_pow`, `trace_restrict_pow` | `WeilRH/LefschetzTrace.lean` |
| `prop:R11` (iv) (round 69) | `WeilRH.R11.im_neg_logDeriv_lt_zero` | `WeilRH/R11Pole.lean` |
| `prop:unit`, first clause (round 69; from `(ℂ, 1)`, `thm:imp-weil-coh` input not formalized) | `WeilRH.UnitProduct.suspMul`, `unitElt`, `equiv`, `equiv_mul`, `equiv_unit`, `equiv_theta`; helpers `addIdx`, `zeroIdx`, `summand_eq_top`, `coord`, `mulComp`, `suspMul_lof`, `idxInt`, `idxEquiv`, `coord_lof`, `equiv_lof`, `logNil_one` | `WeilRH/UnitProduct.lean` |
| `prop:algebra-form` (i) moduli and (ii) over `k ∈ {ℚ, ℝ}` (round 69) | `WeilRH.PositiveTraceOrd.norm_eq_rpow_of_isRoot`, `rep_isSemisimple`, `rep_norm_eq_rpow`, `rep_iSup_eigenspace`; helpers `symForm_isSymm`, `algebraMap_complex`, `matrix_similitude`, `aeval_map_ring`; `WeilRH.nonvacuous_rat`, `nonvacuous_real` | `WeilRH/AlgebraFormReal.lean` |
| `def:residual-gap`, `prop:gap` (round 70) | `WeilRH.Gap.gap_l2`, `gap`; helpers `orth_invariant`, `mul_norm_le`, `μI`, `L2I`, `hat`, `C`, `kernel`, `kernel_memLp`, `hat_eq_inner`, `hat_sub`, `norm_kernel_sq`, `norm_kernel_le`, `norm_kernel_eq`, `norm_hat_le` | `WeilRH/GapStrip.lean` |
| `def:Fminus`, `def:R16-examples`, `prop:R16` (i)–(iii) (round 70) | `WeilRH.R16.norm_A_k`, `norm_k_sub_proj`, `f_even`, `norm_f`, `Fminus_f`, `tendsto_Fminus_f`, `isGreatest_Fminus`, `tendsto_norm_x`, `norm_A_x`; defs `A`, `k`, `e0`, `Fminus`, `f`, `H`, `e`, `Aop`, `x`; helpers `proj_k`, `norm_x` | `WeilRH/R16.lean` |
| `prop:aw5-contains` (iii), diagonal model (round 70; generator of `U_j` not modelled; multiplicity clause round 74) | `WeilRH.AW5Spectral.aw5_spectral`, `aw5_spectral_mult`; helpers `incl_eq_zero`, `card_eq_finrank_eigenspace` | `WeilRH/AW5Spectral.lean` |
| `prop:R9` (i)–(ii); (iii) for bounded `A` (round 70) | `WeilRH.R9.deriv_reflect`, `reflect_companion`, `order_add_smul_deriv`, `order_companion`, `order_reflect_companion`, `G`, `example_E`, `example_Esharp`, `example_order`, `ker_le_span` | `WeilRH/R9.lean` |
| `prop:hb-high`, first clause (round 70) | `WeilRH.riemannXiUpper_ne_zero` | `WeilRH/HbHigh.lean` |
| `prop:hb-high`, second clause (round 75; CONDITIONAL on B1 for `ℚ`, B3', B6; from round 77 on B1 for `ℚ` and B3' only, `riemannXiUpper_im_neg_logDeriv_pos'` in `HbNoRvM.lean`); `eq:hb-product`, series for `𝔪` in symmetric form | `WeilRH.riemannXiUpper_im_neg_logDeriv_pos`; general: `WeilRH.HbSum.hasSum_neg_logDeriv`, `im_neg_logDeriv_pos`; helpers `logDeriv_eq`, `logDeriv_neg`, `im_one_div_pos`, `ZIdx`, `ZIdx.pt`, `ZIdx.fiberEquiv`, `ZIdx.exists_iff`, `ZIdx.card_fiber`, `log_norm_le_global`, `growth_comp`; `WeilRH.HeckePackage.xi_rat`, `riemannXiUpper_growth`, `differentiable_riemannXiUpper`, `riemannXiUpper_zero_ne`, `riemannXiUpper_exists_zero` | `WeilRH/HbSum.lean` |
| `prop:hb` (i)–(iv), `def:hb` (a)–(c), `eq:hb-modulus` (round 75; (i) ⇒ (ii) CONDITIONAL on B1 for `ℚ`, B3', B6, and from round 77 on B1 for `ℚ` and B3' only (`Hb.hb_tfae'`); the other implications unconditional; "`𝔪` holomorphic on `ℂ⁺`" encoded as `F ≠ 0` on `ℂ⁺`) | `WeilRH.Hb.hb_tfae'`, `Hb.hb_tfae_of_zero`, `Hb.hb_tfae`; `Hb.E`, `Hb.Esharp`, `Hb.Esharp_eq`, `Hb.normSq_add_sub`, `Hb.normSq_E_sub`, `Hb.completedXi_conj`, `Hb.riemannXiUpper_conj`, `Hb.deriv_riemannXiUpper_conj` | `WeilRH/HbEquiv.lean` |
| `ξ_K` has infinitely many zeros, with multiplicity (input of `thm:kun-square` (`item:ks-mult`) and `prop:kun-AW6`; round 75; CONDITIONAL on B1, B3) | `WeilRH.Hecke.zeroIdx_infinite`; helpers `one_le_re_dedekindZeta`, `one_le_nrPlaces`, `cfac`, `cfac_le_norm_Gammaℝ`, `cfac_le_norm_Gammaℂ`, `cfac_le_norm_xi`, `norm_xi_le_of_finite`, `eventually_pow_lt_factorial` | `WeilRH/XiKZerosInfinite.lean` |
| `def:window-objects` (a), (b), `thm:window` (i) (round 76; complex-valued `φ`; `C_L` parametrized by `n ∈ ℤ`) | `WeilRH.WindowPoisson.window_poisson`; defs `transform`, `cosetPt`, `aux`; helpers `cosetPt_injective`, `contDiff_aux`, `hasCompactSupport_aux`, `fourier_aux`, `aux_int` | `WeilRH/WindowPoisson.lean` |
| `def:ccm-kernel` (`k₀`, `M_{k₀}`), `prop:R15` (i) (round 76; (ii), (iii): rows below, round 78) | `WeilRH.R15Mellin.hasMellin_k0`; defs `k0`, `gauss`, `e0`; helpers `hasMellin_e0`, `hasMellin_expPi`, `hasMellin_gauss`, `k0_eq` | `WeilRH/R15Mellin.lean` |
| `def:ccm-kernel` (`𝓔k₀`), `prop:R15` (ii) (round 78): for `Re s > 1`, `∫₀^∞ 𝓔k₀(u) u^{s−1/2} du/u` converges absolutely and equals `ζ(s) M_{k₀}(s) = ξ(s)/4` | `WeilRH.R15Periodization.R15_ii`, `hasMellin_sum`, `zeta_mul_M`, `integrand_eq`; defs `M`, `Ek0`, `F`; helpers `hasMellin_scaled`, `integral_norm_F`, `summable_integral_norm` | `WeilRH/R15Periodization.lean` |
| `def:ccm-kernel` (`k_{0,λ}`), `prop:R15` (iii) (round 78) | `WeilRH.R15Tail.tail`; def `k0trunc`; helpers `k0_zero`, `k0_pos`, `abs_k0_le`, `summable_k0`, `summable_k0trunc`, `k0_sub_trunc` | `WeilRH/R15Tail.lean` |
| `def:tensor-diag` (counting function) and `prop:kun-diag` (iii)–(v) (round 78; PARTIAL: on diagonal entries only; (i) and (ii), self-adjointness and compact resolvent as operator properties, are not modelled; "compact resolvent" in (iii) is read as finiteness of every counting function) | `WeilRH.KunDiag.Nsum_le`, `Nsum_finite`, `zero_infinite`, `sharp_one`, `sharp_two`; defs `N`, `Nsum`, `τA`, `τA'`, `τB`, `τB'`; helper `pairs_subset` | `WeilRH/KunDiag.lean` |
| `prop:kun-AW6` (round 78; CONDITIONAL on B1, B3, and on the hypotheses `hτ` (each `ξ_K(1/2 + iτ_i) = 0`) and `hsurj` (every zero of `ξ_K` is some `1/2 + iτ_i`). These two hypotheses stand for the manuscript's AW1–AW4 for the Weil datum together with `thm:rh` and `prop:hilbert`; together they imply GRH for `ξ_K`, so the theorem applies only where GRH(K) holds, exactly as the manuscript's hypothesis does. `T₁ ⊞ T₁` is represented by its diagonal entries as in `KunDiag`; round 80 wording fix from `fidelity-78.md`) | `WeilRH.KunAW6.kun_AW6`, `zeroSet_infinite` | `WeilRH/KunAW6.lean` |
| `N_K(T) = O(T log T)` (sentence after `thm:imp-stirling`; round 76; CONDITIONAL on B1; `N_K(T+1) − N_K(T) = O(log T)` not formalized) | `WeilRH.NKCount.zeroCount_le`; def `zeroCount`; helpers `analyticOnNhd_xi`, `xi_two_ne_zero`, `analyticOrderAt_ne_top`, `divisor_eq`, `divisor_nonneg`, `mem_closedBall_two`, `zeroCount_le_divisor_sum`; finiteness of the counted set (round 78): `zeroSet_finite`, `zeroCount_eq_sum`, `analyticOrderNatAt_pos`, `zeroCount_pos` | `WeilRH/NKCount.lean` |
| R12 | `WeilRH.R12.cos_add_cosh_eq_zero_plus`, `cos_add_cosh_eq_zero_minus`, `zero_not_real`, `WeilRH.R12.fourier_eq` | `Negative` |
| `def:split-datum` (degree one), `prop:kun-hodge-strict` (round 72; every real `γ`; degree-one slice only: AW1 for `U = 𝟙`, unit products and degrees 0, 2 not modelled) | `WeilRH.KunHodgeStrict.splitDatum`, `ρ_add_conj`, `one_sub_ρ`, `Θ_bv`, `e_mem`, `f_mem`, `h_bv`, `not_definiteOn`, `pure_pos_of_posDef`, `not_posDef_blockGram`, `not_hodgeIndex`, `h₀`, `isInfPol_h₀`, `aw4V_splitDatum`, `aw4E_splitDatum`, `kun_hodge_strict` | `WeilRH/KunHodgeStrict.lean` |
| `prop:R12` (i)–(ii) (round 72, with the round-1 R12 row for `μ_a` and the two zeros `π ± ia`) | `WeilRH.R12Kernels.muHat`, `muHat_eq`, `muHat_eq_zero_iff`, `hasDerivAt_muHat`, `deriv_ne_zero`, `im_ne_zero`, `g`, `k`, `k_pos`, `contDiff_k`, `integrable_k`, `fourier_g`, `fourier_k`, `fourier_k_eq_zero_iff` | `WeilRH/R12Kernels.lean` |
| `prop:beta`, the `P` clauses (round 72; superseded in round 79: together with the next row `prop:beta` is complete) | `WeilRH.BetaP.P`, `differentiable_P`, `P_eq`, `P_one` | `WeilRH/BetaP.lean` |
| `prop:beta`, the Beta-integral identity and the expansion (round 79; with round 72, `prop:beta` is complete) | `WeilRH.BetaIntegral.integrand`, `integral_pos`, `P_mul_Gamma`, `lower_bound`, `differentiableOn_integral`, `beta_identity`, `exp_mul_isBigO`, `expansion` | `WeilRH/BetaIntegral.lean` |
| `ζ(X, s)` of a scheme of finite type over `Spec ℤ` (Section `subsec:schemes`; round 80) | `WeilRH.SchemeZeta.zeta`, `norm`; `WeilRH.isJacobsonRing_int`, `SchemeZeta.finite_of_moduleFinite_int`, `finite_residueField`, `one_lt_norm` | `WeilRH/SchemeZeta.lean` |
| `prop:zeta-intrinsic` (round 80): relative zeta over a Jacobson base (`Spec ℤ`, `Spec 𝒪_K`) = absolute zeta, for `X` locally of finite type over the base | `WeilRH.SchemeZeta.relClosedPoints`, `relClosedPoints_eq`, `zetaRel`, `zetaRel_eq`, `zetaRel_eq_zetaRel`, `isJacobsonRing_ringOfIntegers` | `WeilRH/SchemeZeta.lean` |
| `ζ(Spec ℤ, s) = ζ(s)` for `Re s > 1` (normalization check of the definition; round 80) | `WeilRH.SchemeZeta.zeta_specInt`; `primePoint`, `primePoint_bijective`, `closedPointsSpecZEquiv`, `norm_primePoint` | `WeilRH/SchemeZeta.lean` |
| `prop:xiK-asymp`, the expansion of `f` (round 80; CONDITIONAL on B4'; PARTIAL: the expansions of `f'` and `G_ξ = −f''` are not formalized) | `WeilRH.XiKAsymp.stdBranch_asymp`; `stdBranch`, `main`, `A`, `B`, `C`, `E`, `stirling`, `stdBranch_sub_main`, `logGamma_eq_real`, `log_sub_isBigO`, `remainder_bound`, `two_rpow_isBigO`; prime sum `WeilRH.XiKPrimeSum.primeSum`, `norm_primeSum_le`, `summable_idealNorm_rpow`, `primePow_injective` | `WeilRH/XiKAsymp.lean`, `WeilRH/XiKPrimeSum.lean` |

## Fidelity notes (per declaration)

**C-PUR.** Exactly report §5's argument. Hypothesis: `∀ u v, h(Θu,v) + h(u,Θv) = j·h(u,v)`, `j : ℝ`,
`h` positive definite Hermitian. The eigenvalue statement holds in *any* complex inner product
space (no finite dimension). Semisimplicity is `Module.End.IsSemisimple` (every invariant
subspace has an invariant complement — here the orthogonal complement) and requires
`FiniteDimensional`; the corollary "generalized eigenspace = eigenspace" is the report's "no
Jordan blocks". The report's proof via skew-symmetric pairs is replaced by the equivalent
orthogonal-complement argument. Not encoded: the flow form `h(φᵗu, φᵗv) = e^{jt} h(u,v)` of (P)
(only its infinitesimal form) — now in `Flow.lean`, see below; AW5's closed/self-adjoint
realization.

**C-PUR multiplicative / C-WEIL.** Hypothesis `h(Fu, Fv) = c·h(u,v)`; conclusion `‖α‖² = c`
(no sign hypothesis needed), `‖α‖ = √c`, and for `c > 0` in finite dimension `F` is semisimple.
C-WEIL is the case `c = q ^ j` (`Real.rpow`, `q > 0`, `j : ℝ`) with `‖α‖ = q ^ (j/2)`. This
is the linear-algebra core of §7.1; it does not construct ℓ-adic cohomology, a polarization, or
the comparison `ℚ_ℓ → ℂ`.

**C-RH.** `ArithmeticWeilCohomologyQ` records: a degree-one spectral core `V : Type` with a
positive definite Hermitian form (inner product, AW4's `h₁`), `Θ : Module.End ℂ V` (AW1),
`locallyFinite` (AW1: algebraic direct sum of finite-dimensional Θ-stable blocks), `P` (AW4 ⇒
(P) with `j = 1`), and AW2's divisor consequence *without multiplicities* (identity (1) of the Sept-19 record, `D₁ = ξ/2π²`, holds only up to a nonzero constant and is superseded by that record's erratum, ruling R-1: the zeta-regularized value is `D₁ = ∏^reg (s−ρ)/2π = 2^{-1/2} ξ/2π²`, Deninger 1998 p. 168, cited in the notes as `thm:imp-deninger-product`; only the divisor of `D₁`, the zeros of `ξ` with multiplicity, is encoded, and a nonzero constant does not change it):
`zero_isEigenvalue` (nontrivial zeros ⊆ eigenvalues) and `isEigenvalue_zero` (eigenvalues ⊆
nontrivial zeros). The RH proof uses only `P` and `zero_isEigenvalue`. The conclusion is
Mathlib's `RiemannHypothesis`, verbatim. **Not encoded:** the regularized determinants `det_∞`
and zeta-regularization; the identity (AW-det) and its normalization; the endpoint computations
`D₀ = s/2π`, `D₂ = (s-1)/2π` and the exact value of `D₁` (the structure takes their *divisor*
consequence as an axiom); the order condition `m₁(ρ) = dim V¹_{Θ∼ρ} = ord_ρ ξ` (encoded instead in
`ArithmeticWeilCohomologyQMult`, below); degrees 0 and 2 as data; AW3
(duality, functional equation); the antilinear star `*₁` and cup product/trace of AW4 (only the
Hermitian form they induce); AW5 (Hilbert completion, Stone generator, domains); AW6 (no lost
spectrum, growth, trace formula); functoriality and any arithmetic construction.

**C-GRH scaffold.** `LFunctionDatum` = function `L`, degree `weight` with critical line
`Re s = weight/2` (for a pure motive of motivic weight `w`, `weight = w + 1`), and an abstract
nontrivial-zero predicate implying `L s = 0`. `ArithmeticWeilCohomology D` is the same encoding
as above with `j = D.weight`. `grh_riemannZeta_iff` checks that the zeta instance gives exactly
`RiemannHypothesis`; `toArithmeticWeilCohomology`/`ofArithmeticWeilCohomology` show the Q
structure is the zeta instance. The class 𝒞 is an arbitrary `Set LFunctionDatum`, to be fixed
by the Q1 research package. No concrete member other than ζ is built (e.g. Dedekind zeta, or
the completed `completedRiemannZeta` with its own zero predicate — see open obligations).

**C-CONV.** Under `RiemannHypothesis`, `diagonalModel` takes the finitely supported vectors of
`ℓ²(NontrivialZeros)` with `Θ` diagonal (`(Θf)(ρ) = ρ f(ρ)`). Hence
`Nonempty ArithmeticWeilCohomologyQ ↔ RiemannHypothesis`. Multiplicities are **dropped**:
zeros are indexed as a set, each eigenspace is one-dimensional; the model is not arithmetic,
not functorial, and does not implement AW2's order condition. This is the formal content of the
report's warning that bare spectral existence is a reformulation of RH.

**R2.** Report's matrices verbatim (basis `e₁, e₂, f₁, f₂` = indices 0..3; `f₂` = index 3).
Proved for all real `a`, `T` (report: `0 < a < 1/2`, `T > 0`), off-criticality needs `a ≠ 0`.
Beyond the report's list we also prove that `h` satisfies (P) with `j = 1`
(`Θᵀ H + H Θ̄ = H`), which isolates positivity as the missing hypothesis of C-PUR. Not encoded:
the graded-commutative algebra extension, and the `J₊` "second failed expectation".

**ξ datum.** Mathlib has `completedRiemannZeta` (`Λ`, junk values at the poles `0, 1`) and the
entire `completedRiemannZeta₀ = Λ + 1/s + 1/(1−s)`, but no `ξ`. We define
`completedXi s = (s(s−1)Λ₀(s) + 1)/2`, prove it entire and equal to the report's `½ s(s−1)Λ(s)` for
`s ≠ 0, 1`, prove `ξ(1−s) = ξ(s)`, `ξ(0) = ξ(1) = ½`, and `completedXi_eq_zero_iff : ξ ρ = 0 ↔
IsNontrivialZetaZero ρ` for **every** `ρ` (no side condition: `0, 1` are neither zeros of `ξ` nor
nontrivial zeros). The trivial zeros are excluded because `Λ(−2(n+1)) = Λ(2n+3) ≠ 0` (functional
equation plus `ζ ≠ 0` on `Re s > 1`). `ξ ≢ 0` gives finite analytic order everywhere, so
`analyticOrderNatAt completedXi ρ` is the honest zero order. FAITHFUL to §2.

**C-RH with multiplicities.** `ArithmeticWeilCohomologyQMult` has the fields of
`ArithmeticWeilCohomologyQ` except that the two set-level spectral axioms are replaced by
`finiteDimensional_eigenspace : ∀ ρ, FiniteDimensional ℂ (Θ.eigenspace ρ)` and
`finrank_eigenspace : ∀ ρ, finrank ℂ (Θ.eigenspace ρ) = analyticOrderNatAt completedXi ρ`, i.e. the
structure now **encodes the zero orders** `m₁(ρ) = dim V¹_{Θ=ρ} = ord_ρ ξ` of AW2 (the divisor form AW-div of
`latex/notes.tex`; only the divisor of `D₁` is encoded, the zeros of `ξ` with multiplicity, which a
nonzero constant does not change. The exact regularized value is `D₁ = 2^{-1/2} ξ/2π²` (Deninger 1998
p. 168, cited in the notes as `thm:imp-deninger-product`); identity (1) of the Sept-19 record,
`D₁ = ξ/2π²`, is superseded by its erratum (ruling R-1, recorded in
`ai/2026-09-25-harvest-pass-2/contradictions.md`)). Because (P) rules out Jordan chains in any dimension
(`maxGenEigenspace_eq_eigenspace_of_P`), the same holds for generalized eigenspaces
(`finrank_maxGenEigenspace`), which is AW2's `dim V¹_{Θ∼ρ}`. The structure maps to the old one
(`toArithmeticWeilCohomologyQ`), so it implies RH. **Still not encoded:** `det_∞`,
zeta-regularization, (AW-det) and the exact value `D₁ = 2^{-1/2} ξ/2π²` (the structure takes the *divisor* of
`ξ` as its axiom), degrees 0 and 2, AW3, the star, AW5–AW6, arithmetic construction.

**C-CONV with multiplicities.** Under RH, `multDiagonalModel` is the finitely supported part of
`ℓ²(Σ ρ : NontrivialZeros, Fin (ord_ρ ξ))` with `Θ` acting on the `(ρ, k)` coordinate by `ρ`; the
`ρ`-eigenspace is `ℂ^{ord_ρ ξ}` (`GenDiag.finrank_eigenspace`). This is exactly the report's
"basis for every zero counted with order". Hence `Nonempty ArithmeticWeilCohomologyQMult ↔
RiemannHypothesis`: the multiplicity-faithful encoding is *still* a reformulation of RH. The model is
built from the zeros themselves; it is not arithmetic or functorial.

**(P) flow form.** `P_iff_flow`: for a bounded `Θ : E →L[ℂ] E` on a complete complex inner
product space and `φ^t = NormedSpace.exp (t • Θ)`, (P) with weight `j` holds iff
`h(φ^t u, φ^t v) = e^{jt} h(u, v)` for all real `t` (both directions; proof by differentiation:
`F' = jF`, so `e^{−jt}F` is constant; conversely differentiate at `0`). The finite-dimensional
version for `Θ : Module.End ℂ E` uses `LinearMap.toContinuousLinearMap Θ`; `flow_restrict` gives
`h₁(φ^t u, φ^t v) = e^t h₁(u, v)` on every finite-dimensional `Θ₁`-stable block of an
`ArithmeticWeilCohomologyQ` (AW1's "`φ^t = e^{tΘ}` on each finite-dimensional block"). Unbounded
generators and the unitary group of AW5 are not covered.

**R2 (`J₊`).** `J₊ v = −Ω v̄` (matrix `Jplus = −Ω`): `J₊² = −1` (`Jplus_sq`), `B(v, J₊w) = vᵀw̄`
(`Ω · Jplus = 1`), and the commutation defect `ΘJ₊ − J₊Θ̄ = −2a · [[0, I₂], [I₂, 0]]`
(`commDefect_eq`), whose nonzero entries have modulus `2|a|` (`norm_commDefect_apply`); so `J₊`
does not commute with the flow for `a ≠ 0` (`Jplus_not_commute`). FAITHFUL (report: "nonzero
entries of modulus `2a`", `a > 0`).

**R3.** `det(s·1 − Θ) = w⁴ + 2(T² − a²)w² + (T² + a²)²`, `w = s − 1/2` (via the factored form
`((w−a)² + T²)((w+a)² + T²)`), symmetry `s ↦ 1 − s`, no real zeros for `T ≠ 0`, and invertibility
of every integer twist `Θ − n`. Not encoded: the statement about based/metrized determinant
lines of cones.

**R12.** Zeros `π ± i a` of `cos z + cosh a`, and `∫ e^{i z t} dμ_a(t) = cos z + cosh a` for
the positive measure `μ_a = cosh(a)·δ₀ + ½(δ₁ + δ₋₁)` (a `Measure ℝ`, hence positive by
construction). Not encoded: the Gaussian-smoothed variant.

R4 (unbounded skew-symmetric operator with spectrum ℂ) was not attempted (analysis-heavy).

**Abstract positive forms (`Hermitian.lean`).** `PosHermForm V` = a function `V → V → ℂ`, additive
and linear in the first argument, Hermitian, `0 < Re h(u,u)` for `u ≠ 0` (report convention). The
purity lemmas are transported by building the inner product `⟪x, y⟫ := h(y, x)` *inside each
proof* (`InnerProductSpace.ofCore`); the statements are about the original `Module ℂ V` and the
original `Θ`/`F`, so no instance diamond is introduced. FAITHFUL (pure infrastructure).

**Q1-L4.2 (`Duality.lean`).** `WeightedStarDatum d w j V W T` is the degree-`j` slice of Q1's
weighted package of type `(d, w)`: `V = V^j`, `W = V^{2d-j}`, `T = V^{2d}` with flows; a bilinear
cup `V →ₗ W →ₗ T` with `Θ_{2d}(u ∪ v) = Θu ∪ v + u ∪ Θv` (AW1); a trace `tr : T →ₗ ℂ` with
`tr(Θ_{2d} x) = (d + w) tr x` (AW3: equivariance to `ℂ(−d−w)`); an **antilinear** star
`V →ₗ⋆[ℂ] W` with `Θ_{2d-j} ∘ * = * ∘ Θ_j + (d − j) *` (AW4). `h(u, v) = tr(u ∪ *v)`.
`derivation_law` is Lemma 4.2 verbatim, **without** positivity: `h(Θu, v) + h(u, Θv) = (w + j) h(u, v)`.
With `IsPositive` (Hermitian + positive definite, AW4) `re_eq_of_hasEigenvalue` gives
`Re ρ = (w + j)/2` (Theorem 0) and `isSemisimple` (finite dimension). `lineModel τ` is a positive
one-dimensional datum of type `(1, 0)` with eigenvalue `1/2 + iτ` (Q1 Prop. 5.1, non-vacuity).
FAITHFUL to Lemma 4.2 + Theorem 0. Not encoded: perfectness of `B` (AW3's "pairs perfectly" is not
used by Lemma 4.2), graded commutativity, the other degrees, functoriality, AW2, the quaternionic
refinement `*² = −1`. The other half of **Q1 Cor. 5.2** — AW1–AW3 plus a flow-compatible
*indefinite* form with off-line spectrum — is the existing `WeilRH.R2.counterexample` (a `(2,2)`
Hermitian form satisfying (P) with `j = 1` and eigenvalue `1/2 + a + iT`, `a ≠ 0`); we did not
repackage R2 as a `WeightedStarDatum` (it would need the R2 pairing `Ω` as cup/trace and `J` as
star; the matrix identities are already proved).

**Q2-T1′ (`AlgebraForm.lean`).** `PositiveTrace A` for a complex `*`-algebra
(`[Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]`, so `†` is antilinear, anti-multiplicative,
involutive): `τ : A →ₗ[ℂ] ℂ`, `τ(ab) = τ(ba)`, `τ(a†) = conj τ(a)`, `0 < Re τ(a a†)` for `a ≠ 0`
(the report's `τ(aa†) > 0`; realness is automatic from the other axioms). `⟨a, b⟩ = τ(a b†)`.
`form_mulLeft_mulLeft`: `g g† = q^j ⇒ ⟨ga, gb⟩ = q^j⟨a, b⟩`, via `star_mul_self_eq` (`g g† = c ≠ 0 ⇒
g†g = c` in finite dimension, Dedekind-finiteness). Then Theorem 1′: every eigenvalue of `L_g` has
`‖α‖ = q^{j/2}`, `L_g` is semisimple, `minpoly g = minpoly L_g` is squarefree, and every root of
`minpoly g` has modulus `q^{j/2}`. The additive AW4-E of Remark 4.4 (`Θ + Θ† = j ⇒ L_Θ` satisfies
(P), `Re ρ = j/2`, semisimple) is `form_P_mulLeft` / `re_eq_half_of_mulLeft` /
`isSemisimple_mulLeft_of_add_star`. `matrixTrace` shows the hypotheses are satisfiable for
`Matrix n n ℂ` (`† = ᴴ`, `τ = trace`); `matrix_norm_eq_rpow`, `matrix_isSemisimple`. FAITHFUL to
Theorem 1′ over `k = ℂ`. **Gaps:** `k = ℚ, ℝ` (base change `A ⊗_k ℂ` and positivity of the Hermitian
extension), the clause `ρ(g†) = conj ρ(g)`, Corollary 1″ (transfer to a faithful representation
`A ⊆ End V`; done over `k = ℂ` in round 39, `rep_isSemisimple`), and AW4-E's "flow-stable subalgebra of `End(V^j)` containing `Θ_j`" packaging.

**C-A (`Dedekind.lean`).** Mathlib v4.34.1 has `NumberField.dedekindZeta K` only as the L-series
`∑ #{I : N I = n} n^{-s}` (correct for `Re s > 1`) and its residue at `1`; it has **no** continuation,
functional equation or completed `Λ_K`. So `DedekindContinuation K` bundles a function `Λ`,
holomorphic on `ℂ ∖ {0, 1}`, equal to `|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s)` on `Re s > 1`
(`dedekindGammaFactor`, Mathlib's `Gammaℝ`, `Gammaℂ`, `discr`, `nrRealPlaces`, `nrComplexPlaces`),
with `Λ(1 − s) = Λ(s)`: Hecke's theorem, taken as **data**, not as an axiom. `eqOn` proves the
continuation is unique off `{0, 1}` (identity theorem), so the nontrivial-zero predicate
`Λ ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1` and GRH are continuation-independent (`dedekindDatum_grh_iff`).
`grh_dedekind_of_awc` is Theorem A (1) in class form (weight 1, critical line `Re s = 1/2`), proved
objectwise by `ArithmeticWeilCohomology.grh`, as Q1 remarks ("the hypothesis is used objectwise").
**Honesty caveat:** for a field `K` for which no `DedekindContinuation K` has been constructed in
Lean, the hypothesis of `grh_dedekind_of_awc` cannot be instantiated at `K` inside this development;
the statement is not vacuous there, since the type is inhabited mathematically (Hecke). For `K = ℚ` we construct it:
`card_ideal_rat_eq_one` (each `n` is the norm of exactly one ideal of `𝓞 ℚ`) gives `dedekindZeta_rat :
ζ_ℚ = ζ` on `Re s > 1`, and `DedekindContinuation.rat` uses Mathlib's `completedRiemannZeta`
(`dedekindGammaFactor ℚ = Gammaℝ`). Hence `dedekindDatum_rat_grh_iff : GRH(ℚ, C) ↔ RiemannHypothesis`
for every continuation `C`, `riemannHypothesis_of_awc_dedekind_rat`, and
`riemannHypothesis_of_grh_dedekind_class` (the class hypothesis ⇒ Mathlib's `RiemannHypothesis`,
non-vacuously). `dirichletDatum χ` (Mathlib's continued `DirichletCharacter.LFunction`, zeros in
`0 < Re s < 1`) is a second, fully concrete family in 𝒞; `grh_dirichlet_of_awc` is the Theorem A (2)
*shape* for Dirichlet characters, **not** Q1's derivation of (2) from (1) via class field theory.
Not encoded: poles / order-one growth of `Λ_K`, functoriality on 𝒜, Galois descent, Brauer
induction (Theorem A (2)–(3)), multiplicities for `Λ_K`, AW-det, Prop. 4.5 (discriminant).

**C-B (`Calibration.lean`).** `E` finite-dimensional complex inner product space (`V^j = H^j ⊗_ι ℂ`
with the positive form `h`), `F` with `h(Fu, Fv) = q^j h(u, v)`, `q > 1`; by C-WEIL `F` is
semisimple with `|α| = q^{j/2}`, so we are in the semisimple case of Definition 6.1. For each
`k : ℤ`, `suspension F q k = p(F)` (Lagrange interpolation on the roots of `minpoly F`) acts on the
`α`-eigenspace by `ρ_k(α) = (log α + 2πik)/log q` (principal `Complex.log`; over all `k` the set is
branch-free) — this is the `k`-th copy of `V̂ = ⨁_ρ V_{(q^ρ)}`. `suspension_P` is Prop. 6.2(a)
(`h(Θ_k u, v) + h(u, Θ_k v) = j h(u, v)`, via orthogonality of distinct eigenspaces as in
Theorem 1), `flow_suspension` is `q^{Θ_k} = exp(log q · Θ_k) = F`, `weil_of_P_of_flow` is
Prop. 6.2(b) ((P) + `exp(log q · Θ) = F` ⇒ Weil identity, via `P_iff_flow_of_finiteDimensional` at
`t = log q`), and `suspension_P_iff_weil` packages both directions — i.e. "(P) is the logarithm of
`F*F = q^j`" and Thm 6.5(4) (AW4 on the suspension ⇔ Weil positivity ⇔ semisimple + pure, the last
equivalence being Q2 Prop. 2 / C-WEIL). **Gaps:** one copy `k` at a time (the full `ℤ`-indexed
algebraic direct sum with the orthogonal-sum form is not built; (P) and the flow identity are
copywise), no nilpotent part (`N ≠ 0`; §7 shows positivity forbids it anyway), no regularized
determinant (Thm 6.3), no suspended duality/star, no étale cohomology, no choice of `ι`.

**C-K6 (`Kronecker.lean`, `Kunneth.lean`; Künneth report Theorem 6).** *Matrix core:* for Hermitian
`A`, `B` on nonempty index types, `A ⊗ₖ B` (the Gram matrix of `h ⊗ h′`) is `PosDef` iff `A`, `B` are
both positive or both negative definite (`posDef_kronecker_iff`; no nondegeneracy needed — positivity
on pure tensors, `star_dotProduct_kronecker_mulVec`, already forces it), and `A ⊗ₖ A` is `PosDef` iff
`A` is definite (`posDef_kronecker_self_iff`). The general signature formula `(pp′+qq′, pq′+qp′)` is
**not** formalized. *Model:* `SurfaceDatum V` is the degree-one data of Theorem 6 on a
**finite-dimensional** `V = V¹`: `Θ`, a bilinear `B : V →ₗ V →ₗ ℂ` of weight one
(`B(Θx,y) + B(x,Θy) = B(x,y)`, i.e. AW1+AW3 for `V¹×V¹ → V² → ℂ(−1)`), nondegenerate in the first
variable (only this half of perfectness is used), an antilinear bijective `∗ : V →ₗ⋆ V` with `Θ∗ = ∗Θ`
and `B(∗x,∗y) = conj B(x,y)`, and `h₁(x,y) = B(x,∗y)` Hermitian — **positivity not assumed**. It is the
`(1,0,1)` instance of `WeightedStarDatum` with `W = V`, `T = ℂ` (`toWeightedStarDatum`), and Q1
Lemma 4.2 is reused for `derivation_law`. `V_ρ` is the *generalized* eigenspace
(`Θ.maxGenEigenspace ρ`). *(i):* `h₁(V_ρ, V_σ) = 0` unless `ρ + σ̄ = 1` (induction on Jordan-chain
length), so `h₁ ≡ 0` on `V_ρ` for `Re ρ ≠ ½` and `h_S ≡ 0` on `V_ρ ⊗ V_{1−ρ}`. Spectral symmetry
`ρ ↦ 1−ρ` is proved from nondegeneracy of `B` (`hasEigenvalue_one_sub`). *(iii):* `N_S` and `h_S` are
encoded **blockwise by Gram matrices**: `blockGram ρ` = Kronecker product of the Gram matrices of `h₁`
on `V_ρ` and on `V_{1−ρ}` (in `Module.finBasis`), and `HodgeIndex := ∀ ρ, (blockGram ρ).PosDef`.
`hodgeIndex_iff_pureDefinite`: `HodgeIndex ↔ ∀ ρ ∈ Spec Θ, Re ρ = ½ ∧ h₁ definite (either sign) on
V_ρ` (both directions; the sign on `V_{1−ρ} = V_{ρ̄} = ∗V_ρ` matches via `h₁(∗x,∗x) = h₁(x,x)`);
`HodgePure` (positivity on pure tensors `x ⊗ y` only) is also equivalent. From it: `Re ρ = ½` for every
eigenvalue and `Θ` semisimple (no Jordan blocks: `maxGenEigenspace_eq_eigenspace`; semisimplicity via
a squarefree annihilating polynomial, `isSemisimple_of_maxGenEigenspace_eq_eigenspace`). The report's
own route is also formalized: on each `V_ρ`, `±h₁` is a `PosHermForm` satisfying (P) with weight one,
and `PosHermForm.re_eq_half` / `.isSemisimple` (C-PUR) give `Re ρ = ½` and semisimplicity of `Θ|V_ρ`
(`re_eq_half_of_definiteOn`, `isSemisimple_restrict_of_definiteOn`, `toWeightedStarDatum_re_eq_half`).
FAITHFUL to Theorem 6 (i), (iii) at the level of a finite-dimensional, eigenspace-level model of `N_S`.
**Fidelity gaps:** (1) finite dimension — Z(K) is infinite, so the real `V¹` is an infinite algebraic
direct sum; the theorems apply to every finite `Θ`-stable, `∗`-stable sub-datum on which `B` stays
nondegenerate, not to the whole `V¹`; (2) the tensor product `V¹ ⊗ V¹`, the completion
`Π_ρ V_ρ ⊗ V_{1−ρ}`, the classes `[Δ]`, `[Γ_t]` (Prop. 6) and the ambient product category / Künneth
map `κ` are **not** encoded — `N_S` exists only through its block Gram matrices; blockwise positivity
equals positivity on `N_S` by the orthogonality of distinct blocks once all `Re ρ = ½`
(`h_eq_zero_of_mem_maxGenEigenspace`), argued in the docstring rather than stated about a global form;
(3) Theorem 6(ii) is formalized only as its positive-definite consequence (no signature count
`(p²+q², 2pq)`), and nondegeneracy of `h₁|V_ρ` is not stated separately; (4) Theorem 6(iv) (Rosati /
Castelnuovo trace form `tr(uv*)` on `End(V_ρ)`, the involution `v ↦ v^†`) and the flow-algebra /
Weil explicit-formula restriction (K6)(d) are not formalized; (5) GRH for `ζ_K` itself is not derived
here (it needs AW2's divisor identification, as in `ArithmeticWeilCohomology`).

**`def:aw4-EF`, `prop:aw4-EF` (`MultiplicativeForm.lean`).** *Representation:* the subalgebra
`A ⊂ End_ℂ(V)` with its positive trace involution is encoded as an abstract finite-dimensional complex
`*`-algebra `A` (`PositiveTrace A`, `† = star`) with an injective unital `ι : A →ₐ[ℂ] End_ℂ(V)` and
`f ∈ A`, `ι f = F`, `f f^† = q^j` (`AW4EFDatum`); the notes' subalgebra is `ι(A)` with `†`
transported, so the two are equivalent (finite-dimensionality of `A` is derived from injectivity).
(i) FAITHFUL: `F` has the two-sided inverse `ι(q^{-j} f^†) ∈ ι(A)` (`mul_inv`, `inv_mul`), is
semisimple and spanned by its eigenvectors (diagonalizable), and every eigenvalue has modulus `q^{j/2}`
(only `q > 0` is needed). (ii) FAITHFUL for `θ_σ^† = j − θ_σ` (`star_sheetElem`, `q > 1`) and
`θ_σ = p_σ(F) ∈ A` with `p_σ` the Lagrange interpolant of `σ` on the eigenvalues. In this module
`Θ ι_σ = ι_σ θ_σ` is encoded as "`θ_σ` acts on `ker(F − α)` by `σ(α)`" (`ι_sheetElem_apply`); the
statement on the suspension itself, with `(V̂, Θ)`, `ι_σ` and `V̂_σ` built in rounds 12–16, is
`AW4EFDatum.theta_sheetMap` (round 14, `SuspObject.lean`). The degree bound `deg p_σ <`
#eigenvalues is not stated. (iii) FAITHFUL for every finite family of sheets: the
truncation `V̂' = ⨁_{i<n} V̂_{σ_i}` is `Fin n → V` (via the sheet maps), `Θ'` acts on copy `i` by
`θ_{σ_i}` (`truncTheta_apply`), and `truncation` gives the additive datum `AW4EAddDatum` with
`A' = Fin n → A` acting componentwise (injective), `τ' = ∑ τ`, componentwise `†`, `θ'^† = j − θ'`;
`AW4EAddDatum.re_eq_half` / `.isSemisimple` derive purity from it. The statement "every vector of `V̂` lies
in such a `V̂'`" is `AW4EFDatum.exists_aw4EAdd_suspension` (round 15, `SuspObject.lean`);
`isSheet_add_int` records that the sheets `σ + 2πim/log q` of the notes' proof are sheets. (iv) FAITHFUL: `A^t` is `Aᵐᵒᵖ` acting by
transposition `a ↦ (ι a)^t` (injective), trace `a^t ↦ τ(a)`, involution `a^t ↦ (a^†)^t` (`dual`).
The link to `Calibration.lean`: the `k`-th suspension copy `suspEigen q k` is a sheet
(`isSheet_suspEigen`).

**`prop:rosati-EF` (`MultiplicativeForm.lean`).** PARTIAL (linear-algebra content only).
`rosati_aw4EF` is item (iii) for an abstract complex `*`-algebra with positive trace involution
acting faithfully on `V` and an element `π` with `π π^† = q`: all three are **hypotheses** — the
Jacobian, `End⁰(J)`, the Tate module `V_ℓ J`, injectivity of `End⁰(J) ⊗ ℚ_ℓ → End(V_ℓ J)` (item (i)),
the extension of the Rosati involution to `End⁰(J) ⊗ ℂ`, `Tr(a^†) = Tr(a)` via the Weil pairing, Weil /
Milne positivity of `Tr(α β^†)` and `π π^† = q` (Theorem `thm:imp-rosati`) are not formalized.
The positivity step of item (ii) is formalized: `rosati_gram_posDef` (a symmetric rational Gram
matrix positive on `ℚⁿ` is Hermitian positive definite on `ℂⁿ`, via density of `ℚⁿ` in `ℝⁿ`,
`det G ≠ 0` and `z̄ᵀGz = uᵀGu + vᵀGv`), and `rosati_trace_pos` (given a `ℂ`-basis `b` with
`τ(b_i b_k^†) = G_{ik}` rational, symmetric, positive on `ℚⁿ`, `Re τ(x x^†) > 0` for `x ≠ 0`).

**`prop:ff-phantom` (`Phantom.lean`).** FAITHFUL. `S_N` is `phantomSet q N`, the image of
`m ↦ √q e^{iπ(2m+1)/N}` on `m < N` (injective, `phantom_injOn`), so sums over `S_N` are sums over
`m`. (i): `∑_{α∈S_N} α^k = 0` for `1 ≤ k < N` (`N ≥ 2` is implied), `∑ α^N = −N q^{N/2}`, `|α| = √q`,
`q/α = ᾱ ∈ S_N`. (ii): `⋃_{α∈S_N} Σ_q(α) = C_{N log q}` with `Σ_q(α) = {ρ : exp(ρ log q) = α}`;
by `def:log-susp` this union is the spectrum (index set) of the logarithmic suspension of
`(ℂ^{S_N}, diag(S_N))`; the statement on the suspension itself is `Suspension.spec_theta_phantom`
(round 14, `SuspObject.lean`).

**`thm:ff-lefschetz` (`Lefschetz.lean`).** PARTIAL (finite-dimensional core). Degreewise Frobenius
data are finite multisets `M j` of eigenvalues with algebraic multiplicity; `lefschetzNumber n M k =
∑_{j<n} (−1)^j ∑_{α∈M j} α^k` is `N_k` once `Tr(F^k | V^j) = ∑_{α∈M j} α^k` (the identity the notes'
proofs use; the link `Tr(F^k) = ∑ roots(charpoly F)^k` for a linear map is **not** formalized).
Proven: equal `N_k` for all `k ≥ 1` ⇒ equal alternating multiplicities `∑_j (−1)^j m_j(α)` at every
`α ≠ 0` (`altCount_eq_of_lefschetzNumber_eq`, via Dedekind–Artin independence of `k ↦ α^k`), hence
equal rational functions `∏_j det(1 − F_j T)^{(−1)^{j+1}}` in `RatFunc ℂ` (`zetaRat_eq_of_*`;
`zetaRat_eq_prod` identifies its divisor with minus the alternating divisor). **Not formalized:**
item (i) (point counts via the trace formula, `N_0`, duality `N_{−k} = q^{−dk} N_k`), item (ii)
(Poisson summation, test functions `C_c^∞`), item (iii) for the infinite suspended spectrum with a
one-sided tail of test functions (`prop:exp-unique`).

**`prop:EM`, `prop:EM-criterion` (`EilenbergMoore.lean`).** PARTIAL (abstract core). In any Mathlib
pretriangulated category `C`, `ThickClosure P` is the inductively defined thick closure (contains `P`
and zero objects; closed under `⟦n⟧`, `n ∈ ℤ`, under the middle vertex of distinguished triangles, and
under retracts) and `thickClosure_le` proves it is the smallest triangulated, retract-closed class
containing `P` — i.e. `⟨P⟩` of `def:EM-setting`(a) (strictly full since retract-closed). For
triangulated functors `F G : C ⥤ D` and a shift-compatible `κ : F ⟶ G` (a natural transformation of
exact functors), `isIso_app_of_mem_thickClosure`: `κ` iso on `P` ⇒ iso on `⟨P⟩` (five lemma
`isIso₂_of_isIso₁₃` on `mapTriangleHom`, retracts via `NatTrans.retractArrowApp`), and
`isIso_comp_of_mem_thickClosure` handles the composite shape of the Eilenberg–Moore map `κ`
(`def:EM-kappa`). For `prop:EM-criterion`, the closure lemmas (`ext₁`, `ext₂`, `ext₃`, `shift`,
`biprod`, `pow`) are the steps of its induction. **Not formalized (inputs):** `D(S_et, Λ)`,
`D^+`, cochain enhancements, `μ_S` and its exactness in each variable, proper base change and the
projection formula (`prop:EM-fibre`), cohomology sheaves `R^i f_*Λ`, their filtrations, the passage
from short exact sequences of sheaves and truncation triangles `τ_{≤ i}` (t-structures) to
distinguished triangles.

**`prop:B-support`.** The hypothesis of `pairing_eq_zero_of_mem_maxGenEigenspace` is the identity
`B(Θu, v) + B(u, Θv) = c·B(u, v)` that the manuscript's proof derives from the derivation rule of
AW1 and the trace equivariance of AW3, with `c = d` for a Weil datum of type `(d, 0)`; that
derivation (one line in the source) is not re-done here, and `B = B_j` is an arbitrary bilinear
pairing `V × W → K` over any field `K` (the source has `K = ℂ`). The conclusion is verbatim:
`B` vanishes on `V_{Θ∼ρ} × W_{Θ∼σ}` unless `ρ + σ = c`. Round 8:
`cupTrace_eq_zero_of_mem_maxGenEigenspace` takes exactly the source's hypotheses, the derivation
rule `Θ(u ∪ v) = Θu ∪ v + u ∪ Θv` for a bilinear cup `V^j × V^{2d-j} → V^{2d}` and
`tr(Θ_{2d} x) = n·tr(x)`, and concludes `tr(u ∪ v) = 0` unless `ρ + σ = n`; the manuscript's case
is `n = d` (type `(d, 0)`). The graded pieces are arbitrary complex vector spaces (the source's
spectral-core conditions are not needed). `WeightedStarDatum.B_eq_zero_of_mem_maxGenEigenspace`
restates it for the existing degree-`j` slice of type `(d, w)` (`n = d + w`, so `w = 0` is the
source); that structure also carries the AW4 star, which is not used.

**`prop:weil-converse`.** A positive Frobenius polarization of weight `j` (`def:frob-pol`) is a
`PosHermForm` `h` (positive definite Hermitian, linear in the first argument) with `IsFrobPol h F q
j`, i.e. `h(Fu, Fv) = q^j h(u, v)`. "Diagonalizable" is `⨆ α, F.eigenspace α = ⊤`.
`exists_frobPol_iff` is (i) verbatim (`1 < q`, `j : ℝ`, `V` finite-dimensional complex). The
backward direction builds the form `Σ_i u_i conj(v_i)` in a basis of eigenvectors (`basisForm`,
`DirectSum.IsInternal.collectedBasis`) rather than an orthogonal sum of arbitrary forms.
`isFrobPol_iff_orthogonal` is (ii) in the form "a positive definite Hermitian form is a
polarization iff distinct eigenspaces are `h`-orthogonal", under the hypotheses of (i) (only
`0 < q` is used). Since `V = ⊕_α V_α`, a form with orthogonal eigenspaces is the orthogonal sum of
its restrictions, which are positive definite Hermitian. Round 9 states (ii) as written:
`isFrobPol_iff_exists_assemble` says `IsFrobPol h F q j ↔ ∃ (h_α), h = assemble hdiag (h_α)`, where
`assemble hdiag (h_α)` is `⊕_α h_α`, `(u, v) ↦ Σ_α h_α(u_α, v_α)` over the finite set of eigenvalues,
with `u_α` the component of `u` in the internal direct sum `V = ⊕_α V_α` (`eigenProj`). Any family
of positive definite Hermitian forms is allowed (forms on zero eigenspaces are irrelevant), and
`restrict_assemble` shows `h_α` is recovered as the restriction, so the orthogonal sum determines
its summands. `V` is finite-dimensional as in the source; only `0 < q` is used.

**`prop:N-lines`.** The analytic results use any real `q > 1` (the source has a prime power).
`NLinesGeometry` formalizes the geometric product-count step: for schemes over a field and any
extension `K`, the `K`-points of their pullback are pairs, hence their counts multiply. Its
`zetaOfCounts_product_of_geometry` passes this count identity to the analytic product theorem.
Mathlib's `Projectivization.card_of_finrank_two` gives `#ℙ(K²) = #K + 1` for finite `K`.
`finiteExtensionFamily` constructs extensions `Kₙ/F` of degree `n` for `n > 0`, with
`#Kₙ = (#F)^n`; the arbitrary degree-zero field is `F`. The geometric zeta bridges require
count identities only for `n > 0`, since the degree-zero series term vanishes. In
`zetaOfCounts_product_finiteExtensions`, the remaining geometric input is an identification
of scheme `ℙ¹(Kₙ)` with this projectivization. `ProjectiveLineScheme` now fixes the scheme as
`Proj F[X₀,X₁]` and its structure morphism to `Spec F`; the structure morphism is proved
proper. Its specialized zeta theorem uses that actual `ℙ¹_F` rather than an arbitrary scheme
`Y`. The point identification remains an input.
The elliptic point-count formula is a hypothesis:
`#E(𝔽_{qⁿ}) = qⁿ + 1 - αⁿ - βⁿ` with `|α| = |β| = q^{1/2}` (`eq:elliptic-zeta`, from
`thm:imp-deligne`). With these two inputs, `zetaOfCounts_finiteExtensions_eq_zetaX` identifies
the zeta function of the scheme product over the constructed extensions with `zetaX` on
`Re s > 2`. It uses only positive-degree counts; `zetaOfCounts_eq_zetaX` now has that same
hypothesis. `NLinesFormal.zetaSeries` also encodes
`Z(X,t)=exp(Σ_{n≥1} #X(𝔽_{qⁿ})tⁿ/n)` as a formal power series, and
`zetaSeries_projectiveLineScheme_product` proves (i) as the literal identity
`Z(X,t)=Z(E,t)Z(E,qt)` under the remaining `ℙ¹` point-equivalence input.
The analytic specialization (`zetaOfCounts_product`) reads
`ζ_X(s) = ζ_E(s) ζ_E(s-1)` under convergence of both `E`-series. `zetaOfCounts_eq_zetaX` proves
`ζ_X = num/den` on `Re s > 2`, where the series converges. The zeros and poles in (ii)–(iii) are those of
the meromorphic continuation, represented by the rational expression `zetaX = num/den`. That the
continuation is unique (the identity theorem) is not restated. In (ii), "zeros" are points with
`den s ≠ 0` and `zetaX s = 0`; `zeros_zetaX` gives the set equality with
`Σ_q(α) ∪ Σ_q(β) ∪ (1+Σ_q(α)) ∪ (1+Σ_q(β))` (`progression`, `shift1`), the two-line location, and
infinitude of the zeros on each line (via `Σ_q(α)` alone). (iii) is `poles_zetaX`: `zetaX` is
holomorphic wherever `Re s ∉ {0, 1, 2}`, and wherever `den` vanishes, `num` does not and
`Re s ∈ {0, 1, 2}`.

**`prop:tensor-eigen`.** `Θ = Θ_V ⊗ 1 + 1 ⊗ Θ_W` is `ΘV.rTensor W + ΘW.lTensor V`; the block
`V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}` is the range of the tensor product of the two inclusions (Mathlib's
`TensorProduct.map` of the subtypes; over a field it is injective, `blockEquiv`).
`maxGenEigenspace_tensorSum_eq` proves the first display of the proposition, as an equality of
subspaces with `⨆` in place of `⊕`, assuming only that `V` and `W` are spanned by their
generalized eigenspaces. Round 7: directness is `isInternal_block` (all blocks, in `V ⊗ W`) and
`isInternal_block_maxGenEigenspace` (blocks with `ρ + ρ' = λ`, inside `(V ⊗ W)_{Θ∼λ}`), both
`DirectSum.IsInternal`, from `iSupIndep_block` (the blocks lie in the joint generalized
eigenspaces of the commuting pair `Θ_V ⊗ 1`, `1 ⊗ Θ_W`). "Finite-dimensional `Θ`-stable with the
single eigenvalue `ρ + ρ'`" is `mapsTo_block`, `block_le` and the `FiniteDimensional` instance on
`block`, which takes `FiniteDimensional` instances on `V_{Θ∼ρ}`, `W_{Θ∼ρ'}` (the
finite-dimensionality clause of `def:spectral-core` (b)). The dimension formula
`rank_maxGenEigenspace_tensorSum` is stated with `Module.rank` and `Cardinal.sum`, so it holds
also when the sum is infinite (the manuscript's remark after the proof); for spectral cores each
term is the finite product `m_V(ρ) m_W(ρ')`. Divergences: `V` and `W` are in one universe (so the
products need no `Cardinal.lift`); the left side carries `Cardinal.lift` to the universe of `K`;
the discreteness clause is never used; the field is arbitrary (source: `ℂ`); the two `IsInternal`
statements take `[DecidableEq K]` (automatic classically).
Round 10: `SpectralCore Θ` (over `ℂ`) records `def:spectral-core` (b): spanning by the generalized
eigenspaces (`iSup_eq_top`; directness is automatic, so the "algebraic direct sum" clause is
equivalent), `FiniteDimensional` pieces, and "no finite accumulation point" as
`∀ z, ¬ AccPt z (𝓟 (spec Θ))`. `mult Θ ρ = finrank V_{Θ∼ρ}` is (c). `SpectralCore.tensor_eigen` is
the whole proposition for spectral cores (dimension as a cardinal). `finrank_maxGenEigenspace_tensorSum`
adds the hypothesis that `pairs ΘV ΘW λ = {(ρ, ρ') ∈ spec Θ_V × spec Θ_W : ρ + ρ' = λ}` is finite and
then gives `FiniteDimensional` and `finrank = Σ_{p ∈ pairs} m_V m_W`; pairs outside the spectra
contribute `0` to the source's sum, so the sums agree. The finiteness is a genuine extra hypothesis
(not implied by the spectral-core conditions; cf. `thm:kun-square`). Discreteness is still unused;
`V` and `W` share a universe.

**`prop:N-jordan`.** `jordanF q j` is the source matrix verbatim. A positive Frobenius
polarization (`def:frob-pol`) on `ℂ²` is encoded as `hermForm H u v = v* H u` with `H.PosDef`;
every positive definite Hermitian form on `ℂ²`, linear in its first argument, has this form, with
`H` its Gram matrix. `not_exists_polarization` negates the existence of such `H` with
`h(Fu, Fv) = q^j h(u, v)` for all `u, v`. The proof differs from the source's (which cites
`prop:weil-linear`, i.e. `WeilRH.isSemisimple_of_weil`): the identity at `(e₁, e₀)` gives
`q^(j/2) h(e₀, e₀) = 0`. `norm_eq_of_hasEigenvalue` is the purity clause for eigenvalues of
`Matrix.toLin' F`; `hasEigenvalue_jordanF` shows it is not vacuous. The hypothesis `1 < q` is the
source's (only `0 < q` is used). Round 10: `not_exists_frobPol` is the same clause in the
`WeilConverse.lean` encoding (`PosHermForm` on `Fin 2 → ℂ`, `IsFrobPol` for `Matrix.toLin' F`), by
the source's route: `eq_of_hasEigenvalue` (the only eigenvalue is `q^(j/2)`),
`iSup_eigenspace_ne_top` (`e₁` is not in the eigenspace, so `F` is not diagonalizable), then
`exists_frobPol_iff`, whose forward direction is `prop:weil-linear`.

**`prop:polarization-identity`.** The manuscript now states it for a Weil datum of type `(d, 0)`,
with conclusion `h_j(Θu, v) + h_j(u, Θv) = j h_j(u, v)`. `WeightedStarDatum.derivation_law` (round 3,
Q1 Lemma 4.2) proves the type-`(d, w)` statement with `(w + j)`; at `w = 0` it is the manuscript's.
No new declaration was added.

**`prop:formal-curve`.** An element of `H⁰ ⊕ H¹ ⊕ H²` is a triple `(a, x, b) : ℂ × (Fin 2 → ℂ) × ℂ`;
`mul` is the cup product of `def:formal-curve` written out on components (graded commutative, so it
is not a `Ring` instance), and "automorphism of the graded algebra" is `F_mul`, `F_one` and
`F_bijective` for the componentwise (hence graded, linear) map `F`. "Perfect" is `B_perfect`: every
linear functional on `H¹` is `B(x, ·)` for a unique `x`. In `lefschetz n` the traces on the
one-dimensional pieces are written as `1` and `3ⁿ` (the values of `Fⁿ` there) and only the `H¹`
trace is computed from `F₁`; likewise `Z t` takes `det(1 - Ft | H⁰) = 1 - t` and
`det(1 - Ft | H²) = 1 - 3t` directly. `Z` is a function of `t : ℂ` (division by zero is junk at the
poles), not a rational function; `P₁ ∈ ℤ[t]` is the determinant over `ℤ[X]`, linked to `F₁` by
`P₁_eval`, and the functional equation `P₁_funct` is stated pointwise for `t ≠ 0`. In (iii),
Hermitian forms are given by Gram matrices (`hermForm G u v = v* G u`, linear in the first argument);
`frobCompatible_iff` holds for every matrix `G`, and "signature `(1, 1)`" for a nonzero Hermitian
`G` on `ℂ²` is encoded as `det G ≠ 0` together with a positive and a negative direction
(`exists_pos_…`, `exists_neg_…`); the eigenvalues `±|c|` of the Gram matrix are not stated.
In (iv), "semisimple" is "the eigenspaces span", the encoding of `WeilConverse.lean`.

**`prop:suspension` (`Suspension.lean`).** `q^ρ = exp(log q · ρ)` (`qpow`). The index set `Idx F q`
is `{ρ : F.HasEigenvalue (q^ρ)}`; no branch of `log` is chosen. `F` is not assumed invertible: since
`q^ρ ≠ 0`, a zero eigenvalue never enters the index set, and for invertible `F` the object is the
manuscript's. `N_α = log(α⁻¹F)` is the series truncated at `k = dim V`, which is the full series
because `α⁻¹F − 1` is nilpotent on `V_{(α)}` of index `≤ dim V_{(α)}`; that the further terms vanish
is not stated as a lemma, and `q^Θ = F` on summands is not proved. In (i), "each zero is simple" is
encoded as a nonvanishing derivative `α (log q) q^{-s}` (`hasDerivAt_one_sub`, `deriv_ne_zero`), not
via `analyticOrderAt` (but the zero order of `1 − α q^{-s}` is computed with `analyticOrderAt` in
`analyticOrderAt_one_sub`). The determinant clause (round 14): `det_one_sub_smul_eq_prod` is
`det(1 − tF) = ∏_α (1 − α t)^{dim V_{(α)}}` for `t ≠ 0`, the product over the roots of the
characteristic polynomial, i.e. the eigenvalues; with `t = q^{-s}`, which never vanishes, this is
the manuscript's identity. A zero eigenvalue (non-invertible `F`) contributes the factor `1`.
"Counted with multiplicity" is `analyticOrderAt_det`: for every `ρ ∈ ℂ` (not only `ρ ∈ spec Θ`),
`analyticOrderAt (s ↦ det(1 − q^{-s}F)) ρ = mult Θ ρ`; for `ρ ∉ spec Θ` both sides are `0`.
In (iii), `ĥ(u, v) = ∑_ρ h(u_ρ, v_ρ)` over the support of `v` (`suspFun`); positive definiteness
of `ĥ` is part of `PosHermForm`, so "positive" in `def:inf-pol` is built into the type of `h`.
"Diagonalizable" in (iv) is "the eigenspaces of `Θ` span `V̂`". The nonvacuity example is the
suspension of `id_ℂ` at `q = 2`, whose spectrum contains `0`.

**`prop:aw4-EF` (ii), `prop:ff-phantom` (ii) on `V̂` (`SuspObject.lean`).** The sheet of
`def:aw4-EF` (b) is the `MultiplicativeForm.lean` one (`σ : ℂ → ℂ` with `σ α ∈ Σ_q(α)` on
eigenvalues), converted by `isSheet_of`. The sheet map `ι_σ u = Σ_α (copy of u_α in V̂_{σ α})`
(`sheetMap`) is the manuscript's, but with codomain `V̂` rather than the sheet space `V̂_σ`; that
`ι_σ` is an isomorphism onto `V̂_σ`, and that `V̂` is the direct sum of the sheet spaces of
`σ + 2πim/log q`, are not stated. `theta_sheetMap` takes `0 < q` (the manuscript's `q > 1` is only
needed for `star_sheetElem`). `ℂ^{S_N}` is `phantomSet q N → ℂ` (functions on the finset) and
`diag(S_N)` is `Matrix.toLin'` of the diagonal matrix (`phantomF`).

**`prop:aw4-EF` (iii) on `V̂` (round 15, `SuspObject.lean`).** `exists_aw4EAdd_suspension` states
(iii) for every `x ∈ V̂`: a submodule `V̂' ∋ x`, finite-dimensional, `Θ`-stable, with an
`AW4EAddDatum` for `Θ|V̂'` (`LinearMap.restrict`). As in `def:aw4-EF`(a), "a subalgebra
`A' ⊂ End_ℂ(V̂')` containing `id` and `θ'`" is encoded as an abstract `*`-algebra with an injective
unital `ι` and `θ' ∈ A'`, `ι θ' = Θ|V̂'`; FAITHFUL up to this (equivalent) encoding. The proof is the
manuscript's: `σ_0 = suspEigen q 0` (a sheet since `F` is invertible by (i)), the shifts
`σ_m = σ_0 + 2πim/log q` for the finitely many `m` met by the support of `x`, `V̂'` the image of
`Fin n → V` under `w ↦ Σ_i ι_{σ_i} w_i` (`sheetSum`, injective by `sheetSum_injective` because the
shifts are distinct at every eigenvalue), and the round 5 `truncation` datum transported along this
isomorphism (`AW4EAddDatum.nonempty_range`). `V̂'` is not literally indexed by `|m| ≤ n` but by the
finite set of shifts met by `x`; both are finite sums of sheet spaces, which is all (iii) asserts.
`sheetMap_injective` gives injectivity of `ι_σ`; round 16 adds the rest of the remark (below).

**Sheet spaces (round 16, `SuspObject.lean`).** FAITHFUL. `sheetSpace hσ` is
`⨆_α range(lof_{σ(α)})`, the submodule `⨁_α V̂_{σ(α)}` of `def:aw4-EF` (c);
`mem_sheetSpace_iff` identifies it with the vectors supported on `{ρ : ρ = σ(q^ρ)}`.
`range_sheetMap` (image of `ι_σ` is `V̂_σ`) with `sheetMap_injective` gives the isomorphism
`sheetEquiv : V ≃ V̂_σ` of the remark; the directness of the sum in (c) is not stated as a separate
`IsInternal` but is implied by this isomorphism with `V = ⨁_α V_{(α)}`. `isSheet_shiftSheet` is
"`σ + 2πim/log q` is a sheet" (`q > 1`; the `Eig F → ℂ` form of round 5's `isSheet_add_int`),
`existsUnique_shift` is "every `ρ` with `q^ρ = α` equals `σ(α) + 2πim/log q` for exactly one `m`",
and `isInternal_sheetSpace` is `V̂ = ⨁_{m∈ℤ} V̂_{σ + 2πim/log q}` (`DirectSum.IsInternal`). The
invertibility of `F` in (b) is implied by the existence of a sheet (as in `prop:susp-converse`).

**`prop:susp-converse` (`SuspConverse.lean`).** A choice `(ρ_α)` is a sheet `σ : Eig F → ℂ` with
`q^{σ α} = α` (`IsSheet`); its existence forces every eigenvalue to be nonzero, so the hypothesis
"`F` invertible" is implied rather than stated. The restricted form is
`h(u, v) = ∑_α ĥ(ι_α u_α, ι_α v_α)` (`restrictedForm`), where `u_α` is the generalized-eigenspace
projection (`genProj`) and `ι_α` places it in the summand `V̂_{σ α}` (`sheetCopy`): the orthogonal
sum of the restrictions of `ĥ` to these summands, *not* the pullback `ĥ(ι u, ι v)`, which would add
cross terms. That `h` is positive definite is proved (it is part of the `PosHermForm` type). The
proof follows the manuscript: `prop:purity` is applied to each finite-dimensional summand
`V̂_ρ` separately (`PosHermForm.isSemisimple` on `Θ − ρ` with weight `j − 2 Re ρ`), which with
nilpotency gives `Θ = ρ` there (`thetaBlock_eq_of_infPol`); `N_{q^ρ} = 0` then gives `F = α` on
`V_{(α)}` by injectivity of the truncated logarithm on nilpotents (`eq_zero_of_logSeries_eq_zero`,
proved by writing the series as `U · (1 + nilpotent)`).

**`prop:kun-tensor` (round 16 mapping, no new code).** PARTIAL. The manuscript label is the Künneth
report's Prop. 5 (the `% claim:` tag). Already formalized: the positivity core of AW4 for the
tensor datum, that `h_a ⊗ h̃_b` is positive definite iff the factors are (up to a common sign)
(`posDef_kronecker_iff`, matrices), and the two ingredients the proof cites for AW3, the block
decomposition of `V^a ⊗ Ṽ^b` (`prop:tensor-eigen`, `isInternal_block_maxGenEigenspace`) and the
support of `B` (`prop:B-support`, `cupTrace_eq_zero_of_mem_maxGenEigenspace`). **Gap** (obligation
14): the tensor datum `D ⊗ D̃` itself (`def:tensor-datum`: the Koszul-signed graded product, the
trace in bidegree `(2d, 2d̃)`, the signed pairing `B(x⊗y, x'⊗y') = (−1)^{|y||x'|} B(x,x') B̃(y,y')`,
the star `* ⊗ *̃`) and the conclusion "Weil datum of type `(d+d̃, 0)` satisfying AW1/AW3/AW4" are not
modelled, since no graded Weil-datum structure with a product exists in the tree.

**`prop:weighted-algebra-obstruction` (round 17, `WeightedAlgebra.lean`).** FAITHFUL, with
weaker hypotheses than the source. `WeightedAlgebraDatum V d w` places the graded pieces `V^j` as
submodules `G j` of one complex space (zero for `j > 2d`); the cup product is a bilinear
`mul : V → V → V` with `V^i ∪ V^k ⊂ V^{i+k}`; `Θ` preserves each `V^j`, is a derivation, and each
`(V^j, Θ|V^j)` is a `Spectral.SpectralCore`; `Tr(Θx) = (d + w) Tr x` on `V^{2d}`; the star `*_j` is an
antilinear map on `V` sending `V^j` into `V^{2d-j}` with `Θ *_j v = *_j Θ v + (d − j) *_j v` for
`v ∈ V^j`; `h_j(u, v) = Tr(u ∪ *_j v)` is Hermitian and positive definite on `V^j`. Not assumed
(the proof does not need them, so the theorem is stronger): associativity, a unit (except in the
second claim), and that the `V^j` span `V`. `eq_bot` is the first claim. `eq_zero_of_unit` is the
second: a unit `1 ∈ V^0` with `1 ∪ x = x` for all `x` and `V ≠ 0` gives `w = 0`. The source's "unit
of the algebra" is taken to lie in degree zero, and only the left unit law is used. The proof
deduces the second claim from the first rather than via `Θ1 = 0`; the statements are as in the
source. Only spanning by generalized eigenspaces is used from the spectral-core hypothesis.

**`prop:R5`, `prop:bsd-positive-gap`, `prop:bsd-jordan-gap` (round 18, `LinearGaps.lean`).**
`isEmpty_antihom`: FAITHFUL. A unital ring antihomomorphism `ℍ → M₂(ℝ)` is encoded as a
`RingHom` into the opposite ring `(Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ` (Mathlib's `RingHom` is unital);
`ℍ` is `Quaternion ℝ`. The proof differs from the manuscript's (which builds `ℍ ≅ M₂(ℝ)` and uses
a nilpotent): `not_anticomm` shows directly that no real `X, Y` satisfy `X² = Y² = -1`,
`YX = -XY`, using only the `(0,0)` entries and Lagrange's identity. `bsd_positive_gap`: FAITHFUL;
"positive Hermitian space" is a finite-dimensional complex `InnerProductSpace` (bundled in the
existential, `V : Type`), `Θ* ` is `LinearMap.adjoint`, the isometric injection is a
`LinearIsometry` landing in `ker(Θ - 1)`; the witness is the source's (`ℂ^{r+k}`, `Θ = 1`, first
`r` coordinates). The hypothesis `0 < k` is kept as in the source though unused.
`prop:bsd-jordan-gap`: FAITHFUL with one encoding choice: `ord_{s=1} det(s - J)` is the root
multiplicity of `1` in `charpoly J = det(X - J)` (a polynomial, so this equals the analytic order);
`J` is over `ℂ`, `ker(J - 1)` is the kernel of `toLin' (J - 1)`.
`prop:one-branch` was done in round 24 without its determinant clause, which needs `detreg`
(`def:regdet`, obligation 1).

**`prop:R2-star`, `prop:bsd-coefficient-gap`, `prop:bsd-primary-gap`, `prop:R11`, `prop:R14`
(round 19, `Negative.lean`, `ElementaryGaps.lean`).** `prop:R2-star` (i)–(ii) were already
formalized as the `J₊` row (round 1); (iii) `not_exists_posStar`: FAITHFUL. An antilinear map is a
`(Fin 4 → ℂ) →ₗ⋆[ℂ] (Fin 4 → ℂ)`; `B(v, w) = vᵀΩw` as in `def:R2-block`; "positive definite
Hermitian" is the pair `h'(w, v) = conj h'(v, w)` and `0 < h'(v, v)` for `v ≠ 0` (in `ℂ`'s order,
so `h'(v, v)` is real). The Hermitian clause is unused by the proof, which follows the source
((P) for `h'`, then `Re λ = 1/2` on the eigenvector `e₁`, contradicting `lam_re_ne`); only
`a ≠ 0` is assumed. `bsd_coefficient_gap`: FAITHFUL; "leading coefficient" is Mathlib's
`meromorphicTrailingCoeffAt` at `1` and "same divisor" is `MeromorphicOn.divisor` equality on an
arbitrary `U`. `lattice_gap`: FAITHFUL; lattices are `ℤ`-spans in `ℝ`, Gram determinants are
`Matrix.gram` of the one-element bases. `bsd-primary-gap`: FAITHFUL; `G[ℓ^∞]` is
`AddCommMonoid.primaryComponent G ℓ`, the index set is `{ℓ : ℕ // ℓ.Prime}`. `prop:R11` (i):
FAITHFUL; `P` is a real polynomial mapped to `ℂ[X]`, the zero set is stated as an iff with the
four points `±T ± ia`, and "not real" is `Im ≠ 0` for `a > 0`. (ii): FAITHFUL; `P'` is
`Polynomial.derivative`. (iii): done in round 21 (see its note below). (iv) not attempted (it is
about entire functions). `prop:R14` (i): FAITHFUL and slightly more general: completeness of `H` is not
used; a rank-one orthogonal projection is `K.starProjection` with `finrank K = 1` (the instance
`FiniteDimensional ℂ K` is implied by that). (ii): FAITHFUL, the source's witness `Q = ε` on `ℂ`.
(iii)–(iv): done in round 20, see below.
**`prop:R14` (iii)–(iv) and the `w = 0` model (round 20, `ElementaryGaps.lean`,
`WeightedAlgebra.lean`).** `prop:R14` (iii): FAITHFUL. `f ∈ C_c(ℝ)` with `supp f ⊆ [-ℓ, ℓ]` is
`Continuous f` with `tsupport f ⊆ Icc (-ℓ) ℓ` (compact support follows); `c_f` is the Bochner
integral `∫ f(y) conj(f(y - x)) dy`; "f real" is `(f y).im = 0`; "`c_f(x) > 0`" is `0 < c_f x` in the
order of `ℂ` (real and positive). The hypothesis `ℓ > 0` is not needed. (iv): FAITHFUL; the
second claim's witness is the source's tent `max(0, ℓ - |t|)`, and the existential also records that
it is real and positive on `(-ℓ, ℓ)`; the hypotheses `ℓ > 0` (first claim) and `ℓ > ½ log 2`
(second claim) are kept as in the source but not used (for `ℓ ≤ ½ log 2` the second claim is
vacuous). `trivialModel`: `V = ℂ`, `d = 0`, `G 0 = ⊤`, `Θ = 0`, `Tr = id`, `*_j = conj`; each
`V^j` is a spectral core because it is finite-dimensional. It shows the structure is satisfiable
and that `eq_zero_of_unit` is sharp (a nonzero unital datum with `w = 0` exists).
`prop:aw4-forms` and `prop:aw5-contains` were not attempted in round 19 (later: `aw4-forms` (i)–(ii)
in rounds 22–23 and (iii) in round 25, `aw5-contains` (i)–(ii) in round 24): (i)–(ii) of `aw4-forms`
need a positive polarization on all of `V^j` assembled from the local AW4-E data (and conversely
an algebra with positive trace from a polarization), and `aw5-contains` (iii) needs the Hilbert
completion `𝓗^j` (obligation 14 / `prop:hilbert`).

**Weighted rows after the type-`(d, 0)` repair (round 21 recheck).** The manuscript's uncommitted
"weighted-axiom-repair" edits restrict `def:aw`, `def:weil-cohomology`, `prop:polarization-identity`,
`def:aw4-forms` and `prop:aw4-forms` to Weil data of type `(d, 0)`: trace into `ℂ(-d)`, star forms of
weight `j`. Row by row:
- `prop:polarization-identity`: FAITHFUL. `WeightedStarDatum.polarization_identity` is the stated
  `(d, 0)` form, `h_j(Θu, v) + h_j(u, Θv) = j h_j(u, v)`, derived from the general-`w`
  `derivation_law`; the general statement is kept.
- Q1-L4.2 (`WeightedStarDatum`, `derivation_law`, `re_eq_of_hasEigenvalue`, `isSemisimple`): FAITHFUL to
  Q1 Lemma 4.2 / Theorem 0 (type `(d, w)`, `w ∈ ℕ`), the row's source. Relative to the manuscript it
  is a generalization: `def:aw` is the case `w = 0`. `lineModel` already has type `(1, 0)`, and
  `SurfaceDatum.toWeightedStarDatum` type `(1, 0, 1)`, so both are instances of the repaired
  definition.
- `prop:weighted-algebra-obstruction`: FAITHFUL and unaffected. The source still takes `w ∈ ℝ` and
  trace weight `d + w`, as `WeightedAlgebraDatum V d w` (`w : ℝ`) does.
- `def:graded-realization`: unaffected; the source keeps `w ∈ ℝ` and weight `w + j`. No declaration
  cites it.
- `def:aw4-forms`, `prop:aw4-forms`: encoded in round 22 at weight `j` (`θ^† = j − θ`), see the
  round 22 note.
- `prop:B-support`: unaffected. `cupTrace_eq_zero_of_mem_maxGenEigenspace` takes the trace weight `n`
  as a parameter; the repaired `def:aw` is `n = d`.

**`prop:kun-Fq-C` (round 21, `KunFq.lean`).** FAITHFUL, with weaker hypotheses: the source's
`V, W ≠ 0` and `F, G` invertible are not needed (a zero eigenvalue never indexes a summand of
`V̂`). "Infinite-dimensional" is `¬ Module.Finite ℂ`. The proof is the source's: a nonzero block
`V̂_{ρ₁} ⊗ Ŵ_{ρ₂}` (`block_ne_bot`) gives the nonzero blocks at `(ρ₁ + 2πik/log q, ρ₂ − 2πik/log q)`
(`qpow_add_shift`), which are independent inside the generalized eigenspace
(`isInternal_block_maxGenEigenspace`), so a finite-dimensional eigenspace could hold only finitely
many. The core is stated for abstract spectral cores whose spectra are shift-stable
(`maxGenEigenspace_eq_bot_or_infinite_of_shift`). `thm:kun-Fq` was not attempted: (i) needs the
tensor product over the periodic unit `𝟙_q` (`def:flow-module` (e)), a quotient of `V̂ ⊗_ℂ Ŵ` by the
periodicity relations, which is not modelled, and (ii) needs étale cohomology of varieties over `𝔽_q`.

**`prop:R11` (iii) (round 21, `ElementaryGaps.lean`).** FAITHFUL. `im_neg_logDeriv_value` is the
displayed value at `z = 2 + i/8` for `T = 2`, `a = 1/4`, computed from the four-term expansion
`neg_logDeriv_eq`. In `norm_hb_lt` the HB companion of `def:hb` is written out: `E_P(z) = P(z) + iP'(z)`
and `E_P^#(z) = P(z) − iP'(z)`, which is the source's own identification `E_P^# = P − iP'` (from
`P^# = P`, real coefficients); `def:hb` itself is not encoded. The inequality comes from
`|x + iy|² − |x − iy|² = 4|x|² Im(−y/x)` (`norm_add_I_mul_lt`). (iv) is not formalized.

**`prop:kun-orbits` (round 22, `KunOrbits.lean`).** `𝟙_p` (`def:unit` (b)) is encoded as the
logarithmic suspension of `(ℂ, 1)`, the identification of `prop:unit` that the source's proof of (i)
uses. This is the same object, not a substitute: `SuspSpace 1 p` has one copy of `ℂ` exactly at
each `ρ` with `p^ρ = 1`, i.e. at `ρ = 2πik/log p` (`mem_spec_unit_iff`, `mult_unit`), and
`Θ = ρ` there because `N = log 1 = 0`; the multiplication `v^n v^m = v^{n+m}` is not used by (i)–(iii)
and is not encoded. "Eigenvalue" and "multiplicity" are read as in `def:spectral-core` (c):
generalized eigenspace and its dimension (`Θ` is diagonal here, so they agree).
- (i) FAITHFUL. Nonzero and `¬ Module.Finite` for every `k`; the proof is the source's, via
  `prop:kun-Fq-C`.
- (ii) FAITHFUL. Primes are `ℕ` primes, `𝟙_p` uses `q = (p : ℝ)`. The statement lists: the spectrum
  is exactly `{2πi(m/log p + n/log p')}`; `(m, n) ↦` eigenvalue is injective; each generalized
  eigenspace is finite-dimensional of dimension `1` ("simple"); and "dense in `iℝ`" is encoded as
  real part `0` plus density of the imaginary parts in `ℝ`. Unique factorization is
  `int_mul_log_eq`; density uses Mathlib's `dense_addSubgroupClosure_pair_iff` (closure of `{a, b}`
  dense iff `a/b` irrational), as the source argues via `ℤ + θℤ` with `θ` irrational.
- (iii) FAITHFUL (round 25). `kurokawaCone Θ` is `def:kurokawa-cone` verbatim: the sum of the
  blocks `V_{Θ∼ρ} ⊗ V_{Θ∼ρ'}` with `Im ρ · Im ρ' ≥ 0`; it is `Θ`-stable (`mapsTo_kurokawaCone`).
  "The eigenvalue `2πik/log p` has multiplicity `|k| + 1` on the cone" is stated as
  `Module.Finite` and `finrank = |k| + 1` for `cone ⊓ (𝟙_p ⊗ 𝟙_p)_{Θ∼2πik/log p}`;
  `finrank_maxGenEigenspace_restrict` proves (for any `Θ`-stable subspace) that this meet has the
  dimension of the generalized eigenspace of `Θ` restricted to the subspace. The restricted
  operator is not written out for `𝟙_p ⊗ 𝟙_p` itself because instance search does not find
  `AddCommGroup` on submodules of a tensor product of two `SuspSpace`s (the round 21 issue); the
  generic lemma covers it. Proof: the meet of two partial sums of an internal direct sum is the
  sum over the intersection (`biSup_inf_biSup_of_isInternal`), the cone pairs over `2πik/log p`
  are the `(2πim/log p, 2πin/log p)` with `m + n = k`, `mn ≥ 0` (`cone_pairs`), each block is
  one-dimensional, and `card_cone` counts them, which is the source's proof.

**`def:aw4-forms`, `prop:aw4-forms` (i) (round 22, `AW4Forms.lean`).** The definition is stated in
the source for a Weil datum of type `(d, 0)` in degree `j`, but (a) and (b) only involve
`(V^j, Θ_j)`; `AW4V Θ j` and `AW4E Θ j` are stated for one endomorphism `Θ` of a complex space and
real `j`, so the Lean definitions apply to the degree-`j` piece of any datum. Weight is `j`, per the
type-`(d, 0)` repair. (b) reuses the round-5 `AW4EAddDatum` (abstract `*`-algebra acting faithfully
and unitally, equivalent to a subalgebra of `End(V')` containing `id`, `θ`).
- (i) FAITHFUL. Diagonalizable on every generalized eigenspace is
  `maxGenEigenspace ρ = eigenspace ρ`; `Re ρ = j/2` for every eigenvalue; AW4-V in degree `j`. The
  proof follows the source: semisimplicity and purity on each `V'` (round 5's
  `AW4EAddDatum.isSemisimple`, `.re_eq_half`), hence `V = ⨁ ker(Θ − ρ)`, and `h` is the coordinate
  form of a basis of eigenvectors (`PosHermForm.ofBasis`), an orthogonal sum of positive definite
  forms on the eigenspaces. No spectral-core hypothesis (finite-dimensional eigenspaces) is needed,
  since `ofBasis` works for any basis.
- (ii) FAITHFUL (round 23, `aw4E_of_aw4V`), with the source's standing hypothesis that `(V^j, Θ_j)`
  is a spectral core made explicit (`Spectral.SpectralCore Θ`; only spanning and finite-dimensional
  generalized eigenspaces are used). As in the source, `V'` is a finite sum of generalized
  eigenspaces, `A_{V'} = End_ℂ(V')`, `τ` the trace and `†` the `h|_{V'}`-adjoint; Lean realizes
  `End_ℂ(V')` as `Matrix n n ℂ` through `LinearMap.toMatrixOrthonormal` in an orthonormal basis of
  `HSpace h` (`V'` with `⟪u, v⟫ = h(v, u)`), so `†` is `ᴴ` and the positive trace is round 3's
  `matrixTrace`. `θ^† = j − θ` is `IsInfPol` read as an adjoint identity.
- (iii) not formalized (obligation 16).

**`prop:kun-torus` (round 23, `KunTorus.lean`).** `𝕋 = AddCircle a × AddCircle b`,
`φ^t(x, y) = (x + t, y + t)`, "`x ∈ ℚ`" is `x ∈ Set.range ((↑) : ℚ → ℝ)`.
- (i) FAITHFUL; "no periodic orbit" is `φ^t z = z → t = 0`. The hypothesis `a, b > 0` is not
  needed.
- (ii) FAITHFUL. "Every orbit is closed" is `∃ t > 0, φ^t z = z`; "not isolated among closed
  orbits" is: every neighbourhood of `z` contains a point `w` with a closed orbit and
  `w ∉ orbit(z)`. The proof differs from the source's in one step: instead of the finite set
  `{(x, y + ma)}`, the bad `s` with `(x, y + s) ∈ orbit(z)` lie in the countable set `aℤ + bℤ`,
  which has Lebesgue measure zero, so it cannot contain an interval `(0, ε)`.
- (iii) FAITHFUL, from round 22's `int_mul_log_eq`.

**`prop:one-branch` (round 24, `OneBranch.lean`).** `(V, Θ) = (ℂ, ρ₀ • 1)`; the spectral divisor is
`ρ ↦ mult Θ ρ` and the divisor of `1 − α q^{-s}` is the indicator of `Σ_q(α)` (all its zeros are
simple, round 12). FAITHFUL for the spectral-core, divisor and infinitude clauses; the hypothesis
`α ∈ ℂ^×` is implied by `ρ₀ ∈ Σ_q(α)`. The clause `detreg((s − Θ)/2π) = (s − ρ₀)/2π` is not
formalized (obligation 1); what is proved is that `(s − ρ₀)/2π` is not of the form `g(q^{-s})`,
which is the "not a function of `q^{-s}`" half of that clause.

**`prop:aw4-forms` (iii) (round 25, `AW4Star.lean`).** FAITHFUL, stated degree by degree for
the slice `V = V^j`, `W = V^{2d-j}`, `T = V^{2d}` of a type-`(d, 0)` datum (the `WeightedStarDatum`
slice with `w = 0`); the source's construction of `*'_j` is also degree by degree, so "in every
degree" is the conjunction over `j`. Hypotheses: the derivation rule of AW1
(`ΘT (u ∪ v) = Θ_j u ∪ v + u ∪ Θ_{2d-j} v`), AW3 trace equivariance `Tr(ΘT x) = d Tr x`, AW3
perfectness of `B = Tr(· ∪ ·)` on `V^j_{Θ∼ρ} × V^{2d-j}_{Θ∼d-ρ}` (encoded as bijectivity of
`blockPairing ρ (d − ρ) : V^{2d-j}_{Θ∼d-ρ} → (V^j_{Θ∼ρ})^*`, the source's Remark rem:aw-comments
reading), `(V^j, Θ_j)` a spectral core (standing), and AW4-V in degree `j` (`IsInfPol h Θ_j j`).
Conclusion: an antilinear `*' : V^j → V^{2d-j}` (`V →ₗ⋆[ℂ] W`) with the AW4 star law
`Θ_{2d-j} *' = *' Θ_j + (d − j) *'` and star form `Tr(u ∪ *'v) = h(u, v)`; positivity of the star
form is then that of `h`. `exists_weightedStarDatum` packages this as a `WeightedStarDatum d 0 j`
with the given `Θ`'s, `∪` and `Tr` and `D.h = h`. The proof is the source's: purity
(`aw4E_of_aw4V`, `prop:aw4-forms` (i)) splits `V^j` into eigenspaces, `*'v` for `v` in the
`ρ`-eigenspace is the preimage under `blockPairing` of `u ↦ h(u, v)`, B-support
(`cupTrace_eq_zero_of_mem_maxGenEigenspace`) and `h`-orthogonality (`toFun_eq_zero_of_ne`) give
`Tr(u ∪ *'v) = h(u, v)` for all `u`, and perfectness gives the star law, `Θ_{2d-j}` acting by
`d − ρ` on the image of the `ρ`-eigenspace. Only the derivation rule of AW1 is used (as the source
says), and AW2, AW5 and the other degrees are not involved.

**`prop:aw5-contains` (round 24, `AW5Contains.lean`).** Stated for the degree-`j` piece
`(V^j, Θ_j, h_j)` of a type-`(d, 0)` datum, as `def:aw4-forms` was.
- AW5 is encoded on the core only (`AW5Local`): on every finite-dimensional `Θ`-stable `W ⊆ V`,
  `t ↦ exp(t(Θ|_W − j/2))` is isometric for `h|_W` (as a continuous linear map on `HSpace`). This
  is the restriction to `V^j` of the unitarity of `U_j(t) = e^{-jt/2} φ^t`, using that `φ^t` is
  `e^{tΘ}` on such `W`; the completion `𝓗^j`, strong continuity, skew-adjointness and the core
  clause are not encoded, since the proof of (i) uses only this restriction. The theorem is
  therefore stronger than the source's.
- (i) FAITHFUL. It assumes every vector lies in a finite-dimensional `Θ`-stable subspace
  (`LocFin`), as the source's proof does; a spectral core has this property
  (`locFin_of_spectralCore`). The proof is the source's: differentiate at `t = 0`, then polarize.
- (ii) FAITHFUL, with the standing spectral-core hypothesis; "diagonalizable" is
  `⨆ ρ, eigenspace ρ = ⊤`.
- (iii)–(iv) not formalized (they need `𝓗^j` and `prop:hilbert`; obligation 17).

**`prop:hilbert` (round 26, `Hilbert.lean`).** PARTIAL.
- `Completion h` is `UniformSpace.Completion` of `HSpace h`, i.e. of `V` with `⟪u, v⟫ = h(v, u)`;
  it is a complex Hilbert space by Mathlib's instances. This is the source's "Hilbert-space
  completion of `(V, h)`".
- Basis clause FAITHFUL (`exists_hilbertBasis`): a `HilbertBasis ι ℂ 𝓗` whose `k`-th vector is the
  image of `e_k ∈ V` with `Θ e_k = (j/2 + iτ_k) e_k`, `τ_k ∈ ℝ`. The proof is the source's:
  orthonormal bases of the finite-dimensional eigenspaces, mutually orthogonal
  (`inner_eq_zero_of_ne`), span `V`, and `V` is dense in `𝓗`.
- `Θ = j/2 + iT` on `V` FAITHFUL (`theta_eq`), with `T = -i(Θ - j/2)` defined on `V`;
  `T e_k = τ_k e_k` (`T_apply_of_eq`) identifies it with `diag(τ_k)` on `V`, and `T_symm` is the
  source's "`T` is symmetric on its domain" for the domain `V`.
- Round 33 (`HilbertSelfAdjoint.lean`): `def:diag-op` FAITHFUL. `Diag.op b τ` has exactly the
  source's domain `{Σ c_k e_k : Σ |τ_k c_k|² < ∞}` (coefficients `c_k = ⟪b_k, x⟫`) and acts by
  `Σ τ_k c_k e_k`. Self-adjointness FAITHFUL: `IsSelfAdjoint (Diag.op b τ)` is Mathlib's
  `T^† = T` for `LinearPMap`, proved by the source's argument (symmetry gives `T ≤ T^†`; testing
  `T^† y` against `e_k` gives `z_k = τ_k y_k`, so `T^† ≤ T`). `exists_selfAdjoint` packages it with
  the basis clause and states `T = diag(τ_k)` extends `-i(Θ - j/2)` on `V` (the image of `V` lies in
  the domain).
- Round 37: spectral clause FAITHFUL (`exists_spectral`). Mathlib has no spectrum for unbounded
  operators, so "pure point spectrum `{τ_k}`" is stated by its content for a closed operator:
  every `τ_k` is an eigenvalue (`T b_k = τ_k b_k`), and for `μ ∉ {τ_k}` the map `T - μ` from the
  domain of `T` to `𝓗` is bijective (`existsUnique_sub_smul_eq`; the inverse is then bounded by the
  closed graph theorem, and the proof gives the explicit gap). "Finite multiplicities": every
  eigenvector for `μ` lies in the span of the finitely many `b_k` with `τ_k = μ`
  (`mem_span_of_op_eq_smul`). "No finite accumulation": `{τ_k}` has no accumulation point in `ℂ`.
  The finiteness and discreteness of `{τ_k}` are derived from the spectral core
  (`fin_disc_of_basis`), not assumed. Since `{τ_k}` is closed, it is the whole spectrum.

**`prop:R2-frob`, `prop:R17`, `prop:kun-cone` (ii), `prop:R7` (round 27, `Negative.lean`,
`ElementaryGaps.lean`, `KunOrbits.lean`, `LocalCores.lean`).**
- `prop:R2-frob`: FAITHFUL and slightly more general. `J` is `v ↦ S v̄` as in the existing R2 rows,
  so `F J = J F` is `F S = S F̄` (`F_mul_S`) and `J² = -1` is `S S̄ = -1` (`quaternionic`). The
  source's `0 < a < 1/2`, `T > 0`, `q > 1` are relaxed to `0 < q` (no condition on `a`, `T`).
  "The eigenvalues have moduli `q^{1/2+a}` and `q^{1/2-a}`" is stated both ways: every eigenvalue
  of `toLin' F` has one of the two moduli, and each modulus occurs.
- `prop:R17` (i): FAITHFUL. `S_t` is a function `ℂ → ℂ` used only on `Ω`; `ψ` is complex-valued
  (covers real `ψ`); the reflection is `reflect f z = conj (f (conj z))` (`def:hb`). The hypotheses
  `Ω̄ = Ω`, local integrability, smoothness and compact support are kept as in the source but the
  proof only uses evenness of `S` and `ψ` (the integrand is odd; the Bochner integral of a
  non-integrable function is `0`, so no integrability is needed). (ii): FAITHFUL; `bump` is the
  source's piecewise formula, `bump_eq` identifies it with `expNegInvGlue (1 - t²)`, and
  `bump_spec` gives `C^∞`, compact support, evenness, `ψ₀(0) = e^{-1}` and `ψ₀ ≠ 0`.
- `prop:kun-cone` (ii): PARTIAL. Stated for any spectral core `(V, Θ)` on `V ⊗ V` rather than
  `V_K` of `thm:kun-square` (not modelled); `⨁_ρ V_ρ ⊗ V_{1-ρ}` is `⨆ ρ, block Θ Θ ρ (1 - ρ)`, and
  "`Z(K) ∩ ℝ` is finite" becomes the hypothesis that `spec Θ` has finitely many real points. (i)
  needs the surface algebra `H^•` and `κ` and is not formalized.
- `def:R7-local`, `prop:R7` (rounds 27–28): FAITHFUL. The local core `V_p` is
  `KunOrbits.unitTheta p` (the suspension of `(ℂ, 1)` at `q = p`, as `def:R7-local` says), and
  `V_𝒬` is the `DirectSum` over the subtype `𝒬 : Set ℕ` with `Θ_𝒬 = Suspension.diag`; the
  primality of the members of `𝒬` is the hypothesis `∀ p ∈ 𝒬, p.Prime`. Nonemptiness of `𝒬` is not
  needed. (i): the zeros of `1 - p^{-s}` are `Suspension.mem_logSusp_iff_zero` with `α = 1`;
  "eigenvalues" is `spec` (generalized eigenvalues, which coincide here); "multiplicity `#𝒬`" is
  `Module.rank` of the generalized `0`-eigenspace equal to `Cardinal.mk 𝒬`, so it covers infinite
  `𝒬`, with the `finrank` form `mult_zero` for finite `𝒬`; "simple" is `mult = 1`. (ii) follows
  from (i) as in the source. (iii) gives `ξ ≠ 0` on all of `Re s = 0` (from `ξ(1 - s) = ξ(s)` and
  `ζ ≠ 0` on `Re s = 1`), for each `V_p` and for `V_𝒬`. (iv) is FAITHFUL, with `‖·‖` for `|·|` and the
  source's hypothesis `p^s ≠ 1` for every prime.

**`def:trivial-model`, `prop:trivial-model` (round 29, `TrivialModel.lean`).**
- Encoding: `Σ` is a family `ρ : ι → ℂ` of designated first members, one per pair `(e_p, f_p)`
  (`e_p = (p, true)` with eigenvalue `ρ_p`, `f_p = (p, false)` with `1 - ρ_p`); a pair at `1/2` is a
  `p` with `ρ_p = 1/2`. Every divisor of `def:trivial-model` arises this way, and symmetry under
  `ρ ↦ 1 - ρ` and evenness of `m(1/2)` hold by construction. The multiplicity of `σ` in `Σ` is
  `#{i // lam ρ i = σ}`; the source's "finite multiplicities, no finite accumulation" are the
  hypotheses of `spectralCore_theta` only.
- Only the degree-one slice is modelled, as a `WeightedStarDatum 1 0 1 V^1 V^1 ℂ` with
  `V^2 = ℂη ≅ ℂ`, `u ∪ v = B(u, v) η`, `Θ_2 = 1`, `Tr = id`. Not modelled: `V^0`, the products
  involving `V^0`, `*_0`, `*_2` and their star laws, associativity and graded-commutativity of the
  full product (`B` is alternating on basis vectors, `B_e_f`, but `B u u = 0` is not stated).
- (i): PARTIAL. AW1 for `U = 𝟙` is the derivation rule in bidegree `(1, 1)` (`B_theta`); AW3 is the
  trace law `Tr(Θ_2 x) = Tr x` and nondegeneracy of `B` (`B_nondegenerate`), not the blockwise
  perfectness `V^1_ρ × V^1_{1-ρ}`. `Sp_1 = Σ` is FAITHFUL: equality of all multiplicities as
  cardinals (`rank_maxGenEigenspace_theta`) and of supports (`spec_theta`).
- (ii): FAITHFUL for degree one. The star law with `d = j = 1` is `star_comm` of `model`
  (`theta_starLine`); AW4 positivity is `WeightedStarDatum.IsPositive` (`h_1` Hermitian, positive
  definite), and `h_1` is the standard form in the basis (`h_eq_sum`).
- (iii): FAITHFUL for degree-one data. "Some Weil datum with `Sp_1 = Σ` satisfying AW1, AW3 and
  AW4" is a `WeightedStarDatum 1 0 1 V W T` (types in `Type`) with `IsPositive` and the multiplicity
  condition; (⇐) is the model, (⇒) is `WeightedStarDatum.re_eq_half_of_curve` (the source's route
  through `prop:polarization-identity` and `prop:purity`).

**`def:trivial-model`, `prop:trivial-model` in degrees `0`, `2` (round 32, `TrivialModelFull.lean`).**
- Degrees `0` and `2` are the slices `model0` (`j = 0`: `V = V^0 = ℂ`, `W = V^2 = ℂ`) and `model2`
  (`j = 2`) of `WeightedStarDatum`, with the unit products, `Θ_0 = 0`, `Θ_2 = 1`, `Tr = id`,
  `*_0 = *_2 = conj`. The star laws `Θ_2*_0 = *_0Θ_0 + *_0` and `Θ_0*_2 = *_2Θ_2 - *_2` are the
  fields `star_comm`; `h_0(c, c') = h_2(cη, c'η) = cc̄'` positive. FAITHFUL.
- The full product is `mul` on `Tot = ℂ × V^1 × ℂ`,
  `(a, u, c)(a', u', c') = (aa', au' + a'u, ac' + ca' + B(u, u'))`, which is exactly "`u ∪ v = B(u,v)η`
  on `V^1` and the unit products otherwise" (products landing in degree `≥ 3` vanish). Associativity,
  unit and the derivation rule are proved for all elements; graded commutativity is stated as
  `y ∪ x = x ∪ y` with the sign of the `V^1 × V^1` term flipped (`mul_comm_graded`), and in bidegree
  `(1, 1)` as `u ∪ u' = -(u' ∪ u)` (`mul_anticomm_one`). FAITHFUL. `B` is alternating on all of
  `V^1` (`B_antisymm`), not only on basis vectors.
- AW3 perfectness: FAITHFUL under finite multiplicities. `blockPairing_bijective` is the bijectivity
  of `V^1_{Θ∼1-σ} → (V^1_{Θ∼σ})^*` (the round-25 `AW4Star.blockPairing` encoding) for every `σ`,
  assuming every multiplicity of `Σ` finite; the source assumes this through "spectral core"
  (with infinite multiplicity the dual is larger and bijectivity fails). Degrees `0`/`2`:
  `blockPairing_zero_bijective`, for every `σ` (both blocks are `0` unless `σ = 0`).
- Not encoded: AW1's isomorphisms of spectral cores `V^0 ≅ U = 𝟙` and `V^2 ≅ U(-1)`; here `V^0`
  and `V^2` are literally `ℂ` with `Θ = 0` and `Θ = 1`, and `𝟙` with multiplication is not a
  separate object in the tree. The model is not packaged as one structure carrying all degrees
  (there is no graded Weil-datum structure in the tree); it is the three slices, `Tot` and `mul`.


**`def:trivial-model` as one graded datum; `def:aw4-EF` (a) instance (round 35).**
- `TrivialModel.gradedModel` FAITHFUL for finite `Σ` on `Re s = 1/2`: the grading, product
  `u ∪ v = B(u, v)η`, flow `(0, Θ_1, 1)`, trace `cη ↦ c` (weight `d + w = 1`), stars
  `*_0 = conj·η`, `*_1 = starLine`, `*_2 = conj` and positivity of `h_0, h_1, h_2` are those of
  `def:trivial-model`, now checked against every field of `WeightedAlgebraDatum` at once. Finite `ι`
  is a restriction (the spectral-core field is discharged by finite-dimensionality); the line
  hypothesis is necessary (`exists_datum_iff`).
- `deg0Equiv_unit`, `deg2Equiv_twist` FAITHFUL for AW1's `V^0 ≅ 𝟙`, `V^2 ≅ 𝟙(-1)` with `𝟙 = (ℂ, 0)`
  and `𝟙(-1) = (ℂ, 1)`; the isomorphisms are stated componentwise (unit, multiplication, flow,
  trace), not as morphisms in a category of spectral cores.
- `AW4EFDatum.scalarModel` FAITHFUL to `def:aw4-EF` (a): `A = ι(M_n(ℂ)) = End(ℂ^n)` contains `id`
  and `F`, `(τ, †) = (trace, ᴴ)` is a positive trace involution, `F F^† = q^j`.
  `exists_nontrivial` only records that such a datum exists on a nonzero space.

**Round 36: infinite trivial model, indefinite graded datum, weight placement.**
- `TrivialModel.gradedModelInf` FAITHFUL to `def:trivial-model` for any divisor allowed by
  `prop:trivial-model` (i) (finite multiplicities, no finite accumulation point) on `Re s = 1/2`;
  the finiteness restriction of round 35 is gone.
- `HermAlgebraDatum` is `WeightedAlgebraDatum` with positivity replaced by nondegeneracy (every
  nonzero `u ∈ V^j` has `v ∈ V^j` with `h_j(u, v) ≠ 0`). `ContentAssembly.gradedDatum` FAITHFUL to
  `prop:content` (iii) in all degrees for a **finite** divisor; for infinite divisors
  `PairingModel.gradedDatum` takes the degree-one spectral-core condition as a hypothesis (no
  spectral-core lemma for general block data is proved).
- `form_identity_sub` FAITHFUL to the remark's display `h_j(Θu, v) + h_j(u, Θv) = (τ - κ_j) h_j(u, v)`
  (stated for one pairing, with complex `τ`, `κ`); `derivation_unit_eq_zero` FAITHFUL ("a derivation
  of a unital algebra kills its unit"); `trace_weight_eq_shift_of_unit` is the remark's conclusion
  in degree `0` ("the unit argument applies unchanged"), assuming `h_0(1, 1) ≠ 0`, which positivity
  gives.

**Round 37: block data spectral core, `prop:hilbert` spectral clause.**
- `PairingModel.spectralCore_theta` FAITHFUL: the source's hypotheses on the divisor (finite
  multiplicities, no finite accumulation point) give the spectral-core condition in degree one.
  `ContentAssembly.gradedDatumInf` is therefore FAITHFUL to `prop:content` (iii) in all degrees for
  every divisor of the shape `def:trivial-model` allows, not only finite ones. The hypotheses are
  stated on `lamX` (the list of values with repetition), which is how the divisor enters.
- `prop:hilbert` spectral clause: see the `prop:hilbert` note above.
**Round 38: units (`Unit.lean`).**
- `def:unit` (a), (c): FAITHFUL. `𝟙` is `(ℂ, 0)` with the multiplication of `ℂ`; `U(-k)` is
  `Θ_U + k`. That `𝟙` is a unit for the tensor of spectral cores is not stated in `def:unit`; it is the
  property the per-object unit `U_X` of `ax:F1` / `def:deninger-structure` needs, proved here with `TensorProduct.rid`.
- `def:unit` (b): FAITHFUL. `𝟙_q = ⨁_{n∈ℤ} ℂ vⁿ` is encoded as `AddMonoidAlgebra ℂ ℤ` (Laurent
  polynomials, the algebraic direct sum), `vⁿ = single n 1`; `Θ` is defined on coordinates through
  `⨁_{n∈ℤ} ℂ`, and `periodicTheta_single` is the source's `Θ vⁿ = (2πin/log q) vⁿ`.
- `prop:unit`: the spectrum clause and "not isomorphic to `𝟙`" are FAITHFUL for `𝟙_q` itself. The
  isomorphism `V̂⁰ ≅ 𝟙_q` *with its product* is not stated on the suspension (`KunOrbits.unitSpace`),
  because the suspended datum's product (`def:susp-datum`, `prop:susp-product`) is not modelled
  (obligation 13); round 22 already identifies `V̂⁰`'s spectrum. The determinant clause
  `det = 1 - q^{-s}` is `thm:ff-det`/`Suspension.det_one_sub_smul_eq_prod` with `F = 1`.

**Round 39: `prop:algebra-form`, `prop:R10`, `prop:bsd-spectral-rank`, `prop:bsd-picard-gap`.**
- `prop:algebra-form`: (i) and (ii) FAITHFUL over `k = ℂ`. (i) is round 3's Q2-T1′. (ii) does not
  need injectivity of `ι`; "diagonalizable" is given both as `IsSemisimple` and as "the eigenspaces
  span `V`". **Gap:** `k = ℚ, ℝ` (base change `A ⊗_k ℂ` and positivity of the Hermitian extension of
  `S`), as before.
- `prop:R10`: FAITHFUL, with one encoding. "Separable infinite-dimensional" is a Hilbert basis
  indexed by `ℕ` (`HilbertBasis ℕ ℂ H`), which such a space has and which the source's proof chooses
  first; Mathlib's route from separability to a countable Hilbert basis is not used. The domain of
  `diag(λ_n)` is the source's `{Σ c_n e_n | Σ |λ_n c_n|² < ∞}` (round 33's `Diag.op`); "pure point
  spectrum" is round 37's `Diag.spectral_clause`; `ker(A - x)` is `eigSub A x`. In (iii) `W` is a
  bounded linear bijection as in the source; the proof uses only bijectivity and linearity.
- `prop:bsd-spectral-rank`: FAITHFUL to the conditional argument. The generalized block `V_{E,(1)}`
  is a finite-dimensional `V` on which `Θ - 1` is nilpotent; `Θ + Θ* = 2` is the identity
  `h(Θu, v) + h(u, Θv) = 2 h(u, v)` for a `PosHermForm`; orders are `meromorphicOrderAt`;
  `rank E(K)` is `dim_ℂ M` for a space `M` standing for `E(K) ⊗_ℤ ℂ`, with the Abel–Jacobi
  isomorphism a linear equivalence `M ≃ ker(Θ - 1)`. Elliptic curves themselves are not modelled.
- `prop:bsd-picard-gap`: PARTIAL, algebraic part only. The geometric facts (`Pic(E)`, the degree
  splitting `n ↦ O_E(nO)`, Abel–Jacobi `Pic⁰(E)(K) = E(K)`, and that `c₁` sees only the degree) are
  hypotheses: a `ℤ`-linear `deg` with a section, `E(K) ≅ ker deg`, and `c₁ = φ ∘ (deg ⊗ R)`. Proved:
  `Pic(E) ≅ ℤ × ker deg`, `E(K) ⊗ R → Pic(E) ⊗ R` is injective, and its image lies in `ker c₁`, for
  any commutative ring `R` (the source's `ℚ_ℓ`).

**`prop:content` (round 30, `Content.lean`).**
- (ii): FAITHFUL on the degree-one slice. "Positive definite Hermitian form on `V^1`" is
  `PosHermForm.ofBasis` of the basis `e_{ρ,k}` (orthonormal). "Not of the form `h_1`" is stated
  off the line, where the model's `*_1 = 0` and so `h_1 = 0`; "not satisfying `(eq:inf-pol)`
  unless `Σ` lies on the line" is `re_eq_half_of_isInfPol`, proved for *every* positive definite
  form on `V^1` (the source's route through `prop:purity`).
- (iii): PARTIAL. The real-pair block (`ρ : ℝ`, `Θ = diag(ρ, 1-ρ)`, `B(e,f) = 1 = -B(f,e)`,
  `*(ae+bf) = -āe + b̄f`) is FAITHFUL as a degree-one `WeightedStarDatum 1 0 1`: AW1 for `U = 𝟙`,
  the AW3 trace, the star law, `h_1(ae+bf, a'e+b'f) = a b̄' + b ā'`, Hermitian, nondegenerate,
  `(eq:inf-pol)` with weight one, signature `(1, 1)` (one positive and one negative vector). The
  quartet block is the existing `R2` (`Negative.lean`, matrix form, not a `WeightedStarDatum`).
  The assembly is round 31 (below). The last clause ("indefinite as soon as `Σ` has a
  point off the line") is formalized as `not_isPositive_of_re_ne` (not positive definite) for any
  degree-one datum; indefiniteness proper is shown for the pair block and for `R2`.
- (i), (iv): not formalized; they need `Σ_K = div ξ_K` for a number field `K` (`prop:xiK`) and
  the full axioms AW1–AW4 on `X̄_K` (obligation 21).

**`prop:content` (iii) assembly (round 31, `ContentAssembly.lean`).** FAITHFUL on the degree-one
slice. The divisor is given, one family member per unit of multiplicity, by line points
`ρL : ιL → ℂ` (hypothesis `Re = 1/2`; each contributes `ρ, 1 - ρ`, the trivial-model encoding),
real pairs `ρP : ιP → ℝ` (`ρ, 1 - ρ`) and quartets `lQ : ιQ → ℂ` (`λ, λ̄, 1 - λ, 1 - λ̄`); the
multiplicity of `σ` is `#{x // lamX x = σ}`. Every divisor of the source's kind arises this way.
The source's side conditions (support in `0 < Re s < 1`, `ρ ≠ 1/2` for a pair, `Re λ > 1/2`,
`Im λ > 0` for the chosen quartet member) are not needed and not assumed. `V^1 = ⨁_X ℂ` is the
algebraic direct sum of the blocks, with `B` and `*` the direct sums: on the line block the star of
`TrivialModel`, on a pair block the star of `Content.pairDatum`, on a quartet block `v ↦ S v̄`
with `B = uᵀΩv` (`R2_Ω`, `R2_S`, `R2_Θ`; `λ = 1/2 + a + iT`). "Indefinite as soon as `Σ` has a
point off the line" is proved as: if there is a real-pair or quartet unit, some `u, v` have
`h_1(u, u) = 2` and `h_1(v, v) = -2`. A real pair with `ρ = 1/2` would be an on-line point given
as a pair block. The source excludes it, and the theorem is still true for it.
Gap: as for `prop:trivial-model`, only the degree-one slice is modelled (`V^0`, `V^2 = ℂη` with
`Θ_2 = 1` and `u ∪ v = B(u, v)η` are encoded by `T = ℂ`, `ΘT = id`, `tr = id`).

**`prop:content` (iii) in degrees `0`, `2` (round 33, `ContentGraded.lean`).** FAITHFUL to the same
extent as round 32 for the trivial model. The product on `ℂ·1 ⊕ V^1 ⊕ ℂη` is the trivial model's
(`u ∪ v = B(u, v)η`, unit products), now for any `PairingModel.Data` whose signs alternate
(`sgn(σx) = -sgn(x)`, checked for the assembled blocks in `sgn_swp`); `B_antisymm` is then proved on
all of `V^1`. Degrees `0`, `2` reuse `model0`, `model2`, which do not depend on `Σ`.
`content_indef_graded` is the conjunction of these facts with `content_indef` covering degree
one.

**Round 40: `prop:relative-structure`, `prop:slice-not-full`.**
- `def:deninger-structure` (b): `Morphism` is FAITHFUL to the notes' definition, which does not fix
  the dimension; the earlier `Hom` (inside one `Den_d(U)`) embeds via `Hom.toMorphism`. Both
  structures must share the unit `(U, Θ_U)`.
- `prop:relative-structure`: FAITHFUL to the algebraic content. The notes obtain the morphism
  `H(π) : H(X̄_K) → H(X̄)` from functoriality of a Deninger cohomology theory; here it is a hypothesis,
  because `def:deninger-theory` is not formalized (see the claim table). "Graded `H(X̄_K)`-algebra"
  is: unital and associative action (`act_one`, `act_act`), additivity, grading (`act_mem`), and
  compatibility with the cup product on both sides, the right one with the Koszul sign
  (`act_mul_left`, `act_mul_right`); no Mathlib `Module`/`Algebra` instance is built, since `A`'s
  product is a bilinear map rather than a ring structure.
- `prop:slice-not-full`: FAITHFUL. Schemes over `Spec 𝒪_K` are Mathlib's `Over (Spec 𝒪_K)`, and the
  forgetful functor is `Over.forget`. "Automorphism group as a scheme is `Aut(K)`" is the bijection
  `σ ↦ Spec(σ|_{𝒪_K})` (`specAut_injective`, `exists_of_iso`); it reverses composition, so as groups
  it is an anti-isomorphism, which does not change the group up to isomorphism.

**2026-11-01: `Den^natural` morphism repair.** `Morphism` now permits both
dimension and unit to vary; its linear map preserves grading, unit and product
and commutes with the generators, without a trace condition. Identity,
composition, their laws and vanishing above the target top degree are checked.
`Hom` remains the within-component notion. This matches Definition 2.1 of
`ai/2026-10-31-no-functorial-definition/report.md` and the repaired manuscript
definition `def:deninger-structure` (c). The old disjoint-union obstruction is
recorded as `prop:den-disjoint-obstruction`. No category of bundled Deninger
structures or functor on `Schbar^proj` is formalized.

**2026-10-31: Deninger unification pass (`FlowCategory.lean`, `Deninger.lean`).** The notes now have
one definition of a Deninger cohomology theory (`def:deninger-theory`, core and full versions); `def:weil-cohomology` is the object-level list "Deninger axioms" AW1–AW4 on one Weil datum, and the
abstract zeta setting, the spectral-theory and test-category definitions, and the two definitions of
a Deninger cohomology theory on number fields alone are retired (commented out in the notes).
No existing declaration changed; docstrings of `RH`, `Multiplicities`, `Converse`, `Flow`, `Dedekind`
now describe `ArithmeticWeilCohomology*` as the degree-one slice of a polarized Deninger structure
satisfying AW2 (names historical).
- `def:flow-category`, `prop:flow-exact`: FAITHFUL for (a). Gap: (b) is stated for an `ℕ`-indexed
  bounded exact sequence starting with an injection; reindexing the notes' long exact sequence is not
  formalized.
- `def:deninger-structure`: FAITHFUL to AW1 + AW3, with two gaps: AW3 perfectness is encoded as
  two-sided nondegeneracy on blocks (perfect ⇔ nondegenerate for finite-dimensional blocks is not
  formalized), and `Den_d(U)` has `Hom.id`, `Hom.comp` but no bundled category instance.
- `def:polarizable`: FAITHFUL; polarizability is the `Prop` `Nonempty Polarization`, a property as in
  the notes. `WeightedAlgebraDatum.nondeg` shows positivity forces the AW3 nondegeneracy in weight 0.
- `def:deninger-module`: FAITHFUL; the unit is not required to act trivially, as in the notes.
- Not done: the optional degree-one bridge `DeningerStructure` → `ArithmeticWeilCohomologyQ`.

**Round 41: `prop:algebra-form` (i) over `ℚ`, `ℝ`, separability.**
- `PositiveTraceOrd`: FAITHFUL to `def:pos-involution` for `k ≠ ℂ`, stated over any linearly ordered
  field `K` (covers `ℚ` and `ℝ` together); `τ` and `†` are `K`-linear, `τ(a a†) > 0` for `a ≠ 0`.
- `minpoly_separable`: FAITHFUL for the separability clause of (i), slightly more general (any
  nonzero `c` with `g g† = c`, not only `c = q^j`). The proof differs from the source's: no complex
  extension; semisimplicity of `L_g` comes from the anisotropic similitude form directly
  (`isSemisimple_of_similitude`, the left orthogonal of an invariant subspace is an invariant
  complement), and squarefree equals separable in characteristic `0`. The modulus clause is not
  covered (obligation 22).

**Round 44: Arakelov A1 and the start of A2 (Gillet–Soulé 1990 §§3.1–3.2, checked in the
Numdam PDF).**
- `ArithmeticRing`: FAITHFUL to GS Def. 3.1.1 except that **excellence of `A` is not encoded**
  (Mathlib has `IsRegularRing`, which includes Noetherian, but no excellent rings). The instances ℤ
  and `𝓞 K` are Dedekind domains of characteristic `0`, hence excellent; that is not formalized.
  `S` is a `Finset (A →+* ℂ)` of monomorphisms; `F_∞` is a ring endomorphism of `ℂ^S` that is
  conjugate-linear, involutive and fixes `δ(A)`, as in GS.
- `Hom`: FAITHFUL to 3.1.3 (`f_∞` a `ℂ`-algebra map with `δ' ∘ f = f_∞ ∘ δ`, `F'_∞ ∘ f_∞ = f_∞ ∘ F_∞`).
  GS's remark that `f` is necessarily injective is proved (`Hom.f_injective`).
- `int`, `int_hom`, `int_hom_unique`: FAITHFUL to Examples 3.1.2 (1)/(2) for ℤ and to "ℤ is an
  initial object" (3.1.3), as existence plus uniqueness of homomorphisms.
- `ringOfIntegers`: FAITHFUL to Example 3.1.2 (1) for `A = 𝓞 K`: `S = Hom(𝓞 K, ℂ)` is proved
  (`mem_embeddings`), and `F_∞ x = (conj x_{σ̄})_σ` is the conjugation on `ℂ ⊗_ℚ K ≅ ℂ^S`. The other
  rings of Example 3.1.2 (fields `F`, localizations of `𝓞 F`, subrings of `ℝ`, `ℂ` with
  `S = {id, c}`) are not encoded.
- `ArithmeticVariety`: FAITHFUL to the scheme-theoretic part of GS 3.2.1, with "finite type" as
  locally of finite type plus quasi-compact and the generic fibre as the pullback along
  `Spec (Frac A) → Spec A`. Not yet encoded: `X_∞ = X_S(ℂ)` with its involution, and the real
  `(p,p)`-forms and currents (Tier B).

**Round 45: Arakelov A2 finished, A3 started (GS 1990 3.2.1, 5.1.1, checked in the local PDF).**
- `F_apply`, `conj_mem`: FAITHFUL consequences of GS 3.1.1 (not stated there; GS describe `F_∞` only in
  the examples). Proof: `conj ∘ ev_τ ∘ F_∞` is a `ℂ`-algebra map `ℂ^S → ℂ`, hence an evaluation, and
  `F_∞ ∘ δ = δ` identifies which.
- `complexPoints`, `Finf`: FAITHFUL to GS 3.2.1 **as sets**: `X_∞` is the set of pairs `(σ, x)`,
  `x : Spec ℂ → X` over `Spec σ`, i.e. `⊔_σ X_σ(ℂ)`, and `F_∞` acts by `(σ, x) ↦ (σ̄, x ∘ Spec conj)`.
  Not encoded: the analytic-space / complex-manifold structure and continuity of `F_∞` (Tier B; Mathlib
  has no analytification). The base ring is in universe 0 so that `Spec ℂ` and `X` share a universe.
- `complexPointsSpecEquiv(_Finf)`: for `Spec 𝓞 K`, `X_∞ ≃ Hom(K, ℂ)` with `F_∞ ↦ conjugate`; this is the
  description used by the notes (`def:arakelov-pair`) and by Flach–Morin pp. 520–521 in dimension one.
- `ComplexPointsTopology` (2026-11-13): the pointwise evaluation topology on `Hom(K, ℂ)` is
  discrete; transported through `complexPointsSpecEquiv` and `Xbar.pointsEquiv`, it makes `F_∞`
  continuous on the arithmetic-base and manuscript versions of `Spec 𝓞_K`. This is a
  zero-dimensional topological model for GS 3.2.1. The comparison with the analytic topology on
  the complex base change is still open, as are complex manifolds and forms in higher dimension.
  `scratch/2026-11-13-axiom-math/report.md` maps relevant AxiomMath sources and version pins.
- `ArakelovVariety`: PARTIAL relative to GS 5.1.1. (i) Regularity is encoded as regular local stalks
  (`IsRegularScheme`, via Mathlib's `IsRegularLocalRing`, Stacks 00KU). (ii) **Projective generic fibre is
  weakened to proper** (Mathlib has no projective morphisms). (iii) **The Kähler form is an interface**
  (`KahlerInterface`, roadmap D2): an abstract real space of `(1,1)`-forms with `F_∞^*` and a `IsKahler`
  predicate, with no analytic content. The only instance, `zeroDim`, is the honest one for a finite `X_∞`
  (the zero form, Kähler vacuously), so the `Spec A` instances are faithful, but nothing in higher
  dimension is. The roadmap (§6b) asks that the interface also carry the real Hodge structure on
  `H*(X(ℂ))` for the Flach–Morin path; that is not yet done (obligation 23).

**Round 46: Arakelov A4 and D1 (notes `def:compactified-schemes`).**
- `CompactifiedScheme`, `Schbar`: FAITHFUL to (a), (b) except: (i) the Kähler condition "projective, flat,
  regular over `ℤ`" uses **proper** for projective (as in round 45); (ii) the Kähler datum is the D2
  interface; (iii) `X_∞` is a set. Morphisms are exactly morphisms of schemes, as (b) says: the map
  on `X(ℂ)` is induced and automatically `F_∞`-equivariant (`mapPoints_Finf`), and Kähler data are not
  preserved, so `\Schbar → Sch` is fully faithful.
- `Schbar.reg`: PARTIAL; "pure dimension" is not encoded (no equidimensionality predicate in Mathlib).
- `Schbar.proj`: FAITHFUL up to proper-for-projective, on both sides (over a finite field "smooth
  projective" is weakened to smooth proper).
- `\Schbar_1` (e) is not built as a subcategory: only its connected objects `X̄_K` exist. Finite disjoint
  unions are left for D2 (they need coproducts of schemes and of Kähler data).
- `Xbar.place_eq_place_iff`, `isReal_place_iff`, `card_fiber_place`, `card_points`: FAITHFUL; they are the
  standard identification of the `F_∞`-orbits on `Hom(K, ℂ)` with the infinite places (Mathlib's
  `InfinitePlace.mk_eq_iff`, `card_filter_mk_eq`, `card_add_two_mul_card_eq_rank`).

**Round 47: Arakelov D2 (notes `prop:A1-number-fields`).**
- `homEquiv`, `ringHomEquiv`, `ringHom_injective`, `endEquiv`: FAITHFUL; they are the notes' proof
  (`Hom_𝒩(K, L) = Hom(𝓞_K, 𝓞_L) = Hom(Spec 𝓞_L, Spec 𝓞_K)`), and the map on infinite places is induced
  (`Schbar.infty`), adding no choice. `endEquiv` gives `End(X̄_K) ≃ (K →+* K)`; that these are all
  automorphisms (finite-dimensionality over `ℚ`) is not stated separately.
- `arith_fullyFaithful`, `arithEquiv`: PARTIAL. The target "full subcategory of connected objects of
  `\Schbar_1`" is replaced by the essential image of `K ↦ X̄_K`, because `\Schbar_1` (finite disjoint
  unions) is still not built; the notes' step "every connected object of `\Schbar_1` is some `X̄_K`" is
  then true by definition. Disjoint unions are deliberately left out: by refutation N12 of
  `ai/2026-10-31-conditional-dynamical-cohomology/report.md`, no functor into the Deninger category sends
  coproducts to products, so a Deninger theory is stated on connected objects.

**Round 60: `X̄_K` at `n < 0`.**
- FAITHFUL to FM §3.1 at `n < 0` (stated explicitly by FM): `RΓ(X, ℝ(n)) = 0`, `ℝ(n)_D = (2πi)^n ℝ`,
  `RΓ_c = RΓ(G_ℝ, X(ℂ), (2πi)^n ℝ)[−1]`. MODELLED: `(2πi)^n ℝ` identified with `ℝ` (conjugation acts by
  `(−1)^n`), `G_ℝ`-cohomology in positive degree with real coefficients taken to vanish (standard, not
  formalized). COMPUTED: the parity count of `H^0_D`, exactness, `H^*_c`, `H^*(X̄_K) = 0`, `H^*_ar = 0`.
- CONDITIONAL: `ord_{s=n} ζ(X̄_K, s) = 0` assumes `SimplePoles` and `NonvanishingRight` (`ξ_K ≠ 0` on
  `Re s > 1`, i.e. the Euler product of `ζ_K`, missing in Mathlib); for `ℚ` only `SimplePoles` (automatic).
- AGREEMENT with FM Prop. 4.14 (i), (iii) at `n < 0`. The parity-dependent dimension appears only in the
  non-compact `H^1_c(X_K, ℝ(n))` and matches the trivial zeros of the uncompleted `ζ_K` (not formalized), so
  there is no discrepancy with FM's statement for `X̄`.
- The `X̄_K` part of the FM path is now complete for all `n ≤ 1`; `n ≥ 2` (Borel regulators) and every
  case with `dim X(ℂ) > 0` need input outside the current model.

**Round 63: local Euler factors and `ζ_K ≠ 0`.**
- FAITHFUL: `localFactor_eq_prod` and `dedekindZeta_ne_zero` are about Mathlib's own `dedekindZeta`; the
  primes over `p` are encoded as `(normalizedFactors (p)).toFinset`, equivalent to Mathlib's `primesOver`.
- Removed hypothesis: `NonvanishingRight` is now a theorem for every `K`; the remaining analytic hypothesis
  in rounds 50–60 is `SimplePoles` (Hecke's continuation with simple poles).

**Round 62: multiplicativity and the Euler product of `ζ_K`.**
- FAITHFUL: `coeff_mul` and `dedekindZeta_eulerProduct_hasProd` are about Mathlib's own `dedekindZeta`; the
  product is over rational primes `p` with local factors `∑_e a_K(p^e) p^{-es}` (not yet over prime ideals).
- PARTIAL toward nonvanishing: `ζ_K(s) ≠ 0` on `Re s > 1` is reduced to nonvanishing of the local factors.
- Gap (precise): `∑_e a_K(p^e) X^e = ∏_{𝔭 ∣ p} (1 - X^{f_𝔭})⁻¹`, i.e. the splitting of `p` in `𝓞_K`.

**Round 61: convergence of `ζ_K`.**
- FAITHFUL: `LSeriesSummable_coeff` and `dedekindZeta_pos` are about Mathlib's own `dedekindZeta`.
- PARTIAL toward the Euler product: complex nonvanishing on `Re s > 1` is not proved; `NonvanishingRight`
  is now reduced exactly to `ζ_K(s) ≠ 0` on `Re s > 1` and proved on the real axis only.
- Gap (precise): multiplicativity of `n ↦ #{I : N I = n}`, or an Euler product over prime ideals.

**Round 59: `X̄_K` at `n = 0`, nontrivial retraction.**
- FAITHFUL to FM §3.1–3.2 at `n = 0`, reading `ℝ(0)_D = ℝ` from the displayed complex
  `(2πi)^n ℝ → Ω^0 → ⋯ → Ω^{n-1}` (empty Ω-part); FM state `n < 0` explicitly, `n = 0` is our reading.
- MODELLED: `H^0(X_K, ℝ(0)) = ℝ` (Bloch `ℤ(0) = ℤ`, standard, not in FM), `H^0_D = ℝ^{InfinitePlace K}`
  (`G_ℝ`-invariant functions on `X(ℂ)`), other groups `0`. COMPUTED: exactness, `H^*_c`, `H^*(X̄_K)`,
  Weil–Arakelov groups, and `fm414_zero` (from round 58's order, `SimplePoles` only).
- The retraction is nontrivial (zero, not the identity) but FORCED: no Kähler-metric dependence for finite
  `X(ℂ)`. The case `n < 0` (all groups of `X̄_K` vanish, `ord_{s=n} = 0`) is argued in the module docstring,
  not formalized. Kähler-dependent retractions (`ℙⁿ`, `dim X(ℂ) > 0`) remain blocked on analytification.

**Round 58: FM Prop. 4.14 (iii) for `X̄_K`, `n = 1`.**
- FAITHFUL to (iii) in this case, with two encodings: FM's `dim_ℂ CH^n(X̄)_ℂ` is read as `dim_ℝ` of round 57's
  real-coefficient group `ĈH¹(X̄_K)_ℝ` (same number after `⊗_ℝ ℂ`); the order is Mathlib's
  `meromorphicOrderAt`, which ignores `Λ_K`'s junk value at the pole.
- CONDITIONAL only on `SimplePoles` (Hecke's simple poles, not in Mathlib). FM's Conjecture 4.1, which FM's
  Prop. 4.14 assumes, is not needed here. `ζ(Spec 𝒪_K, s)` is still Mathlib's `dedekindZeta` by definition
  (round 50; no Euler product).

**Round 57: `H²(X̄_K, ℝ(1)) ≅ ĈH¹(X̄_K)_ℝ`.**
- FAITHFUL for the real-coefficient group: `ChowR K` is the GS 3.4.3 group with real coefficients, the object
  of FM Notation 4.13 ("Arakelov–Chow group with real coefficients"). FM cite [18, 5.1.1] and [19, 3.3.3] for
  it; GS 1990 §5.1.1 (checked locally) does not itself define real coefficients, and [19] is not local, so the
  construction (quotient by the `ℝ`-span of principal divisors) is the standard one, not checked against [19].
- REFUTATION (not formalized): it is natural to read "`⊗ ℝ`" as `ĈH¹ ⊗_ℤ ℝ`; that is NOT `ℝ` once
  `r₁ + r₂ ≥ 2`. The kernel of the degree on `ĈH¹` contains the torus `H/Λ` (degree-zero Green vectors modulo
  the log-unit lattice of rank `r₁ + r₂ − 1`), a divisible group whose `⊗_ℤ ℝ` is nonzero. `toChowR` is the
  correct comparison; for `K = ℚ` both agree (round 49's `chowDegreeEquivRat`).
- CANONICAL vs CHOSEN: `chowDegreeR` is canonical. `compactOne_Hbar_two` is canonical given round 55's
  modelled `H¹_D = ℝ^{places}` (with Mathlib's `mult`-rescaled regulator). So `chowRToH2` is canonical up to
  that normalization; it is NOT shown to be the map of FM [13, Prop. 2.11], whose construction is not
  formalized.

**Round 56: FM path §3.2 and E4 for `X̄_K`, `n = 1`.**
- `CompactifiedDatum` is an INTERFACE on cohomology groups: the Kähler retraction and the fibre triangle of FM
  §3.2 are recorded only through `ret ∘ adj = id`, the truncation conditions and the long exact sequence.
- `compactOne K` inherits round 55's MODELLED groups; given them, `τ_{<2} RΓ_D = RΓ_D` and `ret = adj = id`
  are forced (Deligne cohomology vanishes in degrees `≥ 2`), and `H^i(X̄_K, ℝ(1)) = H^i_c` is COMPUTED. The
  Kähler metric plays no role, since `X_K(ℂ)` is finite.
- FINDING (agreement): `prop414_shape` — `H^i_ar(X̄_K, ℝ̃(1))` vanishes for `i ∉ {2, 3}` and has dimension 1
  in degrees 2, 3, as FM Prop. 4.14 (i) predicts, and `1 = −ord_{s=1} ζ̂_K` (simple pole; round 50's
  `xi_one_ne_zero`). NOT formalized: the pole order as an order equation, and `H² ≅ CH¹(X̄_K)_ℝ` via round 48's
  degree.
- The non-compactified `(Spec 𝒪_K, ∅)` gives groups of dimension `r₁ + r₂ − 1` in degrees 1, 2. Prop. 4.14
  does not apply to it (not "projective regular" in FM Notation 2.2), so this is a contrast, not a
  counterexample.

**Round 55: FM path E3, degree-one Deligne datum of `X̄_K`.**
- COMPUTED: the regulator `⊗ ℝ` (`regR`), its injectivity and image (Dirichlet's unit theorem via Mathlib's
  `unitLattice`, `instZLattice_unitLattice`, `basisUnitLattice`), hence `H¹_c = 0` and `H²_c ≅ ℝ`; the three
  exactness fields of `degreeOne` are proved.
- MODELLED (standard, not derived): `H¹(Spec 𝒪_K, ℝ(1)) := Λ_K ⊗ ℝ` (Λ_K ≅ 𝒪_K^×/μ(K) by Mathlib's
  `logEmbeddingEquiv`; that `⊗ ℝ` kills `μ(K)`, giving `𝒪_K^× ⊗ ℝ`, is not formalized);
  `H¹_D(X/ℝ, ℝ(1)) := ℝ^{InfinitePlace K}`; all other degrees `0`; `H^i_c → H^i` is `0`.
- NORMALIZATION: the Deligne complex gives `u ↦ (log|σ u|)` on `(ℂ/2πiℝ)^{Hom(K,ℂ)}`, whose `G_ℝ`-invariants
  are `ℝ^{InfinitePlace K}` by evaluating at one embedding per place; `regulatorMap` has entries
  `mult w · log w(u)`, i.e. FM's regulator followed by the invertible diagonal rescaling by `mult w ∈ {1, 2}`.
  Kernel, image dimension and cokernel are unchanged.
- The file sets `backward.isDefEq.respectTransparency.types false`, as Mathlib's `DirichletTheorem.lean` does.

**Round 54: FM path E3, Deligne datum and Weil–Arakelov groups.**
- `DeligneDatum`: an INTERFACE for FM §3.1. Motivic and Deligne cohomology and the regulator are data;
  FM's mapping fibre is recorded only through its long exact sequence. The only instance is the
  degenerate `idDatum`; no geometric instance (Mathlib has no Bloch cycle complex or Deligne cohomology).
- `Har`, `theta`, `theta_comp`, `ker_theta_succ`, `kerThetaEquiv`, `cokerThetaEquiv`: FAITHFUL to FM (2)–(5)
  at the level of COHOMOLOGY GROUPS (FM work with complexes; the cohomology of `RΓ ⊕ RΓ[−1]` is
  `H^i ⊕ H^{i−1}`, and `∪θ` induces `(a, b) ↦ (0, a)`). The compactified `RΓ(X̄, ℝ(n))` of §3.2 (Kähler
  retraction) is not encoded.
- `regulatorMap`: FAITHFUL as the Dirichlet regulator on `𝒪_K^×`; its identification with FM's degree-one
  regulator `H^1(X̄_K, ℝ(1)) → H^1_D` (after `⊗ ℝ`) is standard but not formalized.

**Round 53: FM path, Hodge data of `ℙⁿ_{𝓞_K}`.**
- `ProjSpace.hodge`: an instance of the `HodgeDatum` interface. The pieces `H^{k,k} = ℂ^{Hom(K,ℂ)}` and the
  sign `F_∞ = (−1)^k · (f ↦ f ∘ conj)` are MODELLED (standard topology of `ℙⁿ(ℂ)`), not computed from an
  analytification. Given the datum, `hplus_eq`, `hminus_eq`, `LInfty_two_mul`, `zetaInfty_eq` are FAITHFUL to
  FM's definitions and formula (1).
- `zetaPn` is DEFINITIONAL: `ζ(ℙⁿ_{𝓞_K}, s) := ∏_k ζ_K(s−k)`; the point-count identity is not proved
  (no Serre `ζ(X, s)` for schemes, no Euler product of `dedekindZeta` in Mathlib). `ProjSpace.zetaFM_eq` is
  FAITHFUL relative to this definition and to round 50's `zetaFM`.

**Round 52: FM path, Hodge data at infinity.**
- `HodgeDatum`, `LInfty`, `zetaInfty`: FAITHFUL to FM pp. 520–521 as an *interface*: the Hodge pieces and
  `F_∞` are data, not constructed from a complex manifold `X(ℂ)` (no analytification or Hodge theory in
  Mathlib). Compatibility of `F_∞` with conjugation of coefficients (the real structure) is not encoded;
  FM's formula uses only `F_∞` and the Hodge numbers.
- `Xbar.hodge`, `zetaInfty_hodge`: FAITHFUL for `X̄_K` (`X(ℂ)` finite, `H^* = H^0 = H^{0,0}`). The Hodge
  numbers are computed from the `F_∞`-action, so round 50's simplification is removed.

**Round 51: Arakelov D5 (`prop:content` (i), (iv)).**
- `content_free`: PARTIAL for (i), degree-one slice. AW1 and AW3 are those of `TrivialModel.model`; AW2 is
  encoded as `Sp_1 = div ξ_K` with multiplicities, which with the endpoints `Sp_0 = {0}`, `Sp_2 = {1}`
  (`TrivialModelFull`) is the divisor of `Λ_K` (`SimplePoles.xi_eq_zero_iff`). The notes' "unconditionally"
  holds relative to Hecke's continuation and simple poles (`DedekindContinuation`, `SimplePoles`), which are
  hypotheses here.
- `content_iff`: FAITHFUL to (iv) for degree-one data (`WeightedStarDatum 1 0 1` with `Sp_1 = div ξ_K`),
  under the same hypotheses; "every zero of `ξ_K`" is literal (`P.ξ ρ = 0`).
- `SymEntire.even_mult_half`: FAITHFUL to the notes' parity step in the proof of (i), proved for any entire
  `f` with `f(1 − s) = f(s)`.

**Round 50: Arakelov D3 finished as far as Mathlib allows, D4 done.**
- `SimplePoles`: a hypothesis, PARTIAL for Hecke's theorem in the notes (`thm:imp-hecke`): it records only
  that `s(s − 1)Λ_K` extends to an entire function. `xi_one_ne_zero`, `xi_zero_ne_zero`: FAITHFUL to
  `prop:xiK`'s "`ξ_K(0)ξ_K(1) ≠ 0`", proved from Mathlib's class number formula, not assumed. Still open for
  `prop:xiK`: nonvanishing for `Re s > 1` (Euler product of `dedekindZeta` absent from Mathlib v4.34.1) and
  `ord ξ_K = ord ζ_K` on the strip.
- `zetaFM_eq`, `analyticOrderAt_xiFM`: FAITHFUL to FM p. 520–521 for `X̄_K` with two recorded
  simplifications: FM's `ζ(Spec 𝓞_K, s)` (Euler product over closed points) is taken to be Mathlib's
  ideal-counting `dedekindZeta` (equal for `Re s > 1`, but the Euler product is not in Mathlib), and the
  Hodge numbers `h^{0,+} = r₁ + r₂`, `h^{0,−} = r₂` are used as exponents rather than computed from the
  `F_∞`-action on `ℂ^{X_∞}` (D1 gives the orbit structure). The constants are explicit: `a = −(r₁/2 + r₂) log 2`,
  `b = −(log |d_K|)/2`, consistent with ruling R-1 (`ℚ`: `e^a = 2^{-1/2}`, `b = 0`) and the earlier
  "`b = −½ log |d_K|`" of `ai/2026-09-25-zeta-class-axioms` (C4).

**Round 49: Arakelov C1 finished, D3 started.**
- `toClass_surjective`, `toClass_eq_zero_iff`, `ofGreen_eq_zero_iff`: FAITHFUL to GS 3.4.3's sequence from
  the Green vectors onward. The kernel of `𝓞_K^* → ⊕ ℝ` (GS: roots of unity) is not computed, and the
  units are characterized as the `x ∈ K^*` with trivial principal ideal (`toPrincipalIdeal_eq_one_iff`).
- `chowDegreeEquivRat`: FAITHFUL to GS 3.4.3 ("if `A = ℤ`, `deg : ĈH¹(Spec ℤ) → ℝ` is an isomorphism, since
  `ℤ^* = μ(ℤ)` and `Cl(ℤ) = {1}`").
- `xiK*`: PARTIAL for `prop:xiK`. Proved: the functional equation off `{0, 1}`, independence of the
  continuation, and `ξ_ℚ = 2ξ` with its zeros. Not proved: that `ξ_K` is entire and `ξ_K(0)ξ_K(1) ≠ 0`
  (`DedekindContinuation` does not record that the poles are simple), nonvanishing for `Re s > 1` (needs the
  Euler product of `dedekindZeta`, absent from Mathlib v4.34.1), and `ord ξ_K = ord ζ_K` on the strip (needs
  the continuation of `ζ_K` itself).

**Round 48: Arakelov C1 (GS 1990 §3.4.3).**
- `principal`, `ChowGroup`, `degree`, `chowDegree`, `deg_principal`: FAITHFUL to GS 3.4.3 for `A = 𝓞_K`.
  Divisors on `Spec 𝓞_K` are encoded as invertible fractional ideals and `#(Z)` as
  `FractionalIdeal.absNorm` (the divisor group of a Dedekind domain); `X_∞` as `K →+* ℂ`, which round 46
  identified with `X̄_K(ℂ)` (`Xbar.pointsEquiv`). The factor `½` in `log #(Z) + ½ Σ_σ g_σ` is read from
  GS 3.4.3; that line of the local PDF's text layer is OCR-garbled, so the constant was confirmed by
  consistency: with GS's Green vector `-log |σ f|²` the degree of a principal divisor vanishes exactly
  for `½` (`deg_principal`).
- `ĈH¹` is defined as the quotient in GS 3.4.3, not through Green currents on a general arithmetic
  variety (roadmap C2). Not formalized: the exact sequence's other terms (the map to `Cl(𝓞_K)`, the kernel
  `μ(K)`), the idele description `ĈH¹ ≅ K*\J(K)/U_K`, and GS's isomorphism `deĝ : ĈH¹(Spec ℤ) ≅ ℝ`
  (only surjectivity, for every `K`).

**Round 65: `prop:converse`, `prop:R1`, `prop:R2`, `prop:R3`, `prop:F0` (`ConverseCore.lean`, `R1.lean`,
`R2Block.lean`, `XiHalf.lean`).** Checked against the `latex/notes.tex` statements of 2026-11-20.

* `prop:converse`: FAITHFUL, with two representation choices. (a) "`spec Θ` with multiplicities is the
  multiset of nontrivial zeros" is `mult Θ ρ = ord_ρ ξ` for **every** `ρ ∈ ℂ` (`ord_ρ ξ > 0` exactly at the
  nontrivial zeros, `analyticOrderNatAt_completedXi_pos_iff`), so `ρ ∉ spec Θ` off the zeros. (b) The
  multiplicity of a zero is its order as a zero of `ξ`, not of `ζ`; the two agree at nontrivial zeros
  (`½ s(s−1) Γ_ℝ(s)` is analytic and nonzero there) but that equality is **not** proved in Lean. `V : Type`
  (universe `0`). The (i) ⇒ (ii) model is round 4's `multDiagonalModel`; it is built from the zeros and is not
  arithmetic, as the manuscript says. (ii) ⇒ (i) goes through `PosHermForm.re_eq_half` (`prop:purity`).
* `prop:R1`: FAITHFUL. Forms are functions `(Fin 2 → ℂ) → (Fin 2 → ℂ) → ℂ`, linear in the first argument;
  "nondegenerate" is a trivial left kernel; the eigenline is `{v | Θ v = (j/2 + iτ₁) v}`, shown to be
  `{v | v₂ = 0}` for `τ₁ ≠ τ₂`. "`Re ρ ≠ j/2` is possible" is `dual_off_line`.
* `prop:R2` (i): FAITHFUL up to packaging. `R2.gradedBlock` is a `HermAlgebraDatum _ 1 0`, whose fields are the
  derivation rule (AW1 for `U = 𝟙`), `Tr(Θ_2 x) = (d + w) Tr x` with `d = 1`, `w = 0` (AW3), the star laws
  `Θ_{2-j} *_j = *_j Θ_j + (1 − j) *_j` in degrees `0, 1, 2` (AW4), and Hermitian nondegenerate `h_j`. It lives on
  `ℂ × ⨁_{X} ℂ × ℂ` with `X = (Empty × Bool) ⊕ (Empty × Bool) ⊕ (Unit × Fin 4)`, not literally on `ℂ ⊕ ℂ⁴ ⊕ ℂ`;
  its degree-one data are identified with the matrices `Θ, Ω, S` of `def:R2-block` entrywise on `Fin 4`
  (`ContentAssembly.R2_Θ`, `R2_Ω`, `R2_S`). **Not fields of the structure:** AW3's perfect pairing of the
  `ρ`-eigenline with the `(1 − ρ)`-eigenline (visible from `B(e_x, e_{σx}) = sgn x ≠ 0`, `Data.sgn_ne`, but not
  stated as perfectness), and associativity and graded commutativity of the product (proved separately for
  `PairingModel`, `ContentGraded.lean`). `J² = −1` is proved for the matrix `S` (`R2.quaternionic`: `S S̄ = −1`),
  not restated for `gradedBlock`'s star.
* `prop:R2` (ii): FAITHFUL. Signature `(2, 2)` is the congruence `Pᵀ H P = diag(2, 2, −2, −2)` for a real
  invertible `P` (`R2.signature`; since `P̄ = P` this is the Gram matrix of `h₁` on the columns of `P`), which
  is signature `(2, 2)` by Sylvester's law. The manuscript argues via `H² = 1`, `tr H = 0`.
* `prop:R2` (iii): FAITHFUL and more general: proved for all real `a`, `T`; "none lies on `Re s = 1/2`" needs
  only `a ≠ 0` (`re_ne_half_of_eigen`).
* `prop:R3` (i)–(ii): FAITHFUL; only `T ≠ 0` is used. The cohomology of `C_n` is `ker` and `coker` of
  `toLin' (Θ − n)`. "`p(s) > 0` for real `s`" is `p(x) = (real positive number)`. "Degree four" is
  `natDegree pPoly = 4` with `pPoly.eval = p`. (iii) is not formalized (obligation 1).
* `prop:F0`: **CONDITIONAL** on `ζ(1/2) < 0` (as `(riemannZeta (1/2)).re < 0`; `ζ(1/2)` is proved real).
  `F = riemannXiUpper` is `def:zeta` (d) verbatim. The reduction `0 < ξ(1/2) ↔ ζ(1/2) < 0` is unconditional.
  The manuscript's eta-function step is a Mathlib gap (obligation 24).

**Old claim IDs → manuscript labels (round 65).** No new proofs for these four; the rows map existing declarations
to the current labels and record what they cover. `thm:main-general`: only purity and diagonalizability per
degree (C-PUR, Q1-L4.2); its "polarized graded spectral realization" and the order formula are not encoded.
`thm:A-schemes`: (i) only. `thm:A`: (i) only, conditional on `DedekindContinuation K` (constructed for `K = ℚ`), and the
Weil datum is its degree-one slice; (iv) only for `K = ℚ`. `thm:B`: the linear-algebra core of the suspension
(C-B); no `ℓ`-adic cohomology, AW-det or `ι`.

**Round 66: `thm:main-general`, `thm:A-schemes` (ii)–(iii), `thm:main-number-fields` (first sentence),
`prop:converse` (`ζ`-multiplicities), `prop:no-positivity-cancel` (`η`) (`MainGeneral.lean`, `XiZetaOrder.lean`,
`NoPositivityCancel.lean`).** Checked against the `latex/notes.tex` statements of 2026-11-20.

* `def:graded-realization`: FAITHFUL. `div Z` is `MeromorphicOn.divisor Z Set.univ` (value
  `(meromorphicOrderAt Z ρ).untop₀` when `Z` is meromorphic on `ℂ`); `dim V^j_{Θ∼ρ}` is `Spectral.mult`. The pieces
  are a family `V : ℕ → Type u`; pieces with `j > 2d` are ignored (they enter neither the divisor nor the
  polarization). `w` is a parameter of the type and constrains nothing until `Polarization`, as in the notes.
* `thm:main-general`: FAITHFUL. `Z ≢ 0` is `∃ z, meromorphicOrderAt Z z ≠ ⊤`, with `MeromorphicOn Z Set.univ`;
  `ord_ρ Z` is `meromorphicOrderAt Z ρ`. Both cases of the displayed formula are stated (`…_of_line`,
  `…_zero_of_off`); the divisor forms (`divisor_eq_of_line`, `divisor_eq_zero_of_off`) need neither hypothesis.
  "Zeros only on odd lines, poles only on even lines, `div Z` determines each spectral divisor" are
  `exists_odd_of_divisor_pos`, `exists_even_of_divisor_neg`, `mult_eq_of_line` (together with `mult_eq_zero`).
* `thm:A-schemes` (ii)–(iii): FAITHFUL for the hypotheses "derivation rule of AW1, AW2 for `Z`, trace
  equivariance of AW3, AW4" as encoded by `WeightedAlgebraDatum V d 0` plus the divisor hypothesis `hdiv` (AW2,
  i.e. `eq:aw-div`). `m_j(ρ)` is `Spectral.mult (D.Θr j) ρ`. `d ≥ 1` is not needed. (iii)'s real-part sets
  `{1/2, …, (2d−1)/2}` and `{0, …, d}` are stated as `2 Re ρ = j` with `j ≤ 2d` odd, respectively even.
* `thm:main-number-fields`, first sentence: **CONDITIONAL** on `C : DedekindContinuation K` and
  `P : C.SimplePoles` (Hecke's continuation; constructed for `K = ℚ`, so `riemannHypothesis_of_realization` is
  unconditional, for `DedekindContinuation.rat`). "Nontrivial zero of `ζ_K`" is a zero of `ξ_K = P.ξ`
  (`xi_eq_zero_iff`: `Λ_K(ρ) = 0`, `ρ ≠ 0, 1`). The endpoint data `(V^0, Θ_0) ≅ (ℂ, 0)`, `(V^2, Θ_2) ≅ (ℂ, 1)` are
  taken as hypotheses (linear equivalences) but are not used: the conclusion follows from the odd-line clause,
  since `2 Re ρ ∈ {0, 1, 2}` odd forces `Re ρ = 1/2`. The second sentence (Hecke and Artin `L`-functions) is not
  formalized (needs `thm:A` (ii)–(iii) and the Artin formalism).
* `prop:converse` (`XiZetaOrder.lean`): round 65's caveat (b) is removed. `ord_ρ ζ = ord_ρ ξ` at every
  nontrivial zero, via `ζ = (2 Γ_ℝ⁻¹ / (s(s−1))) ξ` near `ρ` with `1/Γ_ℝ` entire and `Γ_ℝ(ρ) ≠ 0`; and
  `ord_ρ ξ = 0` off the nontrivial zeros. So `PositiveZetaCore`'s multiplicities are exactly the `ζ`-multiplicities
  (`mult_eq_zeta`).
* `prop:no-positivity-cancel`: only the first clause. `exists_eta` proves `∃ η ∈ V^{2d}, Θ η = d η, Tr η = 1` for a
  `DeningerStructure V d ℂ Unit.arith` (AW1 for `𝟙` and AW3), for every `d` (the notes need `d = 2`), by the notes'
  argument (`V^{2d} ≅ 𝟙(−d)`, AW3 pairing with the unit). The adjunction (`def:adjoin-pair`) and its AW1, AW2,
  AW3 and the change of `Sp_1, Sp_2, Sp_3` are not formalized (obligation 25).
* `prop:F0`: unchanged, still conditional on `ζ(1/2) < 0` (obligation 24, updated).

**Round 67: `prop:kun-open`, `prop:kun-arch`, `thm:kun-square` (iii)–(iv), `prop:N-count` (i) (`KunOpen.lean`,
`KunArch.lean`, `KunSquare.lean`, `NCount.lean`).** Checked against the `latex/notes.tex` statements of 2026-11-20.

* `prop:kun-open`: FAITHFUL. "Exact sequence of spectral cores and linear maps commuting with the generators" is
  `KunSeq` (eight `SpectralCore`s, seven intertwining maps `θ' ∘ f = f ∘ θ`, injectivity at `E⁰`,
  `range = ker` at the six inner spots, surjectivity onto `F²`). `Sp(V)` is `ρ ↦ Spectral.mult Θ ρ`; the display is
  the pointwise identity in `ℤ`. "Two such sequences with the same `Fʲ`, `Gʲ`" means the same types and the same
  generators (`altDiv_eq_of_same`). The special cases: `F⁰ = ℂ` with generator `0` is the type `ℂ` with
  `θ_{F⁰} = 0`; "`Sp(E⁰) = [0]`" is `mult = if λ = 0 then 1 else 0`. Discreteness of the spectra is not used.
* `prop:kun-arch`: FAITHFUL for the archimedean factor of `def:artin` (b) at a real place, for one-dimensional
  characters (`LInftyChar χ c`, `c` the generator of the decomposition group). Not formalized: that the
  decomposition group at the real place of `ℚ(i)/ℚ` is generated by complex conjugation and that the nontrivial
  `χ` is the sign there; this enters as `χ c ≠ 1`, `c² = 1`. `χ ⊗ χ` is `χ ^ 2` (`G` commutative). Mathlib's
  `Gammaℝ` takes the value `0` at its poles, so the pole divisor is stated as `meromorphicOrderAt Gammaℝ ρ = -1`
  at `ρ = -2n` and `0` elsewhere (via the entire `1/Γ_ℝ`, simple zeros: `analyticOrderAt_inv_Gammaℝ_add`). The
  self-sum of divisors is `conv D D' λ = Σᶠ_{ρ+ρ'=λ} D(ρ)D'(ρ')`.
* `thm:kun-square` (iii)–(iv): PARTIAL. The surface datum (`def:kun-notation`) is not modelled; its input is an
  arbitrary `H` with `Θ_S` and an injective `κ` with `Θ_S κ = κ(Θ ⊗ 1 + 1 ⊗ Θ)`, which is (i)'s conclusion, not
  proved here. `Z(K)`, `Z(L)` are `spec Θ_V`, `spec Θ_W` (the link `spec = Z(K)` is `thm:rh`'s divisor
  identity, not restated). (iv): FAITHFUL in this setting; `Z(K) ∩ Z(L)` infinite becomes
  `{ρ ∈ spec Θ_V : 1 - ρ ∈ spec Θ_W}` infinite (equal to `Z(K) ∩ Z(L)` when `Z(L)` is `ρ ↦ 1 - ρ`-symmetric,
  `prop:xiK`); the `K = L` case assumes that symmetry and that `spec` is infinite (the manuscript's zero count,
  a Mathlib gap). The consequences "no Weil datum of type `(2, 0)`, AW2 and AW-det cannot be imposed" are the
  negation of `SpectralCore`, by definition. (iii): only the last step (an infinite bounded set of sums `ρ + ρ'`
  gives a finite accumulation point of `spec Θ_S`); the selection of `ρ_k + 1 - ρ'_k` with imaginary parts
  `→ 0` from "distinct imaginary parts in `(0, T]` not `O(T)`", and `Re ∈ [0, 2]`, `Im = 0` of the limit, are not
  formalized. (i), (ii): not formalized here (need the surface datum).
* `prop:N-count` (i): FAITHFUL for any entire `f` with `f(1 - s) = f(s)` and `f(z₀) ≠ 0`, and CONDITIONAL on
  `SimplePoles` for `f = ξ_K` (`NCount.xi`), as `prop:content`. `Σ = div f` is the trivial model of
  `SymEntire.family f`; `Σ'` is listed by `family' f` on `Idx f ⊕ ℕ`, the new member `k` being `1/2 + i e^{k+1}`
  (so `k ≥ 1` in the manuscript's indexing), with partner `1/2 − i e^{k+1}`. "Spectrum with multiplicity" is
  `dim V'_{Θ'∼σ} = m_f(σ) + #{added = σ}`. `ρ ↦ ρ̄` invariance of `Σ'` assumes that of `Σ` (`hconj`; for
  `ξ_K` this is the reality of `ξ_K` on `ℝ`, not formalized). Counts are cardinals of index sets, so
  `N_{Σ'}(T) = N_Σ(T) + ⌊log T⌋` holds without finiteness. (ii) is not formalized (needs `thm:det-K`).
* Not attempted this round: `thm:kun-hodge`, `prop:kun-hodge-strict`, `prop:unit` (first clause),
  `prop:algebra-form` over `ℚ`, `ℝ` (obligation 26).

**Round 69: traces of powers, `prop:R11` (iv), `prop:unit` first clause, `prop:algebra-form` over `ℚ`, `ℝ`.**
* `trace_pow_eq_sum_roots`: FAITHFUL to the identity the notes use in `thm:ff-lefschetz` and
  `def:lefschetz-numbers` (`N_k = ∑_j (-1)^j Tr(F^k | V^j)`), over `ℂ`. `lefschetzNumber_eq_sum_trace`
  connects it to round 5's multiset form. Items (i)–(ii) of `thm:ff-lefschetz` remain open (étale input).
* `R11.im_neg_logDeriv_lt_zero`: FAITHFUL. The order hypothesis is `analyticOrderAt G z₀ = k` with
  `1 ≤ k : ℕ`; a finite order already excludes `G ≡ 0`, so `G ≢ 0` is not a separate hypothesis. "Holomorphic
  at `z₀ - iε`" is `AnalyticAt ℂ (fun z => -deriv G z / G z)`, and `G(z₀ - iε) ≠ 0` is also stated.
* `UnitProduct`: FAITHFUL to the first clause of `prop:unit` given `H⁰ = ℂ` with `F = 1` (the input
  `thm:imp-weil-coh`, not formalized). `suspMul` is `def:susp-datum` (a) in degree zero: the copy of `u ∈ V̂_ρ`
  times the copy of `v ∈ V̂_{ρ'}` is the copy of `uv` in `V̂_{ρ+ρ'}` (here `q^{ρ+ρ'} = 1` is always an
  eigenvalue, so the "`0` otherwise" case is empty). `equiv` sends `1_{2πin/log q}` to `vⁿ`, and `equiv_mul`,
  `equiv_unit`, `equiv_theta` say it is an isomorphism of algebras with generator. The other clauses of
  `prop:unit` are `KunOrbits.mem_spec_unit_iff`, `mult_unit`, `Unit.not_equiv_arith` (rounds 25, 38).
* `AlgebraFormReal`: FAITHFUL for `k ∈ {ℚ, ℝ}`, generalized to any ordered field `K` with a scalar tower
  `K → ℝ → ℂ` whose first map is positive on positives (`nonvacuous_rat`, `nonvacuous_real`). "Complex roots of
  the minimal polynomial over `k`" are the roots of `(minpoly K g).map (algebraMap K ℂ)`; `gg† = q^j` is
  `g * dag g = c • 1` with `algebraMap K ℝ c = q^j`. The proof differs from the source: no Hermitian extension
  to `A ⊗_k ℂ`; an `S`-orthogonal basis (`exists_orthogonal_basis`) gives `Mᵀ D M = c D` with `D > 0`, and the
  modulus follows from an eigenvector of the complexified matrix. (ii) is stated for a ring map
  `ι : A → End_ℂ V` compatible with scalars, which is the restriction of the source's `ι : A ⊗_k ℂ → End V` to
  `A`; injectivity is not used.

**Round 70.**
* `GapStrip`: `gap_l2` is FAITHFUL to `eq:gap-l2`, stated for any finite-dimensional complex inner product
  space (every finite-dimensional `𝓔 ⊂ L²([-ℓ, ℓ])` is one; `gap` restates it for a submodule of `L2I ℓ`). The
  gap `d = dist(μ, spec(A|_{v^⊥}))` is encoded as a lower bound `d ≤ |λ - μ|` for every eigenvalue `λ` of
  `A|_{v^⊥}`; the manuscript's `d` satisfies it, and `d = +∞` (`v^⊥ = 0`) is covered by any `d > 0`. The unit
  norm of `v` is not used. `L²([-ℓ, ℓ])` is `Lp ℂ 2 (volume.restrict (Icc (-ℓ) ℓ))`, `ĝ(z) = ∫ g(t)e^{izt}`
  over `[-ℓ, ℓ]` (`def:weil-form` (a)). `eq:gap-strip` is stated pointwise for every `z` with `|Im z| ≤ b`,
  which is the supremum bound. `C ℓ b` is `def:residual-gap` (c) verbatim. The proof bounds
  `∫ e^{-2yt} = ∫ cosh(2yt) ≤ ∫ cosh(2bt)` instead of the manuscript's power-series monotonicity of
  `sinh(2yℓ)/y`.
* `R16`: FAITHFUL. `A_δ` is `x ↦ (0, δx₁, x₂)` on `EuclideanSpace ℂ (Fin 3)`. `‖f_ℓ‖₂` is `√(∫_ℝ |f_ℓ|²)`.
  `Fminus_f` holds for every `ℓ` (the manuscript's `ℓ ≥ 1` is used only for the norm, where the two intervals
  meet in a null set). In the supremum clause, `g` "supported in `[-ℓ, ℓ]`" is an element of `L2I ℓ`,
  `𝓕₋g(z) = ĝ(-z)`, and the supremum is attained (`IsGreatest`); the statement needs `ℓ > 0` (the manuscript
  has `ℓ ≥ 1`). `ℓ²(ℕ)`, `n ≥ 1`, is `lp (fun _ : ℕ+ => ℂ) 2` with its standard Hilbert basis, and `A` is
  `Hilbert.Diag.op` with `τ_n = n²` on its maximal domain `{(n²⟪e_n, x⟫) ∈ ℓ²}`, the manuscript's
  `{∑ n⁴|c_n|² < ∞}`.
* `AW5Spectral`: PARTIAL for `prop:aw5-contains` (iii). It combines (i) with `prop:hilbert` as the proof does and
  identifies `{τ_k}` with `{(ρ - j/2)/i : ρ ∈ spec Θ}` (as `∃ k, τ_k = μ ↔ Θ.HasEigenvalue (j/2 + iμ)`). AW5's
  unitary group `U_j` on `𝓗^j` and its generator `A_j` are not modelled (no Stone theorem in Mathlib), so the
  operator is the diagonal `diag(τ_k)` itself; the step "`T_j = -iA_j` is the closure of its restriction to
  `V^j`" is outside the encoding. The multiplicity clause is not stated. (iv) is not formalized.
* `R9`: (i) FAITHFUL, with `r` any complex number (the manuscript's `r ∈ ℝ` is not needed) and `G ≢ 0`
  implied by the finite order; the order statement for `E^#` is for `G - iG'`, which is `E^#` when `G^# = G`
  (`reflect_companion`). (ii) FAITHFUL ("simple zero" = `analyticOrderAt = 1`). (iii) is stated for a
  **bounded** self-adjoint `A : H →L[ℂ] H`, with "cyclic" meaning that `{Aⁿ v₀}` spans a dense subspace; the
  manuscript allows unbounded `A` with the resolvent orbit `{v₀} ∪ {R_z v₀}`. `dim ker(A - λ) ≤ 1` is
  `ker(A - λ) ≤ ℂ w`.
* `HbHigh`: FAITHFUL to the first clause of `prop:hb-high` for `F = riemannXiUpper` (`def:zeta` (d)). The
  proof uses `ζ ≠ 0` on `Re s ≥ 1` (Mathlib) in place of "all zeros lie in `𝕊`".

**Round 68: black boxes and their consumers.**
* `BlackBoxes.lean`: the four statements are verbatim those elaborated in
  `ai/2026-11-20-notes-lean-finish/checks/FinalBoxes.lean` (namespace changed to `WeilRH`). Docstring
  citations are chapter/section level (Neukirch Ch. VII §5; Titchmarsh Ch. VIII; Whittaker–Watson Ch. XII)
  except Deligne 1974; no pinpoint numbers were verified. No Stacks tag matches any box. B1 is stated for
  `K : Type` because its source is; every B1 consumer is therefore for `K : Type`, while the older
  hypothesis-form theorems stay universe-polymorphic.
* `HeckeCorollaries.lean`: each theorem is the earlier theorem applied to `hB.continuation`,
  `hB.simplePoles`; FAITHFUL to the same extent as the original, now CONDITIONAL on B1 instead of on
  unconstructed data. `Hecke.xiK` adds B1's order-one bound and independence from the continuation.
  `thm:A` (i) here is objectwise (`grh_of_awc`); the class form is `grh_dedekind_of_awc`.
* `XiKHadamard.lean`: FAITHFUL to `thm:imp-stirling` (iii) applied to `ξ_K` with the zeros indexed with
  multiplicity by `ZeroIdx` (`Nat.card` of each fiber is the analytic order). No `s^k` factor since
  `ξ_K(0) ≠ 0`. B1's `C‖s‖log‖s‖` bound is converted to B3's `2|C|‖s‖^{3/2}`. "Order one" itself is the
  growth bound, not Mathlib's order of growth (Mathlib has none for entire functions).
* `NLinesWeil.lean`: B2' does not state `#A₁ = 2g`, so `prop:N-lines` is proved for any smooth, proper,
  geometrically irreducible curve `X` (an elliptic curve is a special case; Mathlib has no scheme-level
  elliptic curve, so `X` is not required to be one), with numerator `∏_{α ∈ A₁}(1 - αq^{-s})(1 - αq^{1-s})`.
  The manuscript's `zetaX q α β` is the case `A₁ = {α, β}` (`zetaXM_pair`). Zero and pole locations need only
  purity. "Poles" is stated as "where the denominator vanishes" (no cancellation, `den_ne_zero_of_numM_eq_zero`);
  order and infinitude of poles are as in the round-9 `poles_zetaX` and are not re-derived for multisets. The
  `ℙ¹_F` point identification `e` stays a hypothesis (obligation 11). `exists_count_ne_zero` is the
  remark after `prop:formal-curve` for every `q`, not only `q = 3`.

**Round 71: fixes from the independent review of rounds 65–69.**
* `prop:xiK` (B1 form): now FAITHFUL apart from encoding conventions, CONDITIONAL on B1. The strip clause is
  stated for the entire `ξ_K`; the order clause uses `zetaCont`, which equals Mathlib's `dedekindZeta K` on
  `Re s > 1` and is holomorphic off `{0, 1}`, so by the identity theorem it is the continuation of `ζ_K`. It is
  stated for `0 ≤ Re s` (the manuscript has `0 ≤ Re s ≤ 1`; the extra range is harmless). Orders are
  `analyticOrderAt` (`zetaCont` is analytic at every `s ∉ {0, 1}`).
* `prop:N-count` (i) for `ξ_K`: the conjugation clause is proved (`NCount.xi_conj`); the round-68 row is no
  longer overstated.
* `prop:R2` (i): PARTIAL. `R2.axioms_block` ties the block's own degree-one generator, pairing `Tr(u ∪ v)` and
  star `*₁` to `Θ`, `Ω`, `S` in the basis `eb 0..3`, and shows `eb` spans `V¹`. Still not fields of
  `HermAlgebraDatum`: AW3 perfectness, associativity, graded commutativity (the latter two hold for the
  underlying `PairingModel.mul`: `mul_assoc'`, `mul_comm_graded`). The round-65 `R2.axioms` is kept.
* `prop:kun-arch`: the abstract hypotheses are discharged for any group of order two (with its nontrivial
  element and a nontrivial character) and at `Multiplicative (ZMod 2)`; `Gal(ℚ(i)/ℚ)` itself is not built.
* `thm:kun-square` (iv), `prop:N-lines` under B2': claim-table labels now state the assumed `κ` and the
  underived `#A₁ = 2` / two-term `zetaX`.
* B2': docstring cites Weil II (3.3.9) for the proper case. The pinpoint was corroborated only through a secondary
  source (Cadoret cites [D80, (3.3.9)] for integrality of the Frobenius characteristic polynomial of a smooth
  proper `X₀`); Weil II itself was not read in round 71.

**Round 72.**
* `prop:kun-hodge-strict`: FAITHFUL for the degree-one slice. The split-signature datum is encoded by its degree-one
  part as a `SurfaceDatum` (`Kunneth.lean`), whose fields are AW1 (derivation rule with weight one, from the trace
  to `ℂ(-1)`), AW3 (perfectness of `B`) and `def:aw4-alg`; degrees `0` and `2` (`V⁰ = ℂ·1`, `V² = ℂη`, the unit
  products, `*₀`, `*₂`) are not modelled, so "AW1 for `U = 𝟙`" is the degree-one rule only. Coordinates
  `0, 1, 2, 3` are `e₁, e₂, f₁, f₂`. `h_⊗` on `V_ρ ⊗ V_{ρ̄}` is the Kronecker product of the Gram matrices of `h₁`
  on `V_ρ` and `V_{1-ρ}` (`SurfaceDatum.blockGram`, as for C-K6), and `1 - ρ = ρ̄` on the line (`one_sub_ρ`).
  Stated for every real `γ`; the manuscript's `γ > 0` only makes `V_ρ = ℂe₁ ⊕ ℂe₂`, which is not used. The
  signature `(1, 1)` of `h₁` on `V_ρ` is shown as indefiniteness (`h(e₁, e₁) = 1`, `h(e₂, e₂) = -1`), and the
  manuscript's signature `(2, 2)` of `h_⊗` (via `thm:kun-hodge` (ii)) is shown only as failure of positive
  definiteness. AW4-V uses the standard form `∑ uᵢv̄ᵢ`, the orthogonal sum of positive forms on the two
  eigenspaces, as in the proof.
* `prop:R12`: FAITHFUL. `μ_a` and its transform `∫ e^{izt} dμ_a` are the round-1 `R12.μ` (a sum of Dirac masses)
  and `R12.fourier_eq`; simplicity of the zeros is stated as non-vanishing of the derivative `-sin z`; "none real"
  as `Im z ≠ 0`. In (ii) the transform is `∫ e^{izt} k_{a,σ}(t) dt` over `ℝ` with Lebesgue measure, for all
  `z ∈ ℂ` (proved directly with Mathlib's `integral_cexp_quadratic`, without the analytic-continuation step of
  the manuscript); "smooth" is `ContDiff ℝ ⊤`.
* `prop:beta` (superseded, round 79): PARTIAL. `P` is defined as `-(1/π) · dslope (w ↦ sin πw) 1`, which is entire by construction and
  equals `sin(πw)/(π(1 - w))` off `w = 1`; `P(1) = 1`. Not formalized: the identity
  `a^{-w} = P(w) ∫_0^∞ x^{1-w}(x + a)^{-2} dx` (the Beta integral on `(0, ∞)` and its continuation to
  `a ∈ ℂ ∖ (-∞, 0]`) and the expansion `(2π)^w P(w) = w + (1 + log 2π)w² + O(w³)`.
* `thm:kun-hodge`: not re-encoded this round. Its clauses (i) (first half), (iii) and the diagonalizability and
  `Re ρ = 1/2` parts of (iv) are the C-K6 declarations of `Kunneth.lean` (`h_eq_zero_of_re_ne_half`,
  `hodgeIndex_iff_pureDefinite`, `isSemisimple_of_hodgeIndex`, `re_eq_half_of_hodgeIndex`); that correspondence
  was not re-reviewed against the current `thm:kun-hodge` statement in round 72.

**Round 73: `prop:F0`, `def:regdet`, `prop:R3` (iii), `prop:rouche-route` (`EtaZeta.lean`, `RegDet.lean`,
`RegDetSum.lean`, `Hurwitz.lean`, `RoucheRoute.lean`).** Checked by the round author against the current
`notes.tex`; no independent review yet.

* `prop:F0`: FAITHFUL, now unconditional. `F_zero_pos` has the round-65 statement with the hypothesis
  discharged by `riemannZeta_half_re_neg`. The proof of `ζ(1/2) < 0` differs from the manuscript's step (a)
  (which cites the alternating series); it proves `ζ(σ) < 0` for every `σ ∈ (0, 1)`.
* `def:regdet`: FAITHFUL as a definition, with one representation choice. The spectrum enters as a set `S` with
  multiplicities `m` (for a spectral core, `spec Θ` and `Spectral.mult Θ`). Zeta-regularizability is a structure
  carrying its witnesses: for each `s ∈ U` an abscissa of absolute convergence, a meromorphic continuation on a
  preconnected open domain containing the half-plane and `0`, regular at `0`, the holomorphy of
  `s ↦ ∂_w Z(0; s)` on `U`, and the entire extension `D`; `detreg` is `D`. "Continues meromorphically to a
  neighbourhood of `w = 0`" is read as continuation along a preconnected domain from the half-plane, which
  makes the continuation unique; uniqueness of `D` is `D_unique`. The remark after the definition (finite `V`:
  `det_reg = ∏((s - ρ)/2π)^{m(ρ)}` independently of the cut) is `detreg_finite`, for every regularization.
* `prop:R3` (iii): FAITHFUL modulo the representation above. `det_sum` gives, for any regularization of
  `(S', m')` on a cut `c'`, a cut of `S' ∪ spec Θ` on an open `U₀ ⊆ U` with the same branches on `S'`, a
  regularization of `(S' ∪ spec Θ, m' + 1)`, and `det_reg = (2π)^{-4} p(s) det_reg'`. That `(S' ∪ spec Θ, m' + 1)`
  is the spectrum with multiplicities of `Θ' ⊕ Θ` (first sentence of the manuscript's proof) and that the sum is a
  spectral core are not restated. `U₀` is nonempty (it contains a chosen point of `U ∖ spec Θ`); the new branches
  are rotated principal logarithms. Uses `0 < a`, `0 < T` (distinctness of the four eigenvalues); `a < 1/2` is
  not needed.
* `prop:rouche-route`: FAITHFUL. Gap data as in `prop:gap` (gap as a lower bound on the eigenvalues of `A_j` on
  `v_j^⊥`; `v_j` need not be a unit vector). (b) "uniformly on compact subsets of `𝕊`" is
  `TendstoLocallyUniformlyOn` on the open strip (equivalent, `tendstoLocallyUniformlyOn_iff_forall_isCompact`).
  The conclusion is for every zero of `F` in `ℂ`; `riemannXiUpper_eq_zero_mem_strip` supplies the manuscript's
  "all of which lie in `𝕊`". `ĝ` entire (`Gap.differentiable_hat`) is used by the manuscript implicitly.

**Round 81: review fixes (`KunArchGal.lean`).**

* `prop:kun-arch` at `Gal(ℚ(i)/ℚ)`: FAITHFUL. `kun_arch_gal_divisors` states, for every complex embedding, the conjugation clauses of `kun_arch_gal` together with `ord_ρ L_∞(χ, ·) = −1` exactly at `ρ = −1 − 2n` and `ord_ρ L_∞(χ², ·) = −1` exactly at `ρ = −2n` (0 elsewhere), as meromorphic orders. Checked by the round author only.

**Round 80: scheme zeta, `prop:zeta-intrinsic`, `prop:xiK-asymp` (first expansion) (`SchemeZeta.lean`,
`XiKPrimeSum.lean`, `XiKAsymp.lean`).** Checked by the round author only.

* `ζ(X, s)`: FAITHFUL to the manuscript's formula. `X₀` is Mathlib's `closedPoints X` (points with closed
  singleton), `N(x) = Nat.card κ(x)`; the product is a `tprod`, so it is the Euler product wherever that
  converges (multipliable) and is otherwise Mathlib's junk value `1`. Convergence of the Euler product on a
  right half-plane for general `X` is NOT proved (it needs a count of closed points of bounded norm); it is
  proved for `X = Spec ℤ` (`zeta_specInt`). Schemes are in universe `0`.
* `prop:zeta-intrinsic`: FAITHFUL, in a sharpened form. The manuscript's statement "the same whether `X` is
  regarded over `Spec ℤ` or over `Spec 𝒪_K`" is encoded by defining, for a structure morphism `g : X ⟶ S`,
  the relatively closed points (closed in the scheme fibre `g.fiber (g x)` over a closed point of `S`) and the
  corresponding Euler product `zetaRel g`; `zetaRel_eq` shows it equals `ζ(X, s)` for every Jacobson `S`
  (both `Spec ℤ` and `Spec 𝒪_K` qualify) and `g` locally of finite type, and `zetaRel_eq_zetaRel` compares two
  bases. The manuscript requires separated and finite type; only locally of finite type is used.
* `prop:xiK-asymp`: PARTIAL and CONDITIONAL on B4'. `f` is `def:deninger-gamma` (e) with `log Γ = L` from B4'
  (`logGamma_eq_real`: `L` is the branch real on `(0, ∞)`, as the manuscript specifies), principal `log`, and the
  prime sum indexed by `(𝔭, k − 1)` over nonzero primes. "`z = s + x` as `x → +∞`, `O(|z|^{-1})`" is
  `=O[atTop] (fun x => ‖s + x‖⁻¹)`. The proof is the manuscript's for `f` (Stirling for `z` and `z/2`, `log(z − 1)
  = log z + O(1/z)`, the prime sum decaying like `2^{−Re z}`); the manuscript's bound of the prime sum via
  "at most `n` primes over `p`" is replaced by the injection `(𝔭, k) ↦ 𝔭^k` into the ideals. The `f'` and `f''`
  expansions (Cauchy estimates on discs of radius `|z|/4`) are not formalized.

**Round 79: `prop:beta` complete, `prop:kun-arch` at `Gal(ℚ(i)/ℚ)` (`BetaIntegral.lean`, `KunArchGal.lean`).**
Checked by the round author only.

* `prop:beta`: FAITHFUL. `a ∈ ℂ ∖ (-∞, 0]` is `a ∈ slitPlane`; "principal power" is Mathlib's `cpow`; the
  integral is the Bochner integral over `Ioi 0` of `(x : ℂ)^{1-w} ((x + a)^2)⁻¹`, and `integral_pos` also gives
  its integrability (for `a = r > 0`; for general `a` it follows from the local bound in
  `differentiableOn_integral`). The value at `a > 0` is obtained by Fubini rather than the manuscript's
  substitution `x = at` and the Beta function; the continuation in `a` is the manuscript's argument.
  `O(w³)` is `=O[𝓝 0] (fun w => w ^ 3)` in `ℂ`, and `log 2π` is the real logarithm.
* `prop:kun-arch` at `Gal(ℚ(i)/ℚ)`: FAITHFUL for the manuscript's group. `ℚ(i)` is `CyclotomicField 4 ℚ`
  (`ℚ(ζ₄) = ℚ(i)`); "complex conjugation" is `ComplexEmbedding.IsConj φ c` for an arbitrary embedding `φ` (any
  two choices give the same `c`, the group having order two); `χ` is `χ₄` transported along
  `Gal ≃* (ZMod 4)ˣ`, the unique nontrivial character. The decomposition group at the real place is the whole
  group (`ℚ(i)` is totally complex), and `c` generates it (`Subgroup.zpowers c = ⊤`).

**Round 78: review fixes, `prop:R15` (ii)–(iii), `prop:kun-diag` (iii)–(v), `prop:kun-AW6` (`RegDetSum.lean`,
`NKCount.lean`, `R15Tail.lean`, `R15Periodization.lean`, `KunDiag.lean`, `KunAW6.lean`).** Checked by the round author
only.

* `fidelity-76-77.md` fixes: (1) the round-73 `def:regdet` row is relabelled (superseded (c)); (2)
  `det_sum_onHalfPlane`; (3) `zeroSet_finite`, so `zeroCount` is not a junk `finsum`; (4) the B1 row names the
  B6-free round-77 forms.
* `prop:R15` (iii): FAITHFUL. The sums are indexed by `n : ℕ`; the `n = 0` term is `k₀(0) = 0`. `Σ_{n > λ/u}` is a
  `tsum` over the subtype `{n : ℕ // λ/u < n}`. Positivity uses only `λ ≥ 1` (`k₀(v) > 0` for `v ≥ 1`).
* `prop:R15` (ii): FAITHFUL. "Converges absolutely" is `IntegrableOn … (Ioi 0)`; `𝓔k₀(u) = u^{1/2} Σ k₀(nu)` with
  the real power; `ξ` is `completedXi`. The proof is the manuscript's (interchange justified by
  `Σ_n ∫|k₀(nu)|u^{σ−1} du = Σ n^{−σ} ∫|k₀|u^{σ−1} < ∞`).
* `prop:kun-diag`: PARTIAL, as recorded in its row. A diagonal operator's eigenvalues with multiplicity are its
  entries, so the counts are `encard`s of index sets; (iii)'s inequality is proved for `R ≥ 0`; for `R < 0` the left side is `0`, so it
  holds trivially, but that case is not stated separately. (v) reproduces the manuscript's two
  sequences and parameters exactly.
* `prop:kun-AW6`: CONDITIONAL on B1 and B3, and on hypotheses standing for `thm:rh`'s conclusion for the datum
  (every eigenvalue is `1/2 + iτ` with `ρ` a zero, and every zero occurs); these hypotheses imply RH for `ξ_K`, as
  `thm:rh` does under AW1–AW4. The manuscript's infinitude input (`thm:kun-square` (`item:ks-mult`)) is replaced
  by `Hecke.zeroIdx_infinite`.

**Round 77: revised `def:regdet`, B6-free `prop:hb` (`RegDet.lean`, `RegDetSum.lean`, `HbNoRvM.lean`,
`HbSum.lean`, `HbEquiv.lean`, `BlackBoxes2.lean`).** Checked by the round author only.

* Revised `def:regdet` (c): FAITHFUL as a predicate on a `Regularization`. "`Z(w; s)` continues to a meromorphic
  function on `Re w > -ε(s)`" is `{w | -ε s < w.re} ⊆ r.dom s` with `Z s` meromorphic on `r.dom s`; the domain may
  be larger than the half-plane, which is harmless because only the half-plane is used. `IsZetaRegularizable c m`
  is the revised (c) as a proposition. The paragraph after the definition is `detreg_eq_of_onHalfPlane`: the
  common domain `{Re w > -min(ε, ε')}` is convex, contains `0`, and contains a real point to the right of both
  convergence abscissae. Dependence on the cut is still not addressed, as in the manuscript.
* `prop:hb`, `prop:hb-high` (ii): the `'` forms differ from the round-75 forms only in their hypotheses (B6 dropped).
  The zero of `F` is `I(ρ - 1/2)` for a zero `ρ` of `ξ_ℚ = 2ξ` (`HeckePackage.xi_rat`) given by
  `Hecke.zeroIdx_infinite` (B1, and B3 from B3' via `hadamardOrderOne_of_LU`).
* Citations: B4' now cites DLMF (5.11.1) and §5.11(ii), checked at dlmf.nist.gov/5.11 on 2026-11-20. The
  Whittaker–Watson Ch. XII (B4'), Titchmarsh *Theory of Functions* Ch. VIII (B3') and Titchmarsh *Zeta-Function*
  Ch. IX (B6) citations stay chapter-level; no theorem numbers were checked for them.

**Round 76: `thm:window` (i), `prop:R15` (i), `N_K(T) = O(T log T)` (`WindowPoisson.lean`, `R15Mellin.lean`,
`NKCount.lean`).** Checked by the round author only.

* `thm:window` (i): FAITHFUL for complex-valued `φ` that is `C^∞` with compact support (the manuscript's
  `C_c^∞(ℝ)`; real-valued `φ` is a special case). `Φ(s) = ∫ φ(t) e^{st} dt` is `def:window-objects` (a) for `g = φ`.
  The sum over `C_L` is the sum over `n ∈ ℤ` of `Φ(1/2 + 2πi(n + 1/2)/L)`; `cosetPt_injective` shows this
  parametrization is bijective, so no point is counted twice. Convergence of the left side is proved, not assumed.
  The right side is a `tsum` over `k ∈ ℤ` with only finitely many nonzero terms.
* `prop:R15` (i): FAITHFUL. "Converges absolutely" is `MellinConvergent` (integrability of `u^{s-1} k₀(u)` on
  `(0, ∞)`); the value is stated with the principal power `π^{-s/2}` and Mathlib's `Γ`. The proof is the
  manuscript's: Gaussian moments `∫ u^{β-1} e^{-πu²} du = (1/2) π^{-β/2} Γ(β/2)` for `Re β > 0`.
* `N_K(T)`: `zeroCount T` counts zeros of the entire `ξ_K` of `HeckePackage.simplePoles` with `|Im ρ| ≤ T`,
  with multiplicity `analyticOrderNatAt`, as in the manuscript's definition. The bound is
  `N_K(T) ≤ C T log T` for `T ≥ 2`. The manuscript cites Hasanalizade–Shen–Wong for it; this proof instead uses
  B1's growth, the strip clause `Hecke.xiK_strip` and Jensen's inequality, so it is CONDITIONAL on B1 only.

**Round 75: `prop:hb-high` (ii), `prop:hb`, zeros of `ξ_K` (`HbSum.lean`, `HbEquiv.lean`,
`XiKZerosInfinite.lean`).** Checked by the round author only.

* `prop:hb-high` second clause: FAITHFUL for `F = riemannXiUpper` (`F(z) = ξ(1/2 - iz)`, `def:zeta` (d)), stated
  as `0 < Im(-logDeriv F z)` for `Im z ≥ 1/2`. The manuscript groups `r` with `-r` in the even product
  `F(0)∏(1 - z²/r²)`; here the genus-one product of B3' is used directly and the grouping is replaced by
  `𝔪(z) = (L(-z) - L(z))/2`, `L = F'/F`, which cancels `b` and `Σ 1/ρ` termwise (no reindexing of the zeros).
  Hypotheses: B1 for `ℚ` gives `log‖ξ(s)‖ ≤ C‖s‖ log‖s‖` (through `ξ_ℚ = 2ξ`, `HeckePackage.xi_rat`), transferred
  to B3''s `C‖z‖^{3/2}` form along `z ↦ 1/2 - iz`; B6 is used only for the existence of one zero (with no zeros
  the sum is empty and the strict inequality would fail; the manuscript takes existence for granted).
* `prop:hb`: FAITHFUL as a `List.TFAE` of the four conditions for this `F`, with `E = F + iF'` and
  `E^#(z) = conj(E(conj z))` (`def:hb` (a)–(c)). "`𝔪` is holomorphic on `ℂ⁺`" in (ii) is encoded as `F ≠ 0` on
  `ℂ⁺`, equivalent because `𝔪` has a simple pole of residue `-k` at a zero of order `k`. (iii) ⇒ (i) uses
  `R11.im_neg_logDeriv_lt_zero` (round 69) and evenness `F(-z) = F(z)` instead of reality to move a zero from the
  lower to the upper half-plane. (iv) ⇒ (i) is the manuscript's equal-moduli argument at a zero. (ii) ⇒ (iv) uses
  `eq:hb-modulus` (`normSq_E_sub`). `F^# = F` and `(F')^# = F'` come from `ξ(s̄) = conj ξ(s)`, now unconditional
  (`Hb.completedXi_conj`, via `XiKConj.xi_conj` for the `ℚ` continuation built from Mathlib).
* `zeroIdx_infinite`: the zeros of `ξ_K` with multiplicity (`Hecke.ZeroIdx`, round 68) form an infinite type,
  for every `K : Type`. This is the multiplicity-counted statement; infinitude of the zero *set* follows because
  each fiber is finite (`fiberEquiv`), but is not stated separately. The proof is not the manuscript's (which cites
  the counting function); it uses only B1, B3 and `(n-1)!` against `e^{Bn}` at the points `x = 2n`.

**Round 74: black boxes B3', B4', B6; review fixes; zeros from B6 (`BlackBoxes2.lean`, `RegDet.lean`,
`AW5Spectral.lean`, `ZetaZerosRvM.lean`, `KunOverZ.lean`, `P1ZZeros.lean`).** Checked by the round author only.

* Review fixes (`fidelity-70-73.md`): `prop:R3` (iii) relabelled PARTIAL in its row; `prop:kun-hodge-strict` row
  qualified as degree-one only; `prop:aw5-contains` (iii) multiplicity clause proved (`aw5_spectral_mult`, with
  `m_j` the algebraic multiplicity, equal to the eigenspace dimension because `Θ` is semisimple under AW5).
* `def:regdet`: `detreg_eq_of_common_domain` makes `det_reg` canonical under the stated common-domain condition;
  without it, continuations to `w = 0` along different domains need not agree. `notes.tex` `def:regdet` leaves
  the continuation domain unspecified, so the manuscript has the same ambiguity (reported to Taylor; the tex is
  not edited here). For finite spectra `detreg_finite` already shows independence unconditionally.
* `prop:kun-over-Z`: FAITHFUL modulo the encoding: the degree-one datum is `ArithmeticWeilCohomologyQMult`
  (`dim V¹_{Θ=ρ} = ord_ρ ξ`), and the degree-one part of the tensor square is taken to be `V¹ × V¹` with
  `Θ ⊕ Θ`, i.e. the manuscript's first proof step (`V⁰ = ℂ`, `Θ₀ = 0`) is built into the statement. The zero
  of `ξ` comes from B6 instead of the proof of `prop:P1Z`. The proof compares finite dimensions `m` and `2m`.
* `prop:P1Z`: the zero description, the strip clauses `Z ⊆ {0 < Re < 1}`, `Z + 1 ⊆ {1 < Re < 2}` and the
  vertical-line clause are stated for `zetaP1 s = ζ(s)ζ(s-1)` with `s ≠ 1, 2`; `ζ_X = zetaP1` is not proved
  (obligation 32). `Z` is `IsNontrivialZetaZero`. Nonemptiness and the vertical-line clause use B6.
* `ZetaZerosRvM`: standard consequences of B6; `exists_zero_im_gt` is the existence/infinitude input.

## Open obligations

1. Encode the analytic side of AW2: zeta-regularized determinants `det_∞`, (AW-det), the endpoint
   determinants `D₀ = s/2π`, `D₂ = (s−1)/2π` and the regularized value `D₁ = 2^{-1/2} ξ/2π²`
   (Deninger 1998 p. 168; identity (1) of the Sept-19 record is superseded by its erratum, ruling
   R-1). (Round 73: `def:regdet` is now encoded, `RegDet.lean`, and `prop:R3` (iii) is done; still open are the
   infinite-spectrum determinants above, `thm:det-K`, `prop:ff-cut`, `prop:N-count` (ii).) (The zero-order condition itself is
   now encoded: `ArithmeticWeilCohomologyQMult`; `ξ` and its zeros: `Completed.lean`.)
2. Hecke's continuation/functional equation for `Λ_K` in Mathlib: since round 68 the black box B1
   `HeckePackage K` (proved at another pin in AxiomMath/RiemannJensen; backport about 9k lines from
   Mathlib v4.36 would remove it), which yields `DedekindContinuation K`; a multiplicity-faithful
   `ArithmeticWeilCohomology` for general data; Theorem A (2)–(3) via class field theory / Brauer.
3. AW5 (Stone's theorem, unbounded generator, Hilbert completion); the flow form for unbounded
   generators.
4. R4.
5. Theorem 1′ over `ℚ`, `ℝ` (base change) and Corollary 1″; the full `ℤ`-indexed suspension and the
   nonsemisimple / determinant parts of Q2 §6; a `WeightedStarDatum` packaging of R2.
6. Künneth Theorem 6 beyond the finite-dimensional block model: the signature formula for tensor
   products of Hermitian forms, Theorem 6(ii) nondegeneracy, 6(iv) (Rosati/Castelnuovo trace form),
   the completion and diagonal/graph classes (Prop. 6), and a genuine `V¹ ⊗ V¹` with the global `h_S`.
7. Round 5's statements about `V̂` itself: (ii) and `prop:ff-phantom` (ii) were done in round 14
   (`theta_sheetMap`, `spec_theta_phantom`) and (iii) in round 15 (`exists_aw4EAdd_suspension`),
   and the sheet spaces in round 16 (`sheetEquiv`, `isInternal_sheetSpace`): all statements about
   `V̂` itself are now done. Still open here: the geometric
   input of `prop:rosati-EF`; items (i)–(ii) of `thm:ff-lefschetz` (`Tr(F^k) = ∑ α^k` for linear maps is
   done in round 69, `LefschetzTrace.trace_pow_eq_sum_roots`); étale derived categories, t-structures and cochain enhancements for
   `prop:EM`, `prop:EM-criterion`.
8. Done in round 8 (`prop:B-support` from AW1 and AW3: `cupTrace_eq_zero_of_mem_maxGenEigenspace`).
   (Directness and the multiplicity formula of `prop:tensor-eigen` were done in round 7.)
9. Done in round 10 (`SpectralCore`, `SpectralCore.tensor_eigen`, `finrank_maxGenEigenspace_tensorSum`).
   The failure of the spectral-core condition on `V ⊗ W` when the sums are infinite is done in round 67
   (`KunSquare.not_finite_of_pairs_infinite`; `thm:kun-square` (iv)).
10. Done in round 9 (`prop:weil-converse` (ii) as stated: `isFrobPol_iff_exists_assemble`,
    `restrict_assemble`).
11. Round 9, extended in the Axiom Math investigation: the remaining geometric inputs of
    `prop:N-lines` are the `ℙ¹_F = Proj F[X₀,X₁]` scheme-point to projectivization equivalence and the elliptic
    Frobenius count `#E(𝔽_{qⁿ}) = qⁿ + 1 - αⁿ - βⁿ` (Hasse–Weil). The product count and finite
    extension cardinalities are proved; under the two remaining inputs, the zeta function of
    the actual scheme product equals `zetaX` on `Re s > 2`. Round 68: the Frobenius count now comes from
    B2' `WeilConjectures` for any curve (`nLines_of_weil`, multiset form); B2' does not give `#A₁ = 2`, so
    the two-term form needs `A₁ = {α, β}` as input. Still open: the `ℙ¹_F` point equivalence `e`, and
    uniqueness of the meromorphic continuation of `ζ_X`.
12. Round 11: `prop:formal-curve` is complete as linear algebra. The remark after it is done in round 68,
    conditional on B2' (`exists_count_ne_zero`).
13. Round 12: `q^Θ = F` on summands (the remark after `def:log-susp`), which needs
    `exp(log(1 + U)) = 1 + U` for nilpotent `U` (a formal power-series identity not in Mathlib in this
    form) and an exponential on `End_ℂ(V̂_ρ)`. Round 69: Mathlib now has `IsNilpotent.exp` and
    `PowerSeries.subst_exp_log`; what is missing is the bridge evaluating a truncated substitution at a
    nilpotent endomorphism (`aeval U (trunc N f)` is multiplicative modulo `U^N = 0`), about 150 lines;
    `prop:susp-product` (cup products on the graded `V^•`
    of `thm:imp-weil-coh`, not modelled). Done: the factorization of `det(1 − F q^{-s})` and its zero
    orders (round 14: `det_one_sub_smul_eq_prod`, `analyticOrderAt_det`); `prop:susp-converse`
    (round 13: `isFrobPol_restrictedForm`).
14. Round 16: `prop:kun-tensor` beyond its positivity and block-structure ingredients: a graded
    Weil-datum structure with product, the tensor datum of `def:tensor-datum` (Koszul signs, signed
    pairing, `* ⊗ *̃`) and AW1/AW3/AW4 for it. Not attempted: `prop:perm-span` (Artin's induction
    theorem for rational characters; not in Mathlib) and `prop:real-coeff` (needs `W(σ)`, Artin
    `L`-functions and Galois descent).
15. Round 21: `thm:kun-Fq` (i), the flow-module tensor product `V̂ ⊗_{𝟙_q} Ŵ` and its isomorphism with the
    suspension of `(V ⊗ W, F ⊗ G)`; (ii), the étale Künneth input. (`prop:R11` (iv) is done in round 69,
    `R11.im_neg_logDeriv_lt_zero`.)
16. Round 22: `prop:kun-susp-tor` (needs the flow-algebra structure and isomorphisms of
    `thm:kun-Fq` (i), obligation 15, and `Tor` over `R̂`). (`prop:aw4-forms` (ii)–(iii) and the
    Kurokawa cone of `prop:kun-orbits` (iii) were done in rounds 23 and 25.)
17. Round 24: `prop:aw5-contains` (iii)–(iv) (the Hilbert completion `𝓗^j`, the self-adjoint `T_j`
    and its spectrum, trace class under (G); needs `prop:hilbert`) and the full AW5 condition on
    `𝓗^j`; the `detreg` clause of `prop:one-branch` (obligation 1).
18. Round 26: `prop:hilbert`. Closed in round 37: the completion, the eigenvector Hilbert basis,
    `Θ = j/2 + iT` on `V`, `diag(τ_k)` on its maximal domain with `T = T^*` (round 33), and the
    spectral clause (`exists_spectral`, stated through eigenvectors and the resolvent because
    Mathlib has no spectrum for unbounded operators) are all formalized.
19. Round 27: `prop:kun-cone` (i) (needs `H^•` and `κ` of `thm:kun-square`). The `prop:R7` part
    is closed in round 28.
20. Rounds 28–29, 32: `def:trivial-model` and `prop:trivial-model`. The degree-one slice is built
    and (i)–(iii) are proved on it in round 29 (`TrivialModel.lean`); round 32
    (`TrivialModelFull.lean`) adds degrees `0` and `2`, the associative graded-commutative unital
    product with `Θ` a derivation, and AW3's blockwise perfectness. Round 35
    (`TrivialModelGraded.lean`) packages all degrees as one `WeightedAlgebraDatum (Tot ι) 1 0` and
    gives `V^0 ≅ 𝟙` (unital, multiplicative, `Θ_0 ↦ 0`) and `V^2 ≅ 𝟙(-1)` (`Θ_2 ↦ 1`, trace =
    coefficient). Round 36 removes the finiteness assumption (`gradedModelInf`, via
    `SpectralCore.of_equiv`). Still open: `𝟙` is
    encoded as `ℂ` with flow `0` and its own multiplication, not as an object of a category of
    spectral cores with a tensor product.
    Round 38 (`Unit.lean`) proves `𝟙` is a unit for the tensor of spectral cores (`V ⊗ 𝟙 ≅ V`,
    `V ⊗ 𝟙(-k) ≅ V(-k)`) and builds `𝟙_q` with its product; a category of spectral cores with a
    monoidal structure is still not formalized.
21. Round 30: `prop:content`. (i) and (iv) need `div ξ_K` for number fields (`prop:xiK`) and the
    full AW1–AW4 on `X̄_K`. (iii) is assembled in round 31 on the degree-one slice and extended to
    degrees `0` and `2` in round 33 (`ContentGraded.lean`). Unlike the trivial model (round 35), the
    assembled indefinite datum is **not** packaged as a `WeightedAlgebraDatum`: that structure
    requires positive definite `h_j`, which `prop:content` (iii) shows fails off the line. Round 36
    packages it as `HermAlgebraDatum` (Hermitian nondegenerate forms; `ContentAssembly.gradedDatum`)
    for finite divisors; round 37 proves the degree-one spectral-core condition for block data
    (`PairingModel.spectralCore_theta`) and gives the datum for any divisor with finite
    multiplicities and no finite accumulation point (`gradedDatumInf`). Round 51 closes (i) and (iv) in
    degree one (`ContentXiK.content_free`, `content_iff`), given Hecke's continuation and simple poles.
22. Round 41: `prop:algebra-form` over `k ∈ {ℚ, ℝ}` and the first clause of `prop:unit`. Both done in
    round 69 (`AlgebraFormReal`, without base change of the minimal polynomial or of positivity;
    `UnitProduct`).
23. Round 44: Arakelov roadmap (`lean/ROADMAP-arakelov.md`). A1 done except excellence (no Mathlib
    notion). A2 in progress: `X_∞ = X_S(ℂ)` as the set of `ℂ`-points over `S` with the involution
    from `F_∞` (as a set, then as a complex manifold once Tier B exists). Next: A3 (`ArakelovVariety`,
    GS 5.1.1, with the Kähler datum as an interface).
    Round 45: A2 done as sets (`complexPoints`, `Finf`); A3 started (`ArakelovVariety` with
    `KahlerInterface`, proper instead of projective generic fibre). Remaining for A3: add the real Hodge
    structure on `H*(X(ℂ))` with `F_∞` to the interface (roadmap §6b, FM path), and the lemma
    "regular flat over ℤ ⇒ smooth generic fibre" (roadmap A3). Next: A4 (`\Schbar` and its
    subcategories) and D1 (`X̄_K`, orbits of `F_∞` ↔ `InfinitePlace`).
    Round 46: A4 done (`CompactifiedScheme`, `Schbar`, `Schbar.reg` without pure dimension, `Schbar.proj`)
    and D1 done (`Xbar.obj`, orbits of `F_∞` = infinite places, `#X_∞ = [K : ℚ]`). Remaining: `\Schbar_1`
    with finite disjoint unions, and the equivalence with number fields (D2, `prop:A1-number-fields`).
    Round 47: D2 done on connected objects (`NumberFieldCurves.homEquiv`, `NumberFieldCat.arithEquiv`).
    Remaining: `\Schbar_1` with finite disjoint unions (not needed for a theory on connected objects, N12).
    Next: C1 (`ĈH¹(Spec 𝓞_K)` and the arithmetic degree, GS 3.4.3, §4.3).
    Round 48: C1 done for the degree (`ArithChow.ChowGroup`, `chowDegree`, `deg_principal`,
    `chowDegree_surjective`). Remaining for C1: the map `ĈH¹ → Cl(𝓞_K)` and its kernel, and injectivity of
    `deĝ` for `K = ℚ`. Next: D3 (`Λ_K`, `ξ_K`, `prop:xiK`).
    Round 49: C1 done (`toClass`, exactness, `chowDegreeEquivRat`). D3 started (`XiK.lean`); remaining: a
    `simplePoles` field for `DedekindContinuation` (entire `ξ_K`, `ξ_K(0) ≠ 0`), the Euler product of
    `ζ_K` (nonvanishing for `Re s > 1`), and the order comparison on the strip. Next: finish D3 as far as
    Mathlib allows, then D4 (FM's `ζ(X̄_K, s) = e^{a+bs} Λ_K`).
    Round 50: D3 done as far as Mathlib allows (`SimplePoles`: `ξ_K` entire, `ξ_K(0)ξ_K(1) ≠ 0` proved from
    the class number formula); remaining for D3: the Euler product of `ζ_K` (nonvanishing for `Re s > 1`)
    and the order comparison on the strip. D4 done (`ArakelovZeta.zetaFM_eq`, `analyticOrderAt_xiFM`).
    Next: D5 (`Σ_K = div ξ_K`; `prop:content` (i), (iv)).
    Round 51: D5 done in degree one (`ContentXiK.lean`). With it the dimension-one block of the minimum
    viable path (A1–A4, D1–D5, C1) is done, modulo the recorded Mathlib gaps (excellence, projective
    morphisms, analytification, `\Schbar_1` coproducts, the Euler product of `ζ_K`).
    Round 52: Flach–Morin path started (`HodgeInfty.lean`): the Hodge-datum interface, FM's `L_∞` and
    `ζ(X_∞, s)`, computed for `X̄_K`. Positive-dimensional instances need analytification and Hodge theory.
    Round 53: FM path E2 in all degrees for `ℙⁿ_{𝓞_K}` (`HodgeProj.lean`): Hodge numbers computed,
    `ζ(X_∞, s) = ∏_k Γ_ℝ(s−k)^{r₁}Γ_ℂ(s−k)^{r₂}`, FM's completed `ζ(ℙ̄ⁿ, s)` (with `ζ(ℙⁿ_{𝓞_K})` definitional).
    Round 54: FM path E3 started (`WeilArakelov.lean`): `DeligneDatum` interface; FM (2)–(5) for `∪θ` on
    cohomology (acyclicity, kernel and cokernel); the Dirichlet regulator of `X̄_K` in degree one.
24. **Closed in round 73** (`EtaZeta.lean`, `F_zero_pos`). Round 65: `prop:F0` needs `ζ(1/2) < 0` (equivalently, `ζ(s) < 0` on `(0, 1)` at `s = 1/2`). Missing from
    Mathlib v4.34.1: the Dirichlet eta function `η(s) = Σ (−1)^{n−1} n^{−s}`, its convergence and analyticity on
    `Re s > 0`, and the identity `η = (1 − 2^{1−s}) ζ` there (or any sign or zero-free statement for `ζ` on
    `(0, 1)`). Everything else in `prop:F0` is proved (`completedXi_half_pos_iff`).
    Round 66 rechecked Mathlib v4.34.1: no route exists short of new analysis. `ZetaAsymptotics` has
    `ζ(s)/s = 1/(s−1) − ∫_1^∞ {x} x^{−s−1} dx` only for `s > 1` (no continuation of the integral to `(0, 1)`, which
    would give `ζ(s) ≤ s/(s−1) < 0` at once); the Mellin route needs `Λ₀(1/2) < 4` for
    `Λ₀ = completedRiemannZeta₀`, i.e. explicit estimates of the theta-kernel integral of `hurwitzEvenFEPair 0`.
    Either is a self-contained analysis project (size L), not a black box.
25. Round 66: `prop:no-positivity-cancel` beyond `η` (`def:adjoin-pair`). `DeningerStructure` does not require
    `V = ⊕_j V^j`, so the adjunction's product `1 ∪ x = x` for new `x`, all other products with new vectors zero,
    is not definable on `V ⊕ ℂ⁴` without a projection of `V` onto `ℂ · 1`; it needs either an
    `DirectSum.IsInternal G` hypothesis or a refactor to an external graded sum. Then: associativity, graded
    commutativity and the derivation rule on the new products, generalized eigenspaces of `Θ ⊕ Θ_new` (spectral
    cores of `V^j ⊕ L_j`), AW3 nondegeneracy for the new lines, invariance of `eq:aw-div`, and the change of
    `Sp_1, Sp_2, Sp_3`.
26. Round 67: `prop:N-count` (ii) (the spectral zeta function of `Σ'` has a simple pole at `w = 0`; needs
    `thm:det-K` and zeta-regularized determinants, obligation 1). `thm:kun-square` (i)–(ii) and the selection
    step of (iii) (need the surface datum of `def:kun-notation` and, for `K = L`, the infinitude of the zeros of
    `ξ_K`). The Galois input of `prop:kun-arch` (decomposition group at the real place of `ℚ(i)/ℚ`). Not
    attempted: `thm:kun-hodge`, `prop:kun-hodge-strict` (need `h_⊗` of `def:kun-notation` and the split
    datum; obligation 28). (`prop:unit` first clause and `prop:algebra-form` over `ℚ`, `ℝ`: round 69.)
27. Round 68: consumers of B4. `prop:xiK-asymp` needs a complex `log Γ` on `ℂ ∖ (-∞, 0]` (not in Mathlib)
    with a *holomorphic* Stirling remainder, for the Cauchy estimates on `R'`, `R''`; B4 gives only a
    pointwise `R`, so either B4 is strengthened (the source's remainder is the restriction of a
    holomorphic function on `Re s > 0`) or the holomorphy is derived. `thm:det-K` additionally needs
    `def:regdet` (obligation 1) and the zero count `N_K(T) = O(T log T)`. B2' is not kernel-checked:
    with ≥ 30 GB free, run `lake exe cache get && lake build` in AxiomMath/Weil@27cdb20 and compile
    `example : WeilConjectures := fun F _ _ X _ _ d _ => weil_conjectures F X d` there.
28. Round 69, not reached: `prop:aw5-contains` (iii)–(iv) (concretely: `T_j` diagonal in the eigenbasis of
    `prop:hilbert`; trace class under (G)); `prop:gap` (the `L²` bound is finite-dimensional linear algebra; the
    strip bound needs the Fourier–Laplace transform on `L²([-ℓ, ℓ])`); `prop:R16` (explicit `ℂ³`, `L²` and
    `ℓ²` examples); `thm:kun-hodge`, `prop:kun-hodge-strict` (model `h_⊗` and the split-signature datum
    first). None needs a black box. Round 70: `prop:gap`, `prop:R16` and the diagonal model of
    `prop:aw5-contains` (iii) are done; the rest moves to obligation 29.
29. Round 70, not done. `prop:aw5-contains` (iii): the identification of `diag(τ_k)` with `-iA_j` for AW5's
    unitary group (needs `U_j` on `𝓗^j` and Stone's theorem or a direct generator computation) and the
    multiplicity clause; (iv): trace class (needs `U_j`, condition (G), `prop:exp-unique` (i) and trace-class
    operators). `prop:hb-high` second clause (`Im 𝔪 > 0`; needs the Hadamard product `eq:hb-product`).
    `q^Θ = F` (obligation 13: evaluating `PowerSeries.subst_exp_log` at a nilpotent endomorphism).
    `prop:R9` (iii) for unbounded `A` with resolvent cyclicity. Not attempted: `prop:beta` (Beta integral
    and its continuation in `a`), `prop:ff-cut` (needs `def:regdet`), `prop:zeta-intrinsic`, `prop:P1Z`,
    `prop:kun-tate` (i) (need a scheme-level zeta over `Spec ℤ`), `thm:kun-hodge`, `prop:kun-hodge-strict`.
30. Closed in round 75 (`riemannXiUpper_im_neg_logDeriv_pos`, under B1 for `ℚ`, B3', B6). Round 71. `prop:hb-high` second clause (`Im 𝔪 > 0`): B3 (`HadamardOrderOne`) supplies only a pointwise
    `HasProd` with `e^{a+bs}` and genus-one factors; the argument needs the even product `F(0)∏(1 - z²/r²)` of
    `eq:hb-product` with **locally uniform** convergence (Mathlib's `logDeriv_tprod_eq_tsum` takes
    `MultipliableLocallyUniformlyOn`). Deriving local uniformity from `Σ‖ρ‖⁻² < ∞` (Weierstrass M-test for products)
    and the even regrouping is size L; no new box is needed. Still not attempted: `prop:beta`, `prop:ff-cut`,
    `prop:zeta-intrinsic`, `prop:P1Z`, `prop:kun-tate` (i), `thm:kun-hodge`, `prop:kun-hodge-strict`. `prop:kun-arch`:
    `Gal(ℚ(i)/ℚ)` as `ℚ(i) ≃ₐ[ℚ] ℚ(i)` with complex conjugation is not constructed (the order-two instance covers it
    once that group and element are given).
31. Round 72. `prop:beta`: the Beta integral `∫_0^∞ x^{1-w}(x + a)^{-2} dx = a^{-w}Γ(2 - w)Γ(w)` for `a > 0`
    (Mathlib's `betaIntegral` is on `[0, 1]`; needs the substitution `x = t/(1 - t)` with complex powers), its
    holomorphic continuation in `a` to `ℂ ∖ (-∞, 0]`, and the expansion `(2π)^w P(w) = w + (1 + log 2π)w² + O(w³)`.
    `thm:kun-hodge`: (ii) the signature `(p² + q², 2pq)` of `h_⊗` (needs Sylvester's law of inertia / eigenvalues of
    a Kronecker product of Hermitian matrices), the nondegeneracy and equal signature of `h₁` on `V_ρ`, `V_{1-ρ}`,
    (iv) AW4-V/AW4-E and the link to `ξ_K` via AW1/AW2, (v) (surface datum not modelled) and (vi) (`Φ_ρ`, Rosati
    trace form); a fidelity relabel of the C-K6 rows. Not attempted (time): `prop:R15`, `prop:schwartz`,
    `prop:arch-window-limit`, `thm:window` (i) (Poisson summation for `C_c^∞`), `q^Θ = F` (obligation 13),
    `prop:ff-cut`, `prop:zeta-intrinsic`, `prop:P1Z`, `prop:kun-tate` (i).
32. Round 73, not done. `prop:zeta-intrinsic`, `prop:P1Z` (product formula) and `prop:kun-tate` (i) need a
    scheme-level zeta function `ζ(X, s) = ∏_{x closed}(1 - N(x)^{-s})^{-1}` for schemes of finite type over `Spec ℤ`
    with finiteness of residue fields at closed points (Jacobson/Nullstellensatz for finite-type `ℤ`-algebras),
    the count of closed points of `ℙ¹_ℤ` over each `p`, and absolute convergence of the Euler product; a faithful
    `prop:zeta-intrinsic` also needs closed points relative to a base `Spec 𝒪_K` (closed in their fibre over a
    closed point) to agree with closed points of `X`. Estimated L, not M. `thm:det-K`, `prop:ff-cut`,
    `prop:N-count` (ii) need infinite-spectrum regularized determinants (`thm:ff-det`, Hurwitz-zeta continuation)
    on top of `def:regdet`. Not attempted (time): `prop:beta` integral (obligation 31), `prop:R15`,
    `prop:schwartz`, `thm:window` (i).
33. Round 74, not reached. Under B1, B3', B4': `prop:xiK-asymp` (Cauchy estimates on the holomorphic Stirling
    remainder of B4'), infinitude of the zeros of `ξ_K` (B1 + B3'), `N_K(T) = O(T log T)` (B1 + Jensen,
    `MeromorphicOn.circleAverage_log_norm`), `prop:hb-high` second clause, `prop:hb`, `kun-AW6` (B3': the even
    regrouping `F(0)∏(1 - z²/r²)` of `eq:hb-product` and vanishing of `b` from evenness remain), `thm:det-K`.
    `prop:P1Z` product formula remains obligation 32. B2' still not kernel-checked (about 30 GB needed).
    Round 75 closes `prop:hb-high` second clause, `prop:hb` and the infinitude of the zeros of `ξ_K`.
34. Round 75, not reached. `prop:xiK-asymp` (needs the standard branch of `log ξ_K` of `def:deninger-gamma` (d), (e),
    Cauchy estimates on B4''s holomorphic remainder, and the prime-sum bound); `N_K(T) = O(T log T)` (B1 + Jensen);
    `prop:kun-AW6` (needs the Hilbert tensor sum `T₁ ⊞ T₁` of `prop:kun-diag`, not modelled; its zero input is now
    `zeroIdx_infinite`, with the conjugation symmetry of `XiKConj`); `thm:ff-det` (Hurwitz-zeta continuation for one
    progression), then `thm:det-K`, `prop:N-count` (ii), `prop:ff-cut`, `det-K-rf`, `Zpm`, the detreg clause of
    `prop:one-branch`; obligation 32 (scheme zeta over `Spec ℤ`).
35. Round 76, not reached. `prop:xiK-asymp` (define the standard branch of `def:deninger-gamma` (e) with B4''s `L`,
    which agrees with the real-on-`(0,∞)` branch since `L 2 = 0`; bound the prime sum by
    `Σ_p Σ_k Np^{-kσ}/k ≤ 2^{2-σ}(ζ_K(2) - 1)` and its derivatives by Cauchy estimates on unit discs; Cauchy estimates
    on radius-`|z|/4` discs for B4''s remainder); obligation 32; `prop:kun-diag` modelling and `prop:kun-AW6`;
    `prop:R15` (ii) (interchange of sum and integral, `integral_tsum_of_summable_integral_norm`) and (iii)
    (summability of `k₀(nu)` and positivity of `k₀` on `(1, ∞)`); `prop:beta` integral (obligation 31);
    `prop:schwartz`; `q^Θ = F` (obligation 13); `prop:arch-window-limit`; `N_K(T+1) − N_K(T) = O(log T)`.
    The determinant family (`thm:ff-det`, `thm:det-K`, `det-K-rf`, `Zpm`, `prop:ff-cut`, `prop:N-count` (ii),
    the detreg clause of `prop:one-branch`) waited on the `def:regdet` manuscript change (made 2026-11-20; see 36).
36. Round 77. `thm:ff-det` needs the Hurwitz zeta function `ζ_H(w, z)` for complex `z` (Mathlib's `HurwitzZeta` takes
    `a ∈ ℝ/ℤ`), its meromorphic continuation in `w`, `ζ_H(0, z) = 1/2 - z` and Lerch's formula
    `∂_w ζ_H(0, z) = log Γ(z) - ½ log 2π` (`thm:imp-hurwitz`). The rest of the determinant family (`thm:det-K`,
    `det-K-rf`, `Zpm`, `prop:ff-cut`, `prop:N-count` (ii), the detreg clause of `prop:one-branch`) builds on it.
    No black box was added for it.
37. Round 78. `prop:kun-diag` (i)–(ii) (Hilbert tensor product, self-adjointness, compact resolvent as operator
    properties); the Weil datum behind `prop:kun-AW6`'s hypotheses (via `thm:rh`, `prop:hilbert`). Still open from
    35: `prop:xiK-asymp`, obligation 32 (scheme zeta, `prop:P1Z` product formula, `prop:zeta-intrinsic`,
    `prop:kun-tate` (i)), `prop:beta` integral (obligation 31), `prop:schwartz`, `q^Θ = F` (obligation 13),
    `prop:arch-window-limit`, `N_K(T+1) − N_K(T) = O(log T)`. `prop:R15` is closed.
38. Round 79. `prop:beta` and the `Gal(ℚ(i)/ℚ)` instantiation of `prop:kun-arch` are closed (obligation 31's
    Beta integral). Still open from 37: `prop:xiK-asymp`, obligation 32 (scheme zeta, `prop:P1Z` product formula,
    `prop:zeta-intrinsic`, `prop:kun-tate` (i)), `prop:schwartz` (Schwartz bounds for
    `exp(-(1+t²)^{1/4})` of all orders, plus `Σ_𝔭 N𝔭^{-1} = ∞` from the pole of `ζ_K`), `prop:arch-window-limit`
    (needs `ψ(1/4) = -γ - π/2 - 3 log 2`), `q^Θ = F` (obligation 13), `prop:susp-product`, `weil-form`,
    `kun-collapse`, `kun-susp-tor`, `scholze-fixed-radius`, `thm:kun-hodge` (ii), (v), (vi),
    `N_K(T+1) − N_K(T) = O(log T)`.
39. Round 80. Obligation 32 is partly closed: `ζ(X, s)` is defined, residue fields at closed points are finite,
    `prop:zeta-intrinsic` and `ζ(Spec ℤ, s) = ζ(s)` are proved. Still open: absolute convergence of the Euler
    product for general `X` of finite type over `Spec ℤ` (count of closed points of bounded norm); the grouping
    `ζ_X(s) = ∏_p Z(X_{𝔽_p}, p^{-s})` and the comparison of the closed-point zeta of `X_{𝔽_p}` with the
    point-count zeta `exp Σ_m #X(𝔽_{p^m}) t^m/m` (closed points of degree `m` ↔ Frobenius orbits), which give
    `prop:P1Z` (`ζ_{ℙ¹_ℤ} = ζ(s)ζ(s − 1)`) and `prop:kun-tate` (i); the `f'` and `G_ξ = −f''` expansions of
    `prop:xiK-asymp` (Cauchy estimates for B4''s remainder on discs of radius `|z|/4`, and for the prime sum).
    Not attempted: the rest of obligation 38.
