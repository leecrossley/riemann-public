/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.RH
import WeilRH.Completed

/-!
# The Dedekind class `𝒞_Ded` and Theorem A (Q1), plus Dirichlet L-functions

Source: `ai/2026-09-25-zeta-class-axioms/report.md`, §2 (completed zeta functions `Λ_K`), §5.1
Theorem A (1): a polarized Deninger structure satisfying AW2 (notes `def:deninger-structure`,
`def:polarizable`) on every `X̄_K` ⇒ every zero of every `Λ_K` lies on `Re s = 1/2`.

## What Mathlib v4.34.1 provides, and what we assume

* `NumberField.dedekindZeta K` is the **L-series** `∑ #{I : N(I) = n} n^{-s}`. It is the true
  `ζ_K(s)` only for `Re s > 1`; Mathlib has **no** meromorphic continuation, functional equation,
  or completed `Λ_K` for general `K` (only the residue at `s = 1`).
* Mathlib has `Complex.Gammaℝ s = π^{-s/2} Γ(s/2)`, `Complex.Gammaℂ s = 2 (2π)^{-s} Γ(s)` (the
  report's `Γ_ℝ`, `Γ_ℂ`), `NumberField.discr K`, `nrRealPlaces K = r₁`, `nrComplexPlaces K = r₂`.

Hence the Dedekind datum is **parametrized by a continuation**: `WeilRH.DedekindContinuation K`
bundles a function `Λ` that is holomorphic on `ℂ ∖ {0, 1}`, equals
`|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s)` for `Re s > 1`, and satisfies `Λ(1 - s) = Λ(s)`. These
are theorems (Hecke) that Mathlib does not yet have; we take them as data, **not** as axioms.
We prove that `Λ` is unique on `ℂ ∖ {0, 1}` (`DedekindContinuation.eqOn`), so the nontrivial-zero
predicate and GRH do not depend on the chosen continuation (`dedekindDatum_grh_iff`). For
`K = ℚ` we construct the continuation from Mathlib's `completedRiemannZeta`
(`DedekindContinuation.rat`, using `dedekindZeta_rat : ζ_ℚ = ζ` on `Re s > 1`, proved here), so
the class-level theorem genuinely specializes to Mathlib's `RiemannHypothesis`
(`riemannHypothesis_of_grh_dedekind_class`).

The nontrivial zeros of `ζ_K` are the zeros of `Λ_K` (report §2); `Λ_K` has poles at `0, 1`,
where the function `Λ` of a continuation carries junk values, so the predicate is
`Λ ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1`. The pole structure and the order-one growth of `ξ_K` are not encoded.

## Dirichlet L-functions

`dirichletDatum χ` is a second, fully concrete member of `𝒞` (Mathlib has `DirichletCharacter.LFunction`
with continuation): nontrivial zeros are zeros of `L(χ, s)` in the open strip `0 < Re s < 1`
(the form of Theorem A (2)).

## Scope

As everywhere in this project, `ArithmeticWeilCohomology D` (the degree-`j` slice of a polarized
Deninger structure; the name is historical) encodes AW2 as "spectrum = nontrivial zeros" and
polarizability as (P); by `WeilRH.nonempty_arithmeticWeilCohomologyQ_iff`-type converses its
existence is a reformulation of GRH for `D`. Functoriality on `𝒜`, Galois descent, Brauer
induction (Theorem A (2)–(3)) are not formalized.
-/

open Complex NumberField

namespace WeilRH

/-! ### `ζ_ℚ = ζ` on `Re s > 1` -/

/-- Every natural number is the norm of exactly one ideal of `𝓞 ℚ` (`n = 0`: the zero ideal). -/
theorem card_ideal_rat_eq_one (n : ℕ) :
    Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} = 1 := by
  have hrank : Module.finrank ℤ (𝓞 ℚ) = 1 := by
    rw [RingOfIntegers.rank, Module.finrank_self]
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ)
      Rat.ringOfIntegersEquiv.symm.surjective
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨Ideal.span {(n : 𝓞 ℚ)}, by rw [Ideal.absNorm_span_natCast, hrank, pow_one]⟩, ?_⟩
  rintro ⟨I, hI⟩
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, (k : 𝓞 ℚ) = x :=
    ⟨Rat.ringOfIntegersEquiv x, by
      rw [← eq_intCast Rat.ringOfIntegersEquiv.symm, RingEquiv.symm_apply_apply]⟩
  have hk : Ideal.span {(k : 𝓞 ℚ)} = Ideal.span {((k.natAbs : ℕ) : 𝓞 ℚ)} := by
    rcases Int.natAbs_eq k with h | h
    · conv_lhs => rw [h]
      simp
    · conv_lhs => rw [h]
      simp [Ideal.span_singleton_neg]
  change Ideal.span {(k : 𝓞 ℚ)} = Ideal.span {(n : 𝓞 ℚ)}
  change Ideal.absNorm (Ideal.span {(k : 𝓞 ℚ)}) = n at hI
  rw [hk] at hI ⊢
  rw [Ideal.absNorm_span_natCast, hrank, pow_one] at hI
  rw [hI]

/-- Mathlib's Dedekind zeta L-series of `ℚ` is the Riemann zeta function on `Re s > 1`. -/
theorem dedekindZeta_rat {s : ℂ} (hs : 1 < s.re) : dedekindZeta ℚ s = riemannZeta s := by
  rw [dedekindZeta, ← LSeries_one_eq_riemannZeta hs]
  refine LSeries_congr (fun {n} _ => ?_) s
  simp [card_ideal_rat_eq_one n]

/-! ### Continuations of `Λ_K` -/

/-- The archimedean and conductor factor `|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}` of `Λ_K`
(report §2). -/
noncomputable def dedekindGammaFactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ InfinitePlace.nrRealPlaces K * Gammaℂ s ^ InfinitePlace.nrComplexPlaces K

/-- A **continuation of the completed Dedekind zeta function** `Λ_K` (Hecke's theorem, not in
Mathlib v4.34.1): a function holomorphic off `{0, 1}` that equals
`|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s)` for `Re s > 1` and satisfies `Λ(1 - s) = Λ(s)`. -/
structure DedekindContinuation (K : Type*) [Field K] [NumberField K] where
  /-- The completed zeta function `Λ_K` (junk values at the poles `0, 1`). -/
  Λ : ℂ → ℂ
  /-- `Λ_K` is holomorphic on `ℂ ∖ {0, 1}`. -/
  differentiableOn : DifferentiableOn ℂ Λ {0, 1}ᶜ
  /-- `Λ_K(s) = |d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s)` in the half-plane of convergence. -/
  eq_of_one_lt_re : ∀ s : ℂ, 1 < s.re → Λ s = dedekindGammaFactor K s * dedekindZeta K s
  /-- The functional equation `Λ_K(1 - s) = Λ_K(s)`. -/
  one_sub : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s

namespace DedekindContinuation

variable {K : Type*} [Field K] [NumberField K]

lemma isOpen_compl : IsOpen ({0, 1}ᶜ : Set ℂ) :=
  (Set.toFinite _).isClosed.isOpen_compl

lemma isPreconnected_compl : IsPreconnected ({0, 1}ᶜ : Set ℂ) :=
  ((Set.toFinite ({0, 1} : Set ℂ)).countable.isPathConnected_compl_of_one_lt_rank
    (by simp)).isConnected.isPreconnected

/-- **Uniqueness of the continuation.** Two continuations of `Λ_K` agree on `ℂ ∖ {0, 1}`
(identity theorem: both are holomorphic on the connected set `ℂ ∖ {0, 1}` and agree on
`Re s > 1`). -/
theorem eqOn (C C' : DedekindContinuation K) : Set.EqOn C.Λ C'.Λ {0, 1}ᶜ := by
  have h2 : (2 : ℂ) ∈ ({0, 1}ᶜ : Set ℂ) := by norm_num
  refine (C.differentiableOn.analyticOnNhd isOpen_compl).eqOn_of_preconnected_of_eventuallyEq
    (C'.differentiableOn.analyticOnNhd isOpen_compl) isPreconnected_compl h2 ?_
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hU.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
  rw [C.eq_of_one_lt_re s hs, C'.eq_of_one_lt_re s hs]

end DedekindContinuation

/-- The Dedekind datum of `K` (Q1 class `𝒞_Ded`, type `(1, 0)`, degree `j = 1`): `L = Λ_K`, critical
line `Re s = 1/2`, nontrivial zeros = zeros of `Λ_K` (away from its poles `0, 1`). -/
noncomputable def dedekindDatum (K : Type*) [Field K] [NumberField K]
    (C : DedekindContinuation K) : LFunctionDatum where
  L := C.Λ
  weight := 1
  IsNontrivialZero ρ := C.Λ ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1
  isZero_of_isNontrivialZero _ h := h.1

/-- The nontrivial-zero predicate does not depend on the continuation. -/
theorem dedekindDatum_isNontrivialZero_iff {K : Type*} [Field K] [NumberField K]
    (C C' : DedekindContinuation K) (ρ : ℂ) :
    (dedekindDatum K C).IsNontrivialZero ρ ↔ (dedekindDatum K C').IsNontrivialZero ρ := by
  have key : ∀ (C C' : DedekindContinuation K), (dedekindDatum K C).IsNontrivialZero ρ →
      (dedekindDatum K C').IsNontrivialZero ρ := by
    rintro C C' ⟨h, h0, h1⟩
    refine ⟨?_, h0, h1⟩
    rw [← C.eqOn C' (by simp [h0, h1])]
    exact h
  exact ⟨key C C', key C' C⟩

/-- GRH for `ζ_K` does not depend on the continuation. -/
theorem dedekindDatum_grh_iff {K : Type*} [Field K] [NumberField K]
    (C C' : DedekindContinuation K) : (dedekindDatum K C).GRH ↔ (dedekindDatum K C').GRH := by
  simp only [LFunctionDatum.GRH, dedekindDatum_isNontrivialZero_iff C C']
  rfl

/-- **Q1 Theorem A (1), objectwise.** Degree-`j` data of a polarized Deninger structure on `X̄_K`
satisfying AW2 (an `ArithmeticWeilCohomology`; notes `thm:rh`) imply GRH for `ζ_K`: every zero of
`Λ_K` lies on `Re s = 1/2`. -/
theorem grh_dedekind_of_awc_object {K : Type*} [Field K] [NumberField K]
    (C : DedekindContinuation K) (H : ArithmeticWeilCohomology (dedekindDatum K C)) :
    ∀ ρ, C.Λ ρ = 0 → ρ ≠ 0 → ρ ≠ 1 → ρ.re = 1 / 2 := fun ρ h h0 h1 =>
  H.grh ρ ⟨h, h0, h1⟩

/-- **Q1 Theorem A (1), class form.** If every number field `K` (with every continuation of
`Λ_K`) admits such Deninger data (an `ArithmeticWeilCohomology`), then GRH holds for every Dedekind
zeta function. -/
theorem grh_dedekind_of_awc
    (h : ∀ (K : Type) [Field K] [NumberField K] (C : DedekindContinuation K),
      Nonempty (ArithmeticWeilCohomology (dedekindDatum K C))) :
    ∀ (K : Type) [Field K] [NumberField K] (C : DedekindContinuation K),
      (dedekindDatum K C).GRH :=
  fun K _ _ C => (h K C).some.grh

/-! ### The case `K = ℚ` -/

lemma dedekindGammaFactor_rat (s : ℂ) : dedekindGammaFactor ℚ s = Gammaℝ s := by
  have hf : Module.finrank ℚ ℚ = 1 := Module.finrank_self ℚ
  simp [dedekindGammaFactor, InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hf,
    InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hf]

/-- Mathlib's `completedRiemannZeta` is a continuation of `Λ_ℚ`. -/
noncomputable def DedekindContinuation.rat : DedekindContinuation ℚ where
  Λ := completedRiemannZeta
  differentiableOn s hs := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
    exact (differentiableAt_completedZeta hs.1 hs.2).differentiableWithinAt
  eq_of_one_lt_re s hs := by
    have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
    rw [dedekindGammaFactor_rat, dedekindZeta_rat hs, riemannZeta_def_of_ne_zero hs0,
      mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos (by linarith))]
  one_sub s _ _ := completedRiemannZeta_one_sub s

/-- For `ρ ≠ 0, 1`, `Λ(ρ) = 0` iff `ρ` is a nontrivial zero of `ζ` (via `ξ`). -/
theorem completedRiemannZeta_eq_zero_iff {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    completedRiemannZeta ρ = 0 ↔ IsNontrivialZetaZero ρ := by
  rw [← completedXi_eq_zero_iff, completedXi_eq h0 h1]
  have : ρ * (ρ - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  constructor
  · intro h; rw [h]; simp
  · intro h
    have h' : ρ * (ρ - 1) * completedRiemannZeta ρ = 0 := by
      have := congrArg (· * 2) h; simpa using this
    exact (mul_eq_zero.1 h').resolve_left this

/-- For `K = ℚ` the nontrivial zeros of the Dedekind datum are exactly the nontrivial zeros of
`ζ` in the sense of Mathlib's `RiemannHypothesis`, for **any** continuation. -/
theorem dedekindDatum_rat_isNontrivialZero_iff (C : DedekindContinuation ℚ) (ρ : ℂ) :
    (dedekindDatum ℚ C).IsNontrivialZero ρ ↔ IsNontrivialZetaZero ρ := by
  rw [dedekindDatum_isNontrivialZero_iff C DedekindContinuation.rat]
  constructor
  · rintro ⟨h, h0, h1⟩
    exact (completedRiemannZeta_eq_zero_iff h0 h1).1 h
  · intro h
    have h0 : ρ ≠ 0 := by
      rintro rfl
      have := h.1
      rw [riemannZeta_zero] at this
      norm_num at this
    exact ⟨(completedRiemannZeta_eq_zero_iff h0 h.2.2).2 h, h0, h.2.2⟩

/-- GRH for the Dedekind datum of `ℚ` is exactly Mathlib's `RiemannHypothesis`. -/
theorem dedekindDatum_rat_grh_iff (C : DedekindContinuation ℚ) :
    (dedekindDatum ℚ C).GRH ↔ RiemannHypothesis := by
  rw [← LFunctionDatum.grh_riemannZeta_iff]
  simp only [LFunctionDatum.GRH, dedekindDatum_rat_isNontrivialZero_iff]
  rfl

/-- **Q1 Theorem A, `K = ℚ`.** Deninger data (an `ArithmeticWeilCohomology`) on `X̄_ℚ`, as a member
of the Dedekind class (any continuation), imply Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_of_awc_dedekind_rat (C : DedekindContinuation ℚ)
    (H : ArithmeticWeilCohomology (dedekindDatum ℚ C)) : RiemannHypothesis :=
  (dedekindDatum_rat_grh_iff C).1 H.grh

/-- **Q1 Theorem A ⇒ RH.** The class-level hypothesis of `grh_dedekind_of_awc` implies Mathlib's
`RiemannHypothesis` (specialize to `K = ℚ` with the continuation `completedRiemannZeta`). -/
theorem riemannHypothesis_of_grh_dedekind_class
    (h : ∀ (K : Type) [Field K] [NumberField K] (C : DedekindContinuation K),
      Nonempty (ArithmeticWeilCohomology (dedekindDatum K C))) : RiemannHypothesis :=
  (dedekindDatum_rat_grh_iff DedekindContinuation.rat).1
    (grh_dedekind_of_awc h ℚ DedekindContinuation.rat)

/-! ### Dirichlet L-functions -/

/-- The Dirichlet datum of `χ`: `L = L(χ, s)` (Mathlib's continued `DirichletCharacter.LFunction`),
critical line `Re s = 1/2`, nontrivial zeros = zeros in the open critical strip. -/
noncomputable def dirichletDatum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    LFunctionDatum where
  L := DirichletCharacter.LFunction χ
  weight := 1
  IsNontrivialZero ρ := DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
  isZero_of_isNontrivialZero _ h := h.1

/-- **Q1 Theorem A (2) shape for Dirichlet characters.** If every Dirichlet L-function admits
Deninger data (an `ArithmeticWeilCohomology`), every zero of every `L(χ, s)` in `0 < Re s < 1`
lies on `Re s = 1/2`.
(Q1 derives this from the Dedekind case via class field theory; that derivation is not
formalized — here the Dirichlet data are members of `𝒞` in their own right.) -/
theorem grh_dirichlet_of_awc
    (h : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Nonempty (ArithmeticWeilCohomology (dirichletDatum χ))) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ),
      DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2 :=
  fun N _ χ ρ h0 hl hr => (h N χ).some.grh ρ ⟨h0, hl, hr⟩

end WeilRH
