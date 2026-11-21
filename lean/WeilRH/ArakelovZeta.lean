import WeilRH.XiK

/-!
# Flach–Morin's zeta function of `X̄_K` (roadmap D4)

Round 50 of `lean/ROADMAP-arakelov.md`. Source: Flach–Morin, *Deninger's conjectures and
Weil–Arakelov cohomology*, Münster J. Math. 13 (2020), p. 520–521, checked in the local PDF
`refs/citation-tree/weil-etaile/flach-morin-2020-deninger-conjectures-weil-arakelov.pdf`:
`ζ(X̄, s) = ζ(X, s) · ζ(X_∞, s)`, `ζ(X_∞, s) = ∏_i L_∞(h^i(X_ℚ), s)^{(-1)^i}`, and formula (1)

`L_∞(h^i, s) = ∏_{p<q, p+q=i} Γ_ℂ(s-p)^{h^{p,q}} · ∏_{p=i/2} Γ_ℝ(s-p)^{h^{p,+}} Γ_ℝ(s-p+1)^{h^{p,-}}`

with **FM's normalization** `Γ_ℝ(s) = 2^{-1/2} π^{-s/2} Γ(s/2)`, `Γ_ℂ(s) = (2π)^{-s} Γ(s)`, and
`h^{p,±} = dim (H^{p,p})^{F_∞ = ±(-1)^p}`.

For `X̄_K` (`X = Spec 𝓞_K`, `d = 1`) only `i = 0` occurs: `H^0(X(ℂ), ℂ) = ℂ^{X_∞}` with
`X_∞ = Hom(K, ℂ)` and `F_∞` = complex conjugation of embeddings (`CompactifiedScheme.lean`, D1).
Its `F_∞`-invariants have dimension `#(F_∞-orbits) = r₁ + r₂` and its anti-invariants dimension
`r₂` (one per complex pair), so `ζ(X_∞, s) = Γ_ℝ(s)^{r₁+r₂} Γ_ℝ(s+1)^{r₂}`.

## Main results

* `GammaRFM`, `GammaCFM`: FM's gamma factors; `GammaRFM_eq`, `GammaCFM_eq` compare them with
  Mathlib's `Gammaℝ = π^{-s/2} Γ(s/2)` and `Gammaℂ = 2 (2π)^{-s} Γ(s)` (the notes' `Γ_ℝ, Γ_ℂ`).
* `GammaRFM_mul_add_one`: `Γ_ℝ(s) Γ_ℝ(s+1) = Γ_ℂ(s)` in FM's normalization (Legendre).
* `zetaInftyFM_eq`: `ζ(X_∞, s) = Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}` (FM normalization).
* `zetaFM_eq`: for `Re s > 1`, **`ζ(X̄_K, s) = e^{a + b s} Λ_K(s)`** with the explicit constants
  `a = -(r₁/2 + r₂) log 2` and `b = -(log |d_K|)/2` (`fmA`, `fmB`). This is the notes'
  "`ζ(X̄_K, s) = e^{a+bs} Λ_K`"; for `K = ℚ` it is `e^a = 2^{-1/2}`, `b = 0` (ruling R-1).
* `analyticOrderAt_xiFM`: the entire functions `e^{a+bs} ξ_K(s)` and `ξ_K(s)` have the **same
  order at every point**, so FM's zeta and the notes' `Λ_K` have the same divisor (also off the
  poles: `zetaFMCont_eq_zero_iff`).

## Not formalized

* `ζ(Spec 𝓞_K, s) = ∏_𝔭 (1 - N𝔭^{-s})^{-1}` is identified with Mathlib's `dedekindZeta` (the
  ideal-counting L-series); the Euler product is not in Mathlib v4.34.1, so FM's `ζ(X, s)` is
  *defined* here as `dedekindZeta K s`.
* The Hodge numbers `h^{0,±} = r₁ + r₂, r₂` are used as exponents here; that they are the
  dimensions of the `F_∞`-(anti-)invariants of `ℂ^{X_∞}` is proved in `HodgeInfty.lean`
  (`Xbar.finrank_invariants`, `Xbar.finrank_antiinvariants`, `Xbar.zetaInfty_hodge`, round 52).
-/

open NumberField NumberField.InfinitePlace Complex Topology
open scoped Real

noncomputable section

namespace WeilRH.Arakelov

variable (K : Type*) [Field K] [NumberField K]

/-- FM's `Γ_ℝ(s) = 2^{-1/2} π^{-s/2} Γ(s/2)` (FM p. 521, formula (1)). -/
def GammaRFM (s : ℂ) : ℂ := (2 : ℂ) ^ (-(1 : ℂ) / 2) * (π : ℂ) ^ (-s / 2) * Gamma (s / 2)

/-- FM's `Γ_ℂ(s) = (2π)^{-s} Γ(s)` (FM p. 521, formula (1)). -/
def GammaCFM (s : ℂ) : ℂ := (2 * π : ℂ) ^ (-s) * Gamma s

lemma GammaRFM_eq (s : ℂ) : GammaRFM s = (2 : ℂ) ^ (-(1 : ℂ) / 2) * Gammaℝ s := by
  rw [GammaRFM, Gammaℝ_def, mul_assoc]

lemma GammaCFM_eq (s : ℂ) : GammaCFM s = Gammaℂ s / 2 := by
  rw [GammaCFM, Gammaℂ_def]; ring

lemma two_cpow_neg_half_sq : (2 : ℂ) ^ (-(1 : ℂ) / 2) * (2 : ℂ) ^ (-(1 : ℂ) / 2) = 1 / 2 := by
  rw [← cpow_add _ _ two_ne_zero]
  norm_num [cpow_neg_one]

/-- Legendre duplication in FM's normalization: `Γ_ℝ(s) Γ_ℝ(s+1) = Γ_ℂ(s)`. -/
lemma GammaRFM_mul_add_one (s : ℂ) : GammaRFM s * GammaRFM (s + 1) = GammaCFM s := by
  rw [GammaRFM_eq, GammaRFM_eq, GammaCFM_eq, ← Gammaℝ_mul_Gammaℝ_add_one]
  linear_combination (Gammaℝ s * Gammaℝ (s + 1)) * two_cpow_neg_half_sq

/-- FM's archimedean factor of `X̄_K`: `ζ(X_∞, s) = L_∞(h^0, s) = Γ_ℝ(s)^{h^{0,+}} Γ_ℝ(s+1)^{h^{0,-}}`
with `h^{0,+} = r₁ + r₂` and `h^{0,-} = r₂` (FM (1), `i = p = 0`). -/
def zetaInftyFM (s : ℂ) : ℂ :=
  GammaRFM s ^ (nrRealPlaces K + nrComplexPlaces K) * GammaRFM (s + 1) ^ nrComplexPlaces K

/-- `ζ(X_∞, s) = Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}` (FM normalization). -/
lemma zetaInftyFM_eq (s : ℂ) :
    zetaInftyFM K s = GammaRFM s ^ nrRealPlaces K * GammaCFM s ^ nrComplexPlaces K := by
  rw [zetaInftyFM, pow_add, ← GammaRFM_mul_add_one, mul_pow]; ring

/-- Flach–Morin's `ζ(X̄_K, s) = ζ(Spec 𝓞_K, s) · ζ(X_∞, s)` (FM p. 520), with `ζ(Spec 𝓞_K, s)`
taken to be Mathlib's `dedekindZeta` (see the module docstring); meaningful for `Re s > 1`. -/
def zetaFM (s : ℂ) : ℂ := dedekindZeta K s * zetaInftyFM K s

/-- The constant `a = -(r₁/2 + r₂) log 2`. -/
def fmA : ℂ := -((nrRealPlaces K : ℂ) / 2 + nrComplexPlaces K) * Complex.log 2

/-- The constant `b = -(log |d_K|)/2`. -/
def fmB : ℂ := -Complex.log ((|discr K| : ℤ) : ℂ) / 2

lemma discr_cast_ne_zero : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
  exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)

/-- `e^{a + b s} = (2^{-1/2})^{r₁} (2⁻¹)^{r₂} |d_K|^{-s/2}`. -/
lemma exp_fmA_add (s : ℂ) :
    exp (fmA K + fmB K * s) = ((2 : ℂ) ^ (-(1 : ℂ) / 2)) ^ nrRealPlaces K *
      (2 : ℂ)⁻¹ ^ nrComplexPlaces K * ((|discr K| : ℤ) : ℂ) ^ (-s / 2) := by
  have h2 : (2 : ℂ) ^ (-(1 : ℂ) / 2) = exp (Complex.log 2 * (-(1 : ℂ) / 2)) :=
    cpow_def_of_ne_zero two_ne_zero _
  have hh : (2 : ℂ)⁻¹ = exp (-Complex.log 2) := by
    rw [exp_neg, exp_log two_ne_zero]
  have hd : ((|discr K| : ℤ) : ℂ) ^ (-s / 2) =
      exp (Complex.log ((|discr K| : ℤ) : ℂ) * (-s / 2)) :=
    cpow_def_of_ne_zero (discr_cast_ne_zero K) _
  rw [h2, hh, hd, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add, fmA, fmB]
  congr 1
  ring

/-- **FM's zeta of `X̄_K` versus the notes' `Λ_K`**: for `Re s > 1`,
`ζ(X̄_K, s) = e^{a + b s} Λ_K(s)` with `a = -(r₁/2 + r₂) log 2`, `b = -(log |d_K|)/2`. -/
theorem zetaFM_eq (C : DedekindContinuation K) {s : ℂ} (hs : 1 < s.re) :
    zetaFM K s = exp (fmA K + fmB K * s) * C.Λ s := by
  rw [C.eq_of_one_lt_re s hs, exp_fmA_add, zetaFM, zetaInftyFM_eq, GammaRFM_eq, GammaCFM_eq,
    dedekindGammaFactor]
  have hd := discr_cast_ne_zero K
  have hcancel : ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * ((|discr K| : ℤ) : ℂ) ^ (s / 2) = 1 := by
    rw [← cpow_add _ _ hd, show -s / 2 + s / 2 = (0 : ℂ) by ring, cpow_zero]
  set D := ((|discr K| : ℤ) : ℂ)
  set r := nrRealPlaces K
  set c := nrComplexPlaces K
  have key : (2 ^ (-(1 : ℂ) / 2)) ^ r * (2 : ℂ)⁻¹ ^ c * D ^ (-s / 2) *
      (D ^ (s / 2) * Gammaℝ s ^ r * Gammaℂ s ^ c * dedekindZeta K s) =
      (2 ^ (-(1 : ℂ) / 2)) ^ r * (2 : ℂ)⁻¹ ^ c * (D ^ (-s / 2) * D ^ (s / 2)) *
      (Gammaℝ s ^ r * Gammaℂ s ^ c * dedekindZeta K s) := by ring
  rw [key, hcancel, mul_pow, div_eq_mul_inv (Gammaℂ s), mul_pow]
  ring

/-- For `K = ℚ`: `e^{a + b s} = 2^{-1/2}` (ruling R-1: FM's completion is `2^{-1/2} Λ`). -/
lemma exp_fmA_add_rat (s : ℂ) : exp (fmA ℚ + fmB ℚ * s) = (2 : ℂ) ^ (-(1 : ℂ) / 2) := by
  rw [exp_fmA_add]
  have hr : nrRealPlaces ℚ = 1 := by
    have := card_add_two_mul_card_eq_rank ℚ
    simp only [Module.finrank_self] at this
    omega
  have hc : nrComplexPlaces ℚ = 0 := by
    have := card_add_two_mul_card_eq_rank ℚ
    simp only [Module.finrank_self] at this
    omega
  simp [hr, hc, Rat.numberField_discr]

/-- FM's zeta of `X̄_K`, continued off `{0, 1}` through a continuation of `Λ_K`. -/
def zetaFMCont (C : DedekindContinuation K) (s : ℂ) : ℂ := exp (fmA K + fmB K * s) * C.Λ s

/-- FM's zeta and `Λ_K` have the same zeros. -/
theorem zetaFMCont_eq_zero_iff (C : DedekindContinuation K) (s : ℂ) :
    zetaFMCont K C s = 0 ↔ C.Λ s = 0 := by
  simp [zetaFMCont, exp_ne_zero]

/-- FM's completed `ξ`: the entire function `e^{a + b s} ξ_K(s)`. -/
def xiFM {C : DedekindContinuation K} (P : C.SimplePoles) (s : ℂ) : ℂ :=
  exp (fmA K + fmB K * s) * P.ξ s

/-- **Same divisor**: `e^{a+bs} ξ_K` and `ξ_K` have the same order at every point. -/
theorem analyticOrderAt_xiFM {C : DedekindContinuation K} (P : C.SimplePoles) (z : ℂ) :
    analyticOrderAt (xiFM K P) z = analyticOrderAt P.ξ z := by
  have he : AnalyticAt ℂ (fun s => exp (fmA K + fmB K * s)) z := by
    have : Differentiable ℂ (fun s => exp (fmA K + fmB K * s)) := by fun_prop
    exact this.analyticAt z
  have hξ : AnalyticAt ℂ P.ξ z := P.differentiable.analyticAt z
  have h0 : analyticOrderAt (fun s => exp (fmA K + fmB K * s)) z = 0 :=
    he.analyticOrderAt_eq_zero.2 (exp_ne_zero _)
  have : xiFM K P = (fun s => exp (fmA K + fmB K * s)) * P.ξ := rfl
  rw [this, analyticOrderAt_mul he hξ, h0, zero_add]

end WeilRH.Arakelov

end
