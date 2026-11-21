/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.DedekindLocal
import WeilRH.HeckeCorollaries

/-!
# `prop:xiK`: the strip clause and the order comparison (round 71)

`latex/notes.tex`, `prop:xiK`: every zero of `ξ_K` lies in `0 ≤ Re s ≤ 1`, and for
`0 ≤ Re s ≤ 1`, `s ∉ {0, 1}`, the order of `ξ_K` at `s` equals the order of `ζ_K` at `s`.

Mathlib's `dedekindZeta K` is the Dirichlet series, meaningful only on `Re s > 1`. The continuation
of `ζ_K` used here is `zetaCont C s := Λ_K(s) · (|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂})⁻¹`
(`def:zeta` read backwards). It agrees with `dedekindZeta K` on `Re s > 1` (`zetaCont_eq`) and is
holomorphic off `{0, 1}` (`differentiableOn_zetaCont`): the inverse Gamma factor is entire. By the
identity theorem it is therefore *the* continuation of `ζ_K` to `ℂ ∖ {0, 1}`.

## Main results
* `xi_ne_zero_of_one_lt_re`, `xi_ne_zero_of_re_neg`: `ξ_K ≠ 0` off the closed strip
  (Euler product of rounds 61–63 and the functional equation).
* `re_mem_Icc_of_xi_eq_zero`: **every zero of `ξ_K` lies in `0 ≤ Re s ≤ 1`**.
* `analyticOrderAt_zetaCont_eq`: for `0 ≤ Re s`, `s ∉ {0, 1}`, `ord_s ζ_K = ord_s ξ_K`.
* `Hecke.xiK_strip`, `Hecke.xiK_order`: the same for every number field, CONDITIONAL on B1.

Only the hypotheses `C : DedekindContinuation K` and `P : C.SimplePoles` are used; both are supplied
by B1 (`HeckePackage`) through `Hecke` below.
-/

open NumberField Complex Filter Topology

namespace WeilRH.XiKStrip

variable {K : Type*} [Field K] [NumberField K] {C : DedekindContinuation K} (P : C.SimplePoles)

/-- `ξ_K(s) ≠ 0` for `Re s > 1` (unconditional Euler product, `DedekindLocal`). -/
theorem xi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : P.ξ s ≠ 0 :=
  DedekindLocal.nonvanishingRight P s hs

/-- `ξ_K(s) ≠ 0` for `Re s < 0`, by the functional equation. -/
theorem xi_ne_zero_of_re_neg {s : ℂ} (hs : s.re < 0) : P.ξ s ≠ 0 := by
  have h := P.one_sub (1 - s)
  rw [sub_sub_cancel] at h
  rw [h]
  exact xi_ne_zero_of_one_lt_re P (by simp; linarith)

/-- **`prop:xiK`, strip clause:** every zero of `ξ_K` lies in `0 ≤ Re s ≤ 1`. -/
theorem re_mem_Icc_of_xi_eq_zero {ρ : ℂ} (hρ : P.ξ ρ = 0) : 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  by_contra h
  rcases not_and_or.1 h with h | h
  · exact xi_ne_zero_of_re_neg P (lt_of_not_ge h) hρ
  · exact xi_ne_zero_of_one_lt_re P (lt_of_not_ge h) hρ

variable (K) in
/-- The inverse of the archimedean and conductor factor `|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}`. -/
noncomputable def gammaFactorInv (s : ℂ) : ℂ := (dedekindGammaFactor K s)⁻¹

lemma discr_cast_ne_zero : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
  exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)

lemma gammaFactorInv_eq (s : ℂ) : gammaFactorInv K s =
    (((|discr K| : ℤ) : ℂ) ^ (s / 2))⁻¹ * (Gammaℝ s)⁻¹ ^ InfinitePlace.nrRealPlaces K *
      (Gammaℂ s)⁻¹ ^ InfinitePlace.nrComplexPlaces K := by
  simp only [gammaFactorInv, dedekindGammaFactor, mul_inv, inv_pow]

variable (K) in
/-- The inverse Gamma factor is entire. -/
theorem differentiable_gammaFactorInv : Differentiable ℂ (gammaFactorInv K) := by
  have hd := discr_cast_ne_zero (K := K)
  have h1 : Differentiable ℂ fun s : ℂ => (((|discr K| : ℤ) : ℂ) ^ (s / 2))⁻¹ := by
    intro s
    refine DifferentiableAt.inv ?_ ?_
    · exact (differentiableAt_id.div_const 2).const_cpow (Or.inl hd)
    · rw [Ne, cpow_eq_zero_iff]; exact fun h => hd h.1
  have h2 := differentiable_Gammaℝ_inv
  have h3 := differentiable_Gammaℂ_inv
  have : gammaFactorInv K = fun s => (((|discr K| : ℤ) : ℂ) ^ (s / 2))⁻¹ *
      (Gammaℝ s)⁻¹ ^ InfinitePlace.nrRealPlaces K *
        (Gammaℂ s)⁻¹ ^ InfinitePlace.nrComplexPlaces K := funext gammaFactorInv_eq
  rw [this]
  exact (h1.mul (h2.pow _)).mul (h3.pow _)

lemma Gamma_ne_zero_of_re_nonneg {s : ℂ} (hs : 0 ≤ s.re) (h0 : s ≠ 0) : Gamma s ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m hm => h0 ?_
  have hre : s.re = -(m : ℝ) := by rw [hm]; simp
  have hm0 : (m : ℝ) = 0 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [hm]; simp [show (m : ℂ) = 0 by exact_mod_cast (by exact_mod_cast hm0 : m = 0)]

lemma Gammaℝ_ne_zero_of_re_nonneg {s : ℂ} (hs : 0 ≤ s.re) (h0 : s ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Gammaℝ_def]
  refine mul_ne_zero ?_ (Gamma_ne_zero_of_re_nonneg (by simp; linarith) (div_ne_zero h0 two_ne_zero))
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => Real.pi_ne_zero (by exact_mod_cast h.1)

lemma Gammaℂ_ne_zero_of_re_nonneg {s : ℂ} (hs : 0 ≤ s.re) (h0 : s ≠ 0) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_nonneg hs h0)
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => h2pi h.1

/-- The inverse Gamma factor has no zero on `Re s ≥ 0`, `s ≠ 0`. -/
lemma gammaFactorInv_ne_zero {s : ℂ} (hs : 0 ≤ s.re) (h0 : s ≠ 0) : gammaFactorInv K s ≠ 0 := by
  rw [gammaFactorInv_eq]
  have hd := discr_cast_ne_zero (K := K)
  refine mul_ne_zero (mul_ne_zero (inv_ne_zero ?_)
    (pow_ne_zero _ (inv_ne_zero (Gammaℝ_ne_zero_of_re_nonneg hs h0))))
    (pow_ne_zero _ (inv_ne_zero (Gammaℂ_ne_zero_of_re_nonneg hs h0)))
  rw [Ne, cpow_eq_zero_iff]; exact fun h => hd h.1

/-- **The continuation of `ζ_K`:** `ζ_K(s) = Λ_K(s) / (|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂})`. -/
noncomputable def zetaCont (C : DedekindContinuation K) (s : ℂ) : ℂ := C.Λ s * gammaFactorInv K s

/-- `zetaCont C` is Mathlib's `dedekindZeta K` on `Re s > 1`. -/
theorem zetaCont_eq (C : DedekindContinuation K) {s : ℂ} (hs : 1 < s.re) :
    zetaCont C s = dedekindZeta K s := by
  rw [zetaCont, gammaFactorInv, C.eq_of_one_lt_re s hs, mul_comm (dedekindGammaFactor K s),
    mul_assoc, mul_inv_cancel₀ (DedekindZetaConv.dedekindGammaFactor_ne_zero (by linarith)),
    mul_one]

/-- `zetaCont C` is holomorphic on `ℂ ∖ {0, 1}`. -/
theorem differentiableOn_zetaCont (C : DedekindContinuation K) :
    DifferentiableOn ℂ (zetaCont C) {0, 1}ᶜ :=
  C.differentiableOn.mul (differentiable_gammaFactorInv K).differentiableOn

/-- **`prop:xiK`, order clause:** for `0 ≤ Re s` and `s ∉ {0, 1}`, the order of `ζ_K` at `s`
equals the order of `ξ_K` at `s`. -/
theorem analyticOrderAt_zetaCont_eq {s : ℂ} (hs : 0 ≤ s.re) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    analyticOrderAt (zetaCont C) s = analyticOrderAt P.ξ s := by
  let A : ℂ → ℂ := fun z => gammaFactorInv K z / (z * (z - 1))
  have hz : s * (s - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
  have hA : AnalyticAt ℂ A s := by
    have hG : AnalyticAt ℂ (gammaFactorInv K) s :=
      (differentiable_gammaFactorInv K).analyticAt s
    exact hG.div (by fun_prop) hz
  have hAne : A s ≠ 0 := div_ne_zero (gammaFactorInv_ne_zero hs h0) hz
  have hopen : IsOpen ({0, 1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
  have hmem : s ∈ ({0, 1}ᶜ : Set ℂ) := by simp [h0, h1]
  have hev : zetaCont C =ᶠ[𝓝 s] fun z => A z * P.ξ z := by
    filter_upwards [hopen.mem_nhds hmem] with z hz'
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz'
    have hzz : z * (z - 1) ≠ 0 := mul_ne_zero hz'.1 (sub_ne_zero.mpr hz'.2)
    rw [zetaCont, P.eq_xiK z hz'.1 hz'.2, xiK]
    simp only [A]
    rw [div_mul_eq_mul_div, mul_comm (gammaFactorInv K z), mul_assoc, mul_div_assoc,
      mul_div_cancel₀ _ hzz]
  rw [analyticOrderAt_congr hev,
    show (fun z => A z * P.ξ z) = A * P.ξ from rfl,
    analyticOrderAt_mul hA (P.differentiable.analyticAt s),
    hA.analyticOrderAt_eq_zero.2 hAne, zero_add]

/-- In particular every zero of `ζ_K` with `0 < Re s < 1` is a zero of `ξ_K` of the same order. -/
theorem xi_eq_zero_of_zetaCont_eq_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1)
    (hz : zetaCont C s = 0) : P.ξ s = 0 ∧
      analyticOrderAt (zetaCont C) s = analyticOrderAt P.ξ s := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have h1 : s ≠ 1 := by rintro rfl; simp at hs1
  refine ⟨?_, analyticOrderAt_zetaCont_eq P hs.le h0 h1⟩
  have hev := analyticOrderAt_zetaCont_eq P hs.le h0 h1
  have hopen : IsOpen ({0, 1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
  have hA : AnalyticAt ℂ (zetaCont C) s :=
    (differentiableOn_zetaCont C).analyticAt (hopen.mem_nhds (by simp [h0, h1]))
  have : analyticOrderAt (zetaCont C) s ≠ 0 := (hA.analyticOrderAt_ne_zero).2 hz
  rw [hev] at this
  exact ((P.differentiable.analyticAt s).analyticOrderAt_ne_zero).1 this

end WeilRH.XiKStrip

namespace WeilRH.Hecke

open XiKStrip

variable {K : Type} [Field K] [NumberField K] (hB : HeckePackage K)

/-- **`prop:xiK`, strip clause**, for every number field, CONDITIONAL on B1. -/
theorem xiK_strip {ρ : ℂ} (hρ : xi hB ρ = 0) : 0 ≤ ρ.re ∧ ρ.re ≤ 1 :=
  re_mem_Icc_of_xi_eq_zero hB.simplePoles hρ

/-- **`prop:xiK`, order clause**, for every number field, CONDITIONAL on B1: on `0 ≤ Re s ≤ 1`,
`s ∉ {0, 1}`, `ord_s ζ_K = ord_s ξ_K`, where `ζ_K` is continued by `zetaCont`. -/
theorem xiK_order {s : ℂ} (hs : 0 ≤ s.re) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    analyticOrderAt (zetaCont hB.continuation) s = analyticOrderAt (xi hB) s :=
  analyticOrderAt_zetaCont_eq hB.simplePoles hs h0 h1

end WeilRH.Hecke
