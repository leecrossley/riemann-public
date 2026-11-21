/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.Negative

/-!
# Positive kernels with zeros off the line (`def:R12-kernels`, `prop:R12`)

`latex/notes.tex`, `def:R12-kernels`: for `a > 0`,
`μ_a = cosh(a) δ₀ + ½(δ₁ + δ₋₁)`, `g_σ(t) = (4πσ)^{-1/2} e^{-t²/(4σ)}` and
`k_{a,σ}(t) = cosh(a) g_σ(t) + ½(g_σ(t - 1) + g_σ(t + 1))`, with the Fourier transform
`ν̂(z) = ∫ e^{izt} dν(t)`. The measure `μ_a`, the zeros `π ± ia` and `μ̂_a(z) = cos z + cosh a` were
formalized in round 1 (`Negative.lean`, namespace `WeilRH.R12`, old claim ID R12); this module
reuses them and completes the proposition.

`prop:R12`:
* (i) `μ̂_a(z) = cos z + cosh a` for all `z ∈ ℂ` (`muHat_eq`); its zeros are the points
  `(2m + 1)π ± ia` (`muHat_eq_zero_iff`), all simple (`hasDerivAt_muHat`, `deriv_ne_zero`) and
  none real (`im_ne_zero`).
* (ii) for `σ > 0`, `k_{a,σ}` is smooth, integrable and everywhere positive
  (`contDiff_k`, `integrable_k`, `k_pos`), and `∫ e^{izt} k_{a,σ}(t) dt = e^{-σz²}(cos z + cosh a)`
  for all `z ∈ ℂ` (`fourier_k`); so it has the same zeros as `μ̂_a` (`fourier_k_eq_zero_iff`).
-/

namespace WeilRH

namespace R12Kernels

open Complex MeasureTheory Real

noncomputable section

/-- The Fourier transform `μ̂_a(z) = ∫ e^{izt} dμ_a(t)` of the measure
`μ_a = cosh(a) δ₀ + ½(δ₁ + δ₋₁)` (`WeilRH.R12.μ`, round 1). -/
def muHat (a : ℝ) (z : ℂ) : ℂ := ∫ t, cexp (I * z * t) ∂(R12.μ a)

/-- **`prop:R12` (i), first clause.** `μ̂_a(z) = cos z + cosh a` (from `R12.fourier_eq`). -/
theorem muHat_eq (a : ℝ) (z : ℂ) : muHat a z = Complex.cos z + Real.cosh a := by
  rw [muHat, Complex.ofReal_cosh, ← R12.fourier_eq a z]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  ring_nf

lemma cos_pi_add_mul_I (a : ℝ) : Complex.cos (π + a * I) = -(Real.cosh a : ℂ) := by
  rw [add_comm, Complex.cos_add_pi, Complex.cos_mul_I, Complex.ofReal_cosh]

/-- **`prop:R12` (i), zeros.** `μ̂_a(z) = 0` iff `z = (2m + 1)π ± ia` for some `m ∈ ℤ`. -/
theorem muHat_eq_zero_iff (a : ℝ) (z : ℂ) :
    muHat a z = 0 ↔ ∃ m : ℤ, z = (2 * m + 1) * π + a * I ∨ z = (2 * m + 1) * π - a * I := by
  rw [muHat_eq, add_eq_zero_iff_eq_neg, ← cos_pi_add_mul_I, Complex.cos_eq_cos_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact ⟨-k, Or.inl (by push_cast; linear_combination -hk)⟩
    · exact ⟨k - 1, Or.inr (by push_cast; linear_combination hk)⟩
  · rintro ⟨m, hm | hm⟩
    · exact ⟨-m, Or.inl (by push_cast; linear_combination -hm)⟩
    · exact ⟨m + 1, Or.inr (by push_cast; linear_combination hm)⟩

/-- `μ̂_a` has derivative `-sin z` everywhere. -/
theorem hasDerivAt_muHat (a : ℝ) (z : ℂ) : HasDerivAt (muHat a) (-Complex.sin z) z := by
  have : muHat a = fun w => Complex.cos w + Real.cosh a := funext (muHat_eq a)
  rw [this]
  simpa using (Complex.hasDerivAt_cos z).add_const (Real.cosh a : ℂ)

/-- **`prop:R12` (i), simplicity.** For `a > 0` every zero of `μ̂_a` is simple: the derivative
`-sin z` does not vanish there (`sin² z = 1 - cosh² a = -sinh² a ≠ 0`). -/
theorem deriv_ne_zero {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : muHat a z = 0) :
    deriv (muHat a) z ≠ 0 := by
  rw [(hasDerivAt_muHat a z).deriv, neg_ne_zero]
  intro hs
  rw [muHat_eq, add_eq_zero_iff_eq_neg] at hz
  have h1 := Complex.sin_sq_add_cos_sq z
  rw [hs, hz] at h1
  have h2 : ((Real.cosh a : ℂ)) ^ 2 = 1 + (Real.sinh a : ℂ) ^ 2 := by
    have := Real.cosh_sq a
    exact_mod_cast this.trans (by ring)
  have h3 : (Real.sinh a : ℂ) ^ 2 = 0 := by linear_combination h1 - h2
  have : Real.sinh a = 0 := by exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
  exact (Real.sinh_pos_iff.2 ha).ne' this

/-- **`prop:R12` (i), no real zeros.** For `a > 0` every zero of `μ̂_a` has `Im z = ±a ≠ 0`. -/
theorem im_ne_zero {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : muHat a z = 0) : z.im ≠ 0 := by
  obtain ⟨m, hm | hm⟩ := (muHat_eq_zero_iff a z).1 hz <;> subst hm <;> simp <;> exact ha.ne'

/-- `g_σ(t) = (4πσ)^{-1/2} e^{-t²/(4σ)}`. -/
def g (σ t : ℝ) : ℝ := (Real.sqrt (4 * π * σ))⁻¹ * Real.exp (-t ^ 2 / (4 * σ))

/-- `k_{a,σ}(t) = cosh(a) g_σ(t) + ½(g_σ(t - 1) + g_σ(t + 1))`. -/
def k (a σ t : ℝ) : ℝ := Real.cosh a * g σ t + 1 / 2 * (g σ (t - 1) + g σ (t + 1))

lemma g_pos {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : 0 < g σ t :=
  mul_pos (inv_pos.2 (Real.sqrt_pos.2 (by positivity))) (Real.exp_pos _)

/-- **`prop:R12` (ii): positivity.** -/
theorem k_pos (a : ℝ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : 0 < k a σ t := by
  unfold k
  have := g_pos hσ t; have := g_pos hσ (t - 1); have := g_pos hσ (t + 1)
  have := Real.cosh_pos a
  positivity

/-- **`prop:R12` (ii): smoothness.** -/
theorem contDiff_k (a σ : ℝ) : ContDiff ℝ ⊤ (k a σ) := by
  unfold k g; fun_prop

lemma integrable_g {σ : ℝ} (hσ : 0 < σ) (c : ℝ) : Integrable (fun t => g σ (t - c)) := by
  have h : Integrable (fun t : ℝ => Real.exp (-(1 / (4 * σ)) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have h' := (h.comp_sub_right c).const_mul (Real.sqrt (4 * π * σ))⁻¹
  refine h'.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [g]; congr 2; ring

/-- **`prop:R12` (ii): integrability.** -/
theorem integrable_k (a : ℝ) {σ : ℝ} (hσ : 0 < σ) : Integrable (k a σ) := by
  have h0 := (integrable_g hσ 0).const_mul (Real.cosh a)
  have h1 := ((integrable_g hσ 1).add (integrable_g hσ (-1))).const_mul (1 / 2)
  refine (h0.add h1).congr (Filter.Eventually.of_forall fun t => ?_)
  simp [k, sub_neg_eq_add]

/-- The transform of a translate: `∫ e^{izt} g_σ(t - c) dt = e^{izc} e^{-σz²}` for all `z ∈ ℂ`. -/
theorem fourier_g {σ : ℝ} (hσ : 0 < σ) (c : ℝ) (z : ℂ) :
    ∫ t : ℝ, cexp (I * z * t) * (g σ (t - c) : ℂ) = cexp (I * z * c) * cexp (-σ * z ^ 2) := by
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hS : 0 < 4 * π * σ := by positivity
  set b : ℂ := -1 / (4 * σ) with hb
  have hbre : b.re < 0 := by
    rw [hb, show (-1 / (4 * (σ : ℂ))) = ((-1 / (4 * σ) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hint : ∀ t : ℝ, cexp (I * z * t) * (g σ (t - c) : ℂ) =
      ((Real.sqrt (4 * π * σ))⁻¹ : ℝ) * cexp (b * t ^ 2 + (c / (2 * σ) + I * z) * t +
        (-(c : ℂ) ^ 2 / (4 * σ))) := by
    intro t
    rw [g, Complex.ofReal_mul, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    rw [hb]; push_cast; field_simp; ring
  simp_rw [hint]
  rw [integral_const_mul, integral_cexp_quadratic hbre]
  have hpi : (↑π / -b : ℂ) = ((4 * π * σ : ℝ) : ℂ) := by
    rw [hb]; push_cast; field_simp
  have hsq : (((4 * π * σ : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (4 * π * σ) : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hS.le,
      ← Real.sqrt_eq_rpow]
  rw [hpi, hsq, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀
      (Real.sqrt_pos.2 hS).ne', Complex.ofReal_one, one_mul, ← Complex.exp_add]
  congr 1
  rw [hb]; field_simp; linear_combination (16 * (σ : ℂ) ^ 2 * z ^ 2) * Complex.I_sq

/-- **`prop:R12` (ii): the transform.** `∫ e^{izt} k_{a,σ}(t) dt = e^{-σz²}(cos z + cosh a)` for
all `z ∈ ℂ`. -/
theorem fourier_k (a : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : ℂ) :
    ∫ t : ℝ, cexp (I * z * t) * (k a σ t : ℂ) = cexp (-σ * z ^ 2) * (muHat a z) := by
  have hi : ∀ c : ℝ, Integrable (fun t : ℝ => cexp (I * z * t) * (g σ (t - c) : ℂ)) := by
    intro c
    have hexp : ∀ t : ℝ, ‖cexp (I * z * t)‖ ≤ Real.exp (|z.im| * |t|) := by
      intro t
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.2
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero, zero_sub, Complex.mul_im]
      calc -z.im * t ≤ |(-z.im) * t| := le_abs_self _
        _ = |z.im| * |t| := by rw [abs_mul, abs_neg]
    -- dominate by a Gaussian-times-exponential via the quadratic integrability lemma
    have hq : Integrable (fun t : ℝ => cexp ((-1 / (4 * σ) : ℂ) * t ^ 2 +
        (c / (2 * σ) + I * z) * t + (-(c : ℂ) ^ 2 / (4 * σ)))) := by
      refine integrable_cexp_quadratic' ?_ _ _
      rw [show (-1 / (4 * (σ : ℂ))) = ((-1 / (4 * σ) : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
      exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
    refine (hq.const_mul (((Real.sqrt (4 * π * σ))⁻¹ : ℝ) : ℂ)).congr
      (Filter.Eventually.of_forall fun t => ?_)
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    simp only
    rw [g, Complex.ofReal_mul, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; field_simp; ring
  have hk : ∀ t : ℝ, cexp (I * z * t) * (k a σ t : ℂ) =
      (Real.cosh a : ℂ) * (cexp (I * z * t) * (g σ (t - 0) : ℂ)) + (1 / 2 : ℂ) *
        (cexp (I * z * t) * (g σ (t - 1) : ℂ) + cexp (I * z * t) * (g σ (t - (-1)) : ℂ)) := by
    intro t; simp only [k, sub_zero, sub_neg_eq_add]; push_cast; ring
  simp_rw [hk]
  have hA : Integrable (fun t : ℝ => (Real.cosh a : ℂ) * (cexp (I * z * t) * (g σ (t - 0) : ℂ))) :=
    (hi 0).const_mul _
  have hB : Integrable (fun t : ℝ => (1 / 2 : ℂ) *
      (cexp (I * z * t) * (g σ (t - 1) : ℂ) + cexp (I * z * t) * (g σ (t - (-1)) : ℂ))) :=
    ((hi 1).add (hi (-1))).const_mul _
  rw [integral_add hA hB, integral_const_mul, integral_const_mul, integral_add (hi 1) (hi (-1)),
    fourier_g hσ, fourier_g hσ, fourier_g hσ, muHat_eq, Complex.cos]
  push_cast
  simp only [mul_zero, Complex.exp_zero, mul_one]
  ring_nf

/-- **`prop:R12` (ii), zeros.** The transform of `k_{a,σ}` has the same zeros as `μ̂_a`. -/
theorem fourier_k_eq_zero_iff (a : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : ℂ) :
    ∫ t : ℝ, cexp (I * z * t) * (k a σ t : ℂ) = 0 ↔ muHat a z = 0 := by
  rw [fourier_k a hσ, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]

end

end R12Kernels

end WeilRH
