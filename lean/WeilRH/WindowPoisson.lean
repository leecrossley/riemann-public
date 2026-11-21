/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# `thm:window` (i): Poisson summation over the half-shifted coset

`latex/notes.tex`, `def:window-objects` (a)–(b) and `thm:window` (i). For `φ ∈ C_c^∞(ℝ)` with
transform `Φ(s) = ∫ φ(t) e^{st} dt` and `L > 0`, the half-shifted coset is
`C_L = {1/2 + 2πi(n + 1/2)/L : n ∈ ℤ}`, and

`∑_{ρ ∈ C_L} Φ(ρ) = L ∑_{k ∈ ℤ} (-1)^k e^{kL/2} φ(kL)`.

The coset is parametrized bijectively by `n ∈ ℤ` (`cosetPt`), so the sum over `C_L` is the sum over
`n`. The proof is the manuscript's: apply Poisson summation (`SchwartzMap.tsum_eq_tsum_fourier`) to
`u ↦ ψ(Lu)` with `ψ(t) = φ(t) e^{t/2} e^{iπt/L}`. Mathlib's Fourier convention is
`𝓕 f(ξ) = ∫ e^{-2πi x ξ} f(x) dx`.
-/

open Complex MeasureTheory Filter
open scoped SchwartzMap FourierTransform ContDiff

namespace WeilRH
namespace WindowPoisson

/-- `def:window-objects` (a): the transform `Φ(s) = ∫ φ(t) e^{st} dt`. -/
noncomputable def transform (φ : ℝ → ℂ) (s : ℂ) : ℂ := ∫ t : ℝ, φ t * Complex.exp (s * t)

/-- `def:window-objects` (b): the point `1/2 + 2πi(n + 1/2)/L` of the half-shifted coset `C_L`. -/
noncomputable def cosetPt (L : ℝ) (n : ℤ) : ℂ :=
  1 / 2 + 2 * Real.pi * I * ((n : ℂ) + 1 / 2) / L

/-- `n ↦ cosetPt L n` is injective for `L ≠ 0`, so it parametrizes `C_L` bijectively. -/
theorem cosetPt_injective {L : ℝ} (hL : L ≠ 0) : Function.Injective (cosetPt L) := by
  intro m n h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  unfold cosetPt at h
  have h3 : (m : ℂ) = n := by
    have := congrArg (fun z : ℂ => (z - 1 / 2) * (L : ℂ)) h
    simp only [add_sub_cancel_left] at this
    field_simp at this
    linear_combination this / 2
  exact_mod_cast h3

/-- The rescaled auxiliary function `h(u) = φ(Lu) e^{(1/2 + iπ/L) L u}`. -/
noncomputable def aux (φ : ℝ → ℂ) (L : ℝ) (u : ℝ) : ℂ :=
  φ (L * u) * Complex.exp ((1 / 2 + Real.pi * I / L) * ((L * u : ℝ) : ℂ))

theorem contDiff_aux {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (L : ℝ) : ContDiff ℝ ∞ (aux φ L) := by
  unfold aux
  apply ContDiff.mul
  · exact hφ.comp (contDiff_const.mul contDiff_id)
  · apply ContDiff.cexp
    apply contDiff_const.mul
    exact ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)

theorem hasCompactSupport_aux {φ : ℝ → ℂ} (hc : HasCompactSupport φ) {L : ℝ} (hL : L ≠ 0) :
    HasCompactSupport (aux φ L) := by
  have h1 : HasCompactSupport (fun u : ℝ => φ (L * u)) :=
    hc.comp_homeomorph (Homeomorph.mulLeft₀ L hL)
  exact h1.mul_right

/-- The Fourier transform of `aux φ L` at `n` is `L⁻¹ Φ(cosetPt L (-n))`. -/
theorem fourier_aux (φ : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (n : ℤ) :
    𝓕 (aux φ L) n = (L : ℂ)⁻¹ * transform φ (cosetPt L (-n)) := by
  have hL0 : L ≠ 0 := hL.ne'
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL0
  rw [Real.fourier_real_eq_integral_exp_smul]
  set s : ℂ := cosetPt L (-n)
  have key : ∀ u : ℝ, Complex.exp (↑(-2 * Real.pi * u * n) * I) • aux φ L u =
      (fun t : ℝ => φ t * Complex.exp (s * t)) (L * u) := by
    intro u
    simp only [aux, smul_eq_mul]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    simp only [s, cosetPt]
    push_cast
    field_simp
    ring
  simp_rw [key]
  rw [Measure.integral_comp_mul_left (fun t : ℝ => φ t * Complex.exp (s * t)) L]
  rw [abs_of_pos (inv_pos.mpr hL), Complex.real_smul]
  simp [transform, s]

/-- The value `h(k) = (-1)^k e^{kL/2} φ(kL)`. -/
theorem aux_int (φ : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (k : ℤ) :
    aux φ L k = (-1 : ℂ) ^ k * (Real.exp (k * L / 2) : ℂ) * φ (k * L) := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [aux]
  have he : (1 / 2 + Real.pi * I / L) * ((L * k : ℝ) : ℂ) =
      ((k * L / 2 : ℝ) : ℂ) + (k : ℂ) * (Real.pi * I) := by
    push_cast; field_simp
  rw [he, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I, ← Complex.ofReal_exp,
    mul_comm L]
  ring

/-- **`thm:window` (i).** For `φ ∈ C_c^∞(ℝ)` and `L > 0`, the sum of `Φ` over the half-shifted
coset `C_L` converges and `∑_{ρ ∈ C_L} Φ(ρ) = L ∑_k (-1)^k e^{kL/2} φ(kL)`. -/
theorem window_poisson {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {L : ℝ}
    (hL : 0 < L) :
    Summable (fun n : ℤ => transform φ (cosetPt L n)) ∧
      ∑' n : ℤ, transform φ (cosetPt L n) =
        L * ∑' k : ℤ, (-1 : ℂ) ^ k * (Real.exp (k * L / 2) : ℂ) * φ (k * L) := by
  have hL0 : L ≠ 0 := hL.ne'
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL0
  set f : 𝓢(ℝ, ℂ) := (hasCompactSupport_aux hc hL0).toSchwartzMap (contDiff_aux hφ L)
  have hf : (f : ℝ → ℂ) = aux φ L := rfl
  -- transform at the coset, via the Fourier transform at `-n`
  have hT : ∀ n : ℤ, transform φ (cosetPt L n) = L * 𝓕 (aux φ L) (-n : ℤ) := by
    intro n
    rw [fourier_aux φ hL (-n), neg_neg, ← mul_assoc, mul_inv_cancel₀ hL', one_mul]
  have hsum : Summable (fun n : ℤ => 𝓕 (aux φ L) (n : ℝ)) := by
    have hO := (𝓕 f).isBigO_cocompact_rpow (-2)
    have := summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hO.comp_tendsto Int.tendsto_coe_cofinite)
    simp only [SchwartzMap.fourier_coe, hf] at this
    exact this
  have hsum' : Summable (fun n : ℤ => 𝓕 (aux φ L) ((-n : ℤ) : ℝ)) :=
    hsum.comp_injective neg_injective
  refine ⟨?_, ?_⟩
  · simp_rw [hT]; exact hsum'.mul_left _
  · have hP := SchwartzMap.tsum_eq_tsum_fourier f 0
    simp only [zero_add, SchwartzMap.fourier_coe, hf] at hP
    simp only [show ((0 : ℝ) : UnitAddCircle) = 0 from rfl, fourier_eval_zero, mul_one] at hP
    simp_rw [hT]
    rw [tsum_mul_left]
    congr 1
    rw [show (∑' n : ℤ, 𝓕 (aux φ L) ((-n : ℤ) : ℝ)) = ∑' n : ℤ, 𝓕 (aux φ L) (n : ℝ) from
      (Equiv.neg ℤ).tsum_eq (fun n : ℤ => 𝓕 (aux φ L) (n : ℝ))]
    rw [← hP]
    exact tsum_congr fun k => aux_int φ hL k

end WindowPoisson
end WeilRH
