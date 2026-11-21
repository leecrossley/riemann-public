/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# A zero in the upper half-plane forces negative `Im(-G'/G)` below it (`prop:R11` (iv))

Source: `latex/notes.tex`, Proposition `prop:R11`, item (iv): let `G` be entire, `G ≢ 0`, with a
zero `z₀` in the upper half-plane of order `k ≥ 1`. Then there is `ε₀ ∈ (0, Im z₀)` such that
`-G'/G` is holomorphic at `z₀ - iε` and `Im(-G'/G)(z₀ - iε) < 0` for `0 < ε < ε₀`.

`im_neg_logDeriv_lt_zero` is that statement. The order is `analyticOrderAt G z₀ = k` with
`1 ≤ k : ℕ`; a finite order already rules out `G ≡ 0` near `z₀`, so `G ≢ 0` is not a separate
hypothesis. "Holomorphic at `w`" is `AnalyticAt ℂ (fun z => -deriv G z / G z) w`, and the statement
also records `G w ≠ 0`.

Proof (as in the notes): locally `G = (z - z₀)^k H` with `H(z₀) ≠ 0`, so
`-G'/G = -k/(z - z₀) - H'/H`. At `z = z₀ - iε`, `-k/(z - z₀) = -ik/ε` has imaginary part `-k/ε`,
while `H'/H` stays bounded near `z₀`.
-/

open Complex Filter Topology

namespace WeilRH

namespace R11

/-- **`prop:R11` (iv).** An entire function with a zero of order `k ≥ 1` at `z₀`, `Im z₀ > 0`, has
`Im(-G'/G) < 0` at `z₀ - iε` for all small `ε > 0`, where `-G'/G` is holomorphic. -/
theorem im_neg_logDeriv_lt_zero {G : ℂ → ℂ} (hG : Differentiable ℂ G) {z₀ : ℂ} (hz₀ : 0 < z₀.im)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : analyticOrderAt G z₀ = k) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < z₀.im ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      G (z₀ - ε * I) ≠ 0 ∧ AnalyticAt ℂ (fun z => -deriv G z / G z) (z₀ - ε * I) ∧
        (-deriv G (z₀ - ε * I) / G (z₀ - ε * I)).im < 0 := by
  have hGa : AnalyticAt ℂ G z₀ := hG.analyticAt z₀
  obtain ⟨H, hHa, hH0, hev⟩ := (hGa.analyticOrderAt_eq_natCast).mp hk
  -- local properties near `z₀`
  have hHan : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ H z := hHa.eventually_analyticAt
  have hHne : ∀ᶠ z in 𝓝 z₀, H z ≠ 0 := hHa.continuousAt.eventually_ne hH0
  set φ : ℂ → ℂ := fun z => deriv H z / H z with hφ
  have hφc : ContinuousAt φ z₀ := (hHa.deriv.continuousAt).div hHa.continuousAt hH0
  set M : ℝ := ‖φ z₀‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  have hφb : ∀ᶠ z in 𝓝 z₀, ‖φ z‖ < M := by
    have := hφc.norm.eventually (gt_mem_nhds (show ‖φ z₀‖ < M by rw [hM]; linarith))
    exact this
  have hev2 : ∀ᶠ w in 𝓝 z₀, ∀ᶠ z in 𝓝 w, G z = (z - z₀) ^ k • H z := hev.eventually_nhds
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (((hHan.and hHne).and hφb).and hev2)
  refine ⟨min (δ / 2) (min (z₀.im / 2) (k / (2 * M))), ?_, ?_, ?_⟩
  · have : (0 : ℝ) < k := by exact_mod_cast hk1
    positivity
  · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  intro ε hε hεlt
  have hεδ : ε < δ := lt_of_lt_of_le hεlt ((min_le_left _ _).trans (by linarith))
  have hεk : ε < k / (2 * M) := lt_of_lt_of_le hεlt ((min_le_right _ _).trans (min_le_right _ _))
  set w := z₀ - ε * I with hw
  have hwz : w - z₀ = -(ε * I) := by rw [hw]; ring
  have hdist : dist w z₀ < δ := by
    rw [dist_eq_norm, hwz, norm_neg, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε]
    exact hεδ
  obtain ⟨⟨⟨hHw, hHw0⟩, hφw⟩, hevw⟩ := hball hdist
  have hwz0 : w - z₀ ≠ 0 := by
    rw [hwz, neg_ne_zero]
    exact mul_ne_zero (by exact_mod_cast hε.ne') I_ne_zero
  have hGw : G w = (w - z₀) ^ k * H w := by
    rw [hevw.self_of_nhds, smul_eq_mul]
  have hGw0 : G w ≠ 0 := by rw [hGw]; exact mul_ne_zero (pow_ne_zero _ hwz0) hHw0
  -- the derivative at `w`
  have hderiv : HasDerivAt (fun z => (z - z₀) ^ k * H z)
      ((k : ℂ) * (w - z₀) ^ (k - 1) * 1 * H w + (w - z₀) ^ k * deriv H w) w := by
    have h1 := ((hasDerivAt_id w).sub_const z₀).pow k
    exact h1.mul hHw.differentiableAt.hasDerivAt
  have hdG : deriv G w = (k : ℂ) * (w - z₀) ^ (k - 1) * 1 * H w + (w - z₀) ^ k * deriv H w := by
    have heq : G =ᶠ[𝓝 w] fun z => (z - z₀) ^ k * H z := by
      filter_upwards [hevw] with z hz
      rw [hz, smul_eq_mul]
    rw [heq.deriv_eq]
    exact hderiv.deriv
  have hlog : -deriv G w / G w = -((k : ℂ) / (w - z₀)) - φ w := by
    rw [hdG, hGw, hφ]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  have hkw : (k : ℂ) / (w - z₀) = ((k / ε : ℝ) : ℂ) * I := by
    rw [hwz]
    have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    push_cast
    field_simp
    rw [I_sq]
    ring
  refine ⟨hGw0, ?_, ?_⟩
  · exact (((hG.analyticAt w).deriv).neg).div (hG.analyticAt w) hGw0
  · rw [hlog, hkw]
    simp only [sub_im, neg_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero]
    have hφim : -(φ w).im < M := by
      have := Complex.abs_im_le_norm (φ w)
      have := neg_le_abs (φ w).im
      linarith
    have hkε : M < k / ε := by
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      rw [lt_div_iff₀ hε]
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * M)).mp hεk
      nlinarith
    linarith

end R11

end WeilRH
