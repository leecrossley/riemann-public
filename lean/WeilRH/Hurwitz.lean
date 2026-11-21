/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Hurwitz's theorem and the zero-reality step of `prop:rouche-route` (round 73)

* `Hurwitz.exists_zero`: if holomorphic `W j → F` uniformly on a closed disc `D̄(z₀, r)`, `F(z₀) = 0`
  and `F` has no zero on the circle `|z - z₀| = r`, then `W j` has a zero in the disc for all large
  `j`. The proof is the maximum-modulus argument applied to `1 / W j`.
* `Hurwitz.im_eq_zero_of_tendsto`: on a preconnected open set `S`, if `W j → F` locally uniformly,
  `F` is holomorphic and not zero at one point, and eventually every zero of `W j` in `S` is real,
  then every zero of `F` in `S` is real. This is the analytic core of the manuscript's proof of
  `prop:rouche-route` (the paragraph "Suppose `F(z₀) = 0` with `z₀ ∉ ℝ` …").
-/

open Complex Set Filter Topology Metric

namespace WeilRH

namespace Hurwitz

/-- **Hurwitz's theorem** (existence of zeros near a zero of the limit). -/
theorem exists_zero {W : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : ∀ j, DifferentiableOn ℂ (W j) (closedBall z₀ r))
    (hF : ContinuousOn F (closedBall z₀ r))
    (hu : TendstoUniformlyOn W F atTop (closedBall z₀ r)) (hz₀ : F z₀ = 0)
    (hsph : ∀ z ∈ sphere z₀ r, F z ≠ 0) :
    ∀ᶠ j in atTop, ∃ z ∈ closedBall z₀ r, W j z = 0 := by
  -- the minimum `m > 0` of `‖F‖` on the circle
  have hsc : IsCompact (sphere z₀ r) := isCompact_sphere z₀ r
  have hsne : (sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.2 hr.le
  obtain ⟨z₁, hz₁, hmin⟩ := hsc.exists_isMinOn hsne
    ((hF.mono sphere_subset_closedBall).norm)
  set m := ‖F z₁‖
  have hm : 0 < m := norm_pos_iff.2 (hsph z₁ hz₁)
  have hev := Metric.tendstoUniformlyOn_iff.1 hu (m / 2) (by linarith)
  filter_upwards [hev] with j hj
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hcl : closure (ball z₀ r) = closedBall z₀ r := closure_ball z₀ hr.ne'
  have hd : DiffContOnCl ℂ (fun z => (W j z)⁻¹) (ball z₀ r) := by
    refine DiffContOnCl.inv ?_ (fun z hz => hcon z (hcl ▸ hz))
    exact (hW j).diffContOnCl_ball subset_rfl
  have hbound : ∀ z ∈ frontier (ball z₀ r), ‖(W j z)⁻¹‖ ≤ 2 / m := by
    intro z hz
    rw [frontier_ball z₀ hr.ne'] at hz
    have h1 : m ≤ ‖F z‖ := hmin hz
    have h2 : dist (F z) (W j z) < m / 2 := hj z (sphere_subset_closedBall hz)
    rw [dist_eq_norm] at h2
    have h3 : m / 2 < ‖W j z‖ := by
      have := norm_sub_norm_le (F z) (F z - W j z)
      simp only [sub_sub_cancel] at this
      linarith
    rw [norm_inv]
    calc ‖W j z‖⁻¹ ≤ (m / 2)⁻¹ := inv_anti₀ (by positivity) h3.le
      _ = 2 / m := by rw [inv_div]
  have hc := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hbound
    (subset_closure (mem_ball_self hr))
  have h4 : dist (F z₀) (W j z₀) < m / 2 := hj z₀ (mem_closedBall_self hr.le)
  rw [hz₀, dist_zero_left] at h4
  rw [norm_inv] at hc
  have hW0 : 0 < ‖W j z₀‖ := norm_pos_iff.2 (hcon z₀ (mem_closedBall_self hr.le))
  have : m / 2 ≤ ‖W j z₀‖ := by
    have := (inv_le_comm₀ hW0 (by positivity)).1 (hc.trans (le_of_eq (by ring) : 2 / m ≤ (m / 2)⁻¹))
    simpa using this
  linarith

/-- **Zeros of a locally uniform limit are real** if those of the approximants eventually are. -/
theorem im_eq_zero_of_tendsto {S : Set ℂ} (hS : IsOpen S) (hSc : IsPreconnected S)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F S) {x₀ : ℂ} (hx₀ : x₀ ∈ S) (hFx₀ : F x₀ ≠ 0)
    {W : ℕ → ℂ → ℂ} (hW : ∀ j, DifferentiableOn ℂ (W j) S)
    (hreal : ∀ᶠ j in atTop, ∀ z ∈ S, W j z = 0 → z.im = 0)
    (hconv : TendstoLocallyUniformlyOn W F atTop S) :
    ∀ z ∈ S, F z = 0 → z.im = 0 := by
  intro z₀ hz₀S hFz₀
  by_contra him
  have han : AnalyticOnNhd ℂ F S := hF.analyticOnNhd hS
  rcases (han z₀ hz₀S).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact hFx₀ (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hSc hz₀S h hx₀)
  -- a punctured disc around `z₀` free of zeros, inside `S`
  obtain ⟨ε, hε, hεF⟩ : ∃ ε > 0, ∀ z, z ∈ ball z₀ ε → z ≠ z₀ → F z ≠ 0 := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hh⟩ := h
    exact ⟨ε, hε, fun z hz hne => hh hz hne⟩
  obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.1 hS z₀ hz₀S
  have hb : 0 < |z₀.im| := abs_pos.2 him
  set r := min (min ε δ) |z₀.im| / 2
  have hr : 0 < r := by positivity
  have hrε : r < ε := by
    have := min_le_left (min ε δ) |z₀.im|; have := min_le_left ε δ
    simp only [r]; linarith
  have hrδ : r < δ := by
    have := min_le_left (min ε δ) |z₀.im|; have := min_le_right ε δ
    simp only [r]; linarith
  have hrim : r < |z₀.im| := by
    have := min_le_right (min ε δ) |z₀.im|
    simp only [r]; linarith
  have hDS : closedBall z₀ r ⊆ S :=
    (closedBall_subset_ball hrδ).trans hδS
  have hu : TendstoUniformlyOn W F atTop (closedBall z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hS).1 hconv _ hDS (isCompact_closedBall z₀ r)
  have hzeros := exists_zero hr (fun j => (hW j).mono hDS) (hF.continuousOn.mono hDS) hu hFz₀
    (fun z hz => hεF z (sphere_subset_closedBall.trans (closedBall_subset_ball hrε) hz)
      (fun h => by rw [h, mem_sphere, dist_self] at hz; linarith))
  obtain ⟨j, ⟨z, hz, hWz⟩, hj⟩ := (hzeros.and hreal).exists
  have hzim : z.im = 0 := hj z (hDS hz) hWz
  have : |z₀.im| ≤ r := by
    have h1 : |(z - z₀).im| ≤ ‖z - z₀‖ := abs_im_le_norm _
    rw [← dist_eq_norm] at h1
    simp only [sub_im, hzim, zero_sub, abs_neg] at h1
    exact h1.trans (mem_closedBall.1 hz)
  linarith

end Hurwitz

end WeilRH
