/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import WeilRH.XiKStrip

/-!
# `N_K(T) = O(T log T)` from B1 and Jensen's inequality

`latex/notes.tex`, the sentence after `thm:imp-stirling`: for the number `N_K(T)` of zeros `ρ` of
`ξ_K` with `|Im ρ| ≤ T`, counted with multiplicity, `N_K(T) = O(T log T)`. The manuscript cites
Hasanalizade–Shen–Wong; here it is proved from the order-one growth of B1 (`HeckePackage.growth`)
by Mathlib's Jensen inequality `AnalyticOnNhd.sum_divisor_le`, applied on the discs about `2` of
radii `T + 2` and `2(T + 2)`, together with the strip clause `Hecke.xiK_strip` of round 71.

CONDITIONAL on B1 (`HeckePackage K`), an explicit hypothesis. The second bound
`N_K(T+1) − N_K(T) = O(log T)` is not formalized.
-/

open Complex Metric Filter MeromorphicOn

namespace WeilRH.NKCount

variable {K : Type} [Field K] [NumberField K] (hB : HeckePackage K)

/-- `N_K(T)`: the zeros `ρ` of `ξ_K` with `|Im ρ| ≤ T`, counted with multiplicity. -/
noncomputable def zeroCount (T : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | Hecke.xi hB ρ = 0 ∧ |ρ.im| ≤ T}, (analyticOrderNatAt (Hecke.xi hB) ρ : ℝ)

theorem analyticOnNhd_xi : AnalyticOnNhd ℂ (Hecke.xi hB) Set.univ :=
  fun z _ => hB.simplePoles.differentiable.analyticAt z

theorem xi_two_ne_zero : Hecke.xi hB 2 ≠ 0 :=
  XiKStrip.xi_ne_zero_of_one_lt_re hB.simplePoles (by norm_num)

theorem analyticOrderAt_ne_top (z : ℂ) : analyticOrderAt (Hecke.xi hB) z ≠ ⊤ := by
  have h2 : analyticOrderAt (Hecke.xi hB) 2 ≠ ⊤ := by
    rw [((analyticOnNhd_xi hB) 2 trivial).analyticOrderAt_eq_zero.mpr (xi_two_ne_zero hB)]
    exact ENat.zero_ne_top
  exact (analyticOnNhd_xi hB).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    trivial trivial h2

/-- On a disc, the divisor of the entire `ξ_K` is its analytic order. -/
theorem divisor_eq (U : Set ℂ) {z : ℂ} (hz : z ∈ U) :
    (divisor (Hecke.xi hB) U z : ℝ) = (analyticOrderNatAt (Hecke.xi hB) z : ℝ) := by
  rw [((analyticOnNhd_xi hB).mono (Set.subset_univ U)).divisor_apply hz]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_ne_top hB z)
  rw [← hn, analyticOrderNatAt, ← hn]
  simp

theorem divisor_nonneg (U : Set ℂ) (z : ℂ) : (0 : ℝ) ≤ divisor (Hecke.xi hB) U z := by
  by_cases hz : z ∈ U
  · rw [divisor_eq hB U hz]; positivity
  · simp [hz]

/-- Every zero with `|Im ρ| ≤ T` lies in the closed disc of radius `T + 2` about `2`. -/
theorem mem_closedBall_two {T : ℝ} {ρ : ℂ} (hρ : Hecke.xi hB ρ = 0) (hT : |ρ.im| ≤ T) :
    ρ ∈ closedBall (2 : ℂ) |T + 2| := by
  obtain ⟨h0, h1⟩ := Hecke.xiK_strip hB hρ
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  rw [mem_closedBall, dist_eq_norm, abs_of_nonneg (by linarith)]
  calc ‖ρ - 2‖ ≤ |(ρ - 2).re| + |(ρ - 2).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 + T := by
      have : |(ρ - 2).re| ≤ 2 := by
        rw [abs_le]; simp; constructor <;> linarith
      have him : (ρ - 2).im = ρ.im := by simp
      rw [him]
      linarith
    _ = T + 2 := by ring

/-- `N_K(T)` is bounded by the divisor sum over the disc of radius `T + 2` about `2`. -/
theorem zeroCount_le_divisor_sum {T : ℝ} :
    zeroCount hB T ≤ ∑ᶠ u, (divisor (Hecke.xi hB) (closedBall (2 : ℂ) |T + 2|) u : ℝ) := by
  set D := fun u => (divisor (Hecke.xi hB) (closedBall (2 : ℂ) |T + 2|) u : ℝ)
  set S := {ρ : ℂ | Hecke.xi hB ρ = 0 ∧ |ρ.im| ≤ T}
  have hfin : (Function.support D).Finite :=
    ((divisor (Hecke.xi hB) (closedBall (2 : ℂ) |T + 2|)).finiteSupport
      (isCompact_closedBall _ _)).subset (fun u hu => by simpa [D] using hu)
  have hS : zeroCount hB T = ∑ᶠ ρ ∈ S, D ρ := by
    refine finsum_mem_congr rfl (fun ρ hρ => ?_)
    exact (divisor_eq hB _ (mem_closedBall_two hB hρ.1 hρ.2)).symm
  rw [hS, finsum_mem_def]
  refine finsum_le_finsum (hfin.subset (by rw [Set.support_indicator]; exact Set.inter_subset_right)) hfin (fun u => ?_)
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu]; exact divisor_nonneg hB _ u

/-- Each zero of `ξ_K` has positive multiplicity. -/
theorem analyticOrderNatAt_pos {ρ : ℂ} (hρ : Hecke.xi hB ρ = 0) :
    0 < analyticOrderNatAt (Hecke.xi hB) ρ := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_ne_top hB ρ)
  have h0 : analyticOrderAt (Hecke.xi hB) ρ ≠ 0 := fun h =>
    (((analyticOnNhd_xi hB) ρ trivial).analyticOrderAt_eq_zero.1 h) hρ
  rw [analyticOrderNatAt, ← hn, ENat.toNat_coe]
  rw [← hn] at h0
  exact Nat.pos_of_ne_zero (by exact_mod_cast h0)

/-- The zeros of `ξ_K` with `|Im ρ| ≤ T` form a finite set, so `zeroCount` is a genuine finite
count (not the junk value of `finsum` on an infinite support). -/
theorem zeroSet_finite (T : ℝ) : {ρ : ℂ | Hecke.xi hB ρ = 0 ∧ |ρ.im| ≤ T}.Finite := by
  refine ((divisor (Hecke.xi hB) (closedBall (2 : ℂ) |T + 2|)).finiteSupport
    (isCompact_closedBall _ _)).subset (fun ρ hρ => ?_)
  rw [Function.mem_support]
  have hD := divisor_eq hB (closedBall (2 : ℂ) |T + 2|) (mem_closedBall_two hB hρ.1 hρ.2)
  have hpos := analyticOrderNatAt_pos hB hρ.1
  intro h
  rw [h] at hD
  have h0 : (analyticOrderNatAt (Hecke.xi hB) ρ : ℝ) = 0 := by rw [← hD]; simp
  have h0' : analyticOrderNatAt (Hecke.xi hB) ρ = 0 := by exact_mod_cast h0
  omega

/-- `N_K(T)` as a finite sum over the (finite) zero set. -/
theorem zeroCount_eq_sum (T : ℝ) :
    zeroCount hB T = ∑ ρ ∈ (zeroSet_finite hB T).toFinset,
      (analyticOrderNatAt (Hecke.xi hB) ρ : ℝ) := by
  rw [zeroCount, finsum_mem_eq_finite_toFinset_sum _ (zeroSet_finite hB T)]

/-- `N_K(T) ≥ 0`, and it is positive as soon as some zero has `|Im ρ| ≤ T`. -/
theorem zeroCount_pos {T : ℝ} {ρ : ℂ} (hρ : Hecke.xi hB ρ = 0) (hT : |ρ.im| ≤ T) :
    0 < zeroCount hB T := by
  rw [zeroCount_eq_sum]
  refine Finset.sum_pos' (fun _ _ => by positivity) ⟨ρ, ?_, ?_⟩
  · simpa using ⟨hρ, hT⟩
  · exact_mod_cast analyticOrderNatAt_pos hB hρ

/-- **`N_K(T) = O(T log T)`**, CONDITIONAL on B1: there is `C` with `N_K(T) ≤ C T log T` for
`T ≥ 2`. -/
theorem zeroCount_le : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → zeroCount hB T ≤ C * T * Real.log T := by
  obtain ⟨C₀, hC₀⟩ := hB.growth
  set C₁ := max C₀ 0
  set a := |Real.log ‖Hecke.xi hB 2‖|
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(C₁ * 20 + a) / Real.log 2, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  set r : ℝ := T + 2
  set R : ℝ := 2 * (T + 2)
  set M : ℝ := Real.exp (C₁ * (2 * T + 6) * Real.log (2 * T + 6))
  have hr : 0 < |r| := by simp [r]; positivity
  have hrR : |r| < |R| := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < r), abs_of_pos (by positivity : (0 : ℝ) < R)]
    simp only [r, R]; linarith
  have hlog6 : 0 ≤ Real.log (2 * T + 6) := Real.log_nonneg (by linarith)
  have hM1 : 1 ≤ M := Real.one_le_exp (by positivity)
  have hbound : ∀ z ∈ sphere (2 : ℂ) |R|, ‖Hecke.xi hB z‖ ≤ M := by
    intro z hz
    rw [mem_sphere, dist_eq_norm, abs_of_pos (by positivity : (0 : ℝ) < R)] at hz
    have hz1 : ‖z‖ ≤ 2 * T + 6 := by
      have := norm_le_norm_add_norm_sub' z 2
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      calc ‖z‖ ≤ ‖z - 2‖ + ‖(2 : ℂ)‖ := by
            have := norm_sub_norm_le z 2; linarith
        _ = 2 * T + 6 := by rw [hz, h2]; simp only [R]; ring
    have hz2 : 2 ≤ ‖z‖ := by
      have := norm_sub_norm_le z 2
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      have : ‖z - 2‖ ≤ ‖z‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      rw [hz, h2] at this; simp only [R] at this; linarith
    by_cases h0 : Hecke.xi hB z = 0
    · rw [h0, norm_zero]; linarith
    · have hpos : 0 < ‖Hecke.xi hB z‖ := norm_pos_iff.2 h0
      rw [← Real.exp_log hpos]
      apply Real.exp_le_exp.2
      have hg := hC₀ z hz2
      have hlz : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (by linarith)
      calc Real.log ‖Hecke.xi hB z‖ ≤ C₀ * ‖z‖ * Real.log ‖z‖ := hg
        _ ≤ C₁ * ‖z‖ * Real.log ‖z‖ := by
            have : C₀ ≤ C₁ := le_max_left _ _
            have : 0 ≤ ‖z‖ * Real.log ‖z‖ := by positivity
            nlinarith
        _ ≤ C₁ * (2 * T + 6) * Real.log (2 * T + 6) := by
            have hC1 : 0 ≤ C₁ := le_max_right _ _
            have : Real.log ‖z‖ ≤ Real.log (2 * T + 6) :=
              Real.log_le_log (by linarith) hz1
            have hn : 0 ≤ ‖z‖ := norm_nonneg _
            calc C₁ * ‖z‖ * Real.log ‖z‖ ≤ C₁ * (2 * T + 6) * Real.log ‖z‖ := by
                  apply mul_le_mul_of_nonneg_right _ hlz
                  exact mul_le_mul_of_nonneg_left hz1 hC1
              _ ≤ C₁ * (2 * T + 6) * Real.log (2 * T + 6) := by
                  apply mul_le_mul_of_nonneg_left this; positivity
  have hJ := ((analyticOnNhd_xi hB).mono (Set.subset_univ _)).sum_divisor_le hr hrR hM1
    (xi_two_ne_zero hB) hbound
  -- move the coercion inside the finsum
  have hcast : ((∑ᶠ u, divisor (Hecke.xi hB) (closedBall (2 : ℂ) |r|) u : ℤ) : ℝ) =
      ∑ᶠ u, (divisor (Hecke.xi hB) (closedBall (2 : ℂ) |r|) u : ℝ) :=
    map_finsum (Int.castRingHom ℝ)
      ((divisor _ _).finiteSupport (isCompact_closedBall _ _))
  rw [hcast] at hJ
  have hRr : R / r = 2 := by simp only [R, r]; field_simp
  rw [hRr] at hJ
  have hxi2 : 0 < ‖Hecke.xi hB 2‖ := norm_pos_iff.2 (xi_two_ne_zero hB)
  rw [Real.log_div (by positivity) hxi2.ne', Real.log_exp] at hJ
  -- elementary bounds
  have hlog5 : Real.log (2 * T + 6) ≤ 4 * Real.log T := by
    have h5T : 2 * T + 6 ≤ T ^ 4 := by
      have h3 : 8 ≤ T ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hT 3
        norm_num at this; linarith
      have : T ^ 4 = T * T ^ 3 := by ring
      nlinarith
    calc Real.log (2 * T + 6) ≤ Real.log (T ^ 4) := Real.log_le_log (by linarith) h5T
      _ = 4 * Real.log T := by rw [Real.log_pow]; norm_num
  have hC1 : 0 ≤ C₁ := le_max_right _ _
  have ha : -Real.log ‖Hecke.xi hB 2‖ ≤ a := neg_le_abs _
  have hTlog : Real.log 2 ≤ T * Real.log T := by nlinarith
  have key : C₁ * (2 * T + 6) * Real.log (2 * T + 6) - Real.log ‖Hecke.xi hB 2‖ ≤
      (C₁ * 20 + a) * T * Real.log T := by
    have h1 : C₁ * (2 * T + 6) * Real.log (2 * T + 6) ≤ C₁ * 20 * T * Real.log T := by
      have : (2 * T + 6) * Real.log (2 * T + 6) ≤ 5 * T * (4 * Real.log T) := by
        apply mul_le_mul (by linarith) hlog5 hlog6 (by positivity)
      nlinarith
    have h2 : a ≤ a * T * Real.log T := by
      have ha0 : 0 ≤ a := abs_nonneg _
      have : 1 ≤ T * Real.log T := by
        have : Real.log 2 * 2 ≤ T * Real.log T := by nlinarith
        have : (1 : ℝ) ≤ Real.log 2 * 2 := by
          have := Real.log_two_gt_d9; linarith
        linarith
      nlinarith
    linarith
  calc zeroCount hB T ≤ ∑ᶠ u, (divisor (Hecke.xi hB) (closedBall (2 : ℂ) |r|) u : ℝ) :=
        zeroCount_le_divisor_sum hB
    _ ≤ (C₁ * (2 * T + 6) * Real.log (2 * T + 6) - Real.log ‖Hecke.xi hB 2‖) / Real.log 2 := hJ
    _ ≤ (C₁ * 20 + a) * T * Real.log T / Real.log 2 := by gcongr
    _ = (C₁ * 20 + a) / Real.log 2 * T * Real.log T := by ring

end WeilRH.NKCount
