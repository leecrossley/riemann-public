/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import WeilRH.GapStrip
import WeilRH.Hurwitz
import WeilRH.EtaZeta
import WeilRH.HbHigh

/-!
# `prop:rouche-route` (round 73)

Source: `latex/notes.tex`, `prop:rouche-route`, with `def:residual-gap` and `prop:gap`
(`WeilRH.Gap`), `def:zeta` (d) (`F = riemannXiUpper`) and `prop:F0` (`F_zero_pos`).

For each `j` let `(𝓔_j, A_j, v_j, μ_j)` be a gap datum on `[-ℓ_j, ℓ_j]` with gap `d_j` and let
`k_j ∈ 𝓔_j` have residual `r_j = ‖(A_j - μ_j)k_j‖` and projection `w_j`. If
(a) every zero of `v̂_j` is real, (b) `k̂_j → F` locally uniformly on `𝕊 = {|Im z| < 1/2}` and
(c) `C(ℓ_j, b) r_j/d_j → 0` for every `0 < b < 1/2`, then every zero of `F` is real
(`rouche_route`).

* `Gap.differentiable_hat`: `ĝ` is entire for `g ∈ L²([-ℓ, ℓ])` (differentiation under the
  integral; implicit in the manuscript).
* The Hurwitz step is `Hurwitz.im_eq_zero_of_tendsto`.
* `riemannXiUpper_eq_zero_mem_strip`: every zero of `F` lies in `𝕊` (from `prop:hb-high` and
  `ξ(1 - s) = ξ(s)`), which is the manuscript's closing clause "all of which lie in `𝕊`".

**Representation.** As in `prop:gap`, the gap is a lower bound `d_j ≤ |λ - μ_j|` on the eigenvalues
of `A_j` on `v_j^⊥` and `v_j` need not be a unit vector.
-/

open MeasureTheory Complex Set Filter Topology Metric
open scoped InnerProductSpace

namespace WeilRH

namespace Gap

lemma isFiniteMeasure_μI (ℓ : ℝ) : IsFiniteMeasure (μI ℓ) :=
  isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne

/-- `ĝ` is entire. -/
theorem differentiable_hat {ℓ : ℝ} (g : L2I ℓ) : Differentiable ℂ (hat g) := by
  have := isFiniteMeasure_μI ℓ
  have hgi : Integrable (fun t => (g : ℝ → ℂ) t) (μI ℓ) :=
    (Lp.memLp g).integrable (by norm_num)
  intro z₀
  set K : ℝ := Real.exp ((|z₀.im| + 1) * |ℓ|)
  have hbd : ∀ z ∈ ball z₀ 1, ∀ t ∈ Icc (-ℓ) ℓ, ‖cexp (I * z * t)‖ ≤ K := by
    intro z hz t ht
    rw [norm_cexp_I_mul, Real.exp_le_exp]
    have ht' : |t| ≤ |ℓ| := (abs_le.mpr ⟨ht.1, ht.2⟩).trans (le_abs_self ℓ)
    have hzim : |z.im| ≤ |z₀.im| + 1 := by
      have h1 : |(z - z₀).im| ≤ ‖z - z₀‖ := abs_im_le_norm _
      rw [← dist_eq_norm] at h1
      have h2 := (mem_ball.1 hz).le
      rw [sub_im] at h1
      have := abs_sub_abs_le_abs_sub z.im z₀.im
      linarith
    calc -(z.im * t) ≤ |z.im * t| := neg_le_abs _
      _ = |z.im| * |t| := abs_mul _ _
      _ ≤ (|z₀.im| + 1) * |ℓ| := by gcongr
  have hmeas : ∀ z, AEStronglyMeasurable (fun t : ℝ => (g : ℝ → ℂ) t * cexp (I * z * t)) (μI ℓ) :=
    fun z => (Lp.aestronglyMeasurable g).mul (by fun_prop : Continuous fun t : ℝ =>
      cexp (I * z * t)).aestronglyMeasurable
  have hmem : ∀ᵐ t ∂(μI ℓ), t ∈ Icc (-ℓ) ℓ := ae_restrict_mem measurableSet_Icc
  have hint : Integrable (fun t : ℝ => (g : ℝ → ℂ) t * cexp (I * z₀ * t)) (μI ℓ) := by
    refine Integrable.mono' (hgi.norm.mul_const K) (hmeas z₀) ?_
    filter_upwards [hmem] with t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbd z₀ (mem_ball_self one_pos) t ht) (norm_nonneg _)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μI ℓ)
    (F := fun z t => (g : ℝ → ℂ) t * cexp (I * z * t))
    (F' := fun z t => (g : ℝ → ℂ) t * (cexp (I * z * t) * (I * t)))
    (bound := fun t => ‖(g : ℝ → ℂ) t‖ * (K * |ℓ|)) (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall hmeas) hint
    ((Lp.aestronglyMeasurable g).mul (by fun_prop : Continuous fun t : ℝ =>
      cexp (I * z₀ * t) * (I * t)).aestronglyMeasurable) ?_ (hgi.norm.mul_const _) ?_
  · exact hderiv.2.differentiableAt
  · filter_upwards [hmem] with t ht z hz
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left (mul_le_mul (hbd z hz t ht) ?_ (norm_nonneg _)
      (Real.exp_pos _).le) (norm_nonneg _)
    rw [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨ht.1, ht.2⟩).trans (le_abs_self ℓ)
  · refine Eventually.of_forall fun t z _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => I * z * t) (I * t) z := by
      simpa using ((hasDerivAt_id z).const_mul I).mul_const (t : ℂ)
    exact h1.cexp.const_mul _

lemma hat_smul {ℓ : ℝ} (c : ℂ) (g : L2I ℓ) (z : ℂ) : hat (c • g) z = c * hat g z := by
  rw [hat_eq_inner, hat_eq_inner, inner_smul_right]

end Gap

/-- `F(-z) = F(z)` (from `ξ(1 - s) = ξ(s)`). -/
lemma riemannXiUpper_neg (z : ℂ) : riemannXiUpper (-z) = riemannXiUpper z := by
  simp only [riemannXiUpper]
  rw [← completedXi_one_sub]; congr 1; ring

/-- Every zero of `F` lies in the strip `𝕊 = {|Im z| < 1/2}`. -/
lemma riemannXiUpper_eq_zero_mem_strip {z : ℂ} (hz : riemannXiUpper z = 0) : |z.im| < 1 / 2 := by
  by_contra h
  rcases le_abs'.1 (not_lt.1 h) with h' | h'
  · have : 1 / 2 ≤ (-z).im := by simp; linarith
    exact riemannXiUpper_ne_zero this (by rw [riemannXiUpper_neg]; exact hz)
  · exact riemannXiUpper_ne_zero h' hz

/-- The strip `𝕊 = {|Im z| < 1/2}`. -/
def strip : Set ℂ := {z | |z.im| < 1 / 2}

lemma isOpen_strip : IsOpen strip := isOpen_lt (continuous_abs.comp continuous_im) continuous_const

lemma isPreconnected_strip : IsPreconnected strip := by
  have : strip = {z : ℂ | -(1/2) < z.im} ∩ {z : ℂ | z.im < 1/2} := by
    ext z; simp [strip, abs_lt]
  rw [this]
  have hl : IsLinearMap ℝ (fun z : ℂ => z.im) := ⟨fun x y => by simp, fun c x => by simp⟩
  exact ((convex_halfSpace_gt hl _).inter (convex_halfSpace_lt hl _)).isPreconnected

/-- Every compact subset of `𝕊` lies in some `{|Im z| ≤ b}` with `0 < b < 1/2`. -/
lemma exists_b_of_isCompact {L : Set ℂ} (hL : IsCompact L) (hLS : L ⊆ strip) :
    ∃ b, 0 < b ∧ b < 1 / 2 ∧ ∀ z ∈ L, |z.im| ≤ b := by
  rcases L.eq_empty_or_nonempty with h | h
  · exact ⟨1 / 4, by norm_num, by norm_num, by simp [h]⟩
  obtain ⟨z₁, hz₁, hmax⟩ := hL.exists_isMaxOn h (continuous_abs.comp continuous_im).continuousOn
  have h1 : |z₁.im| < 1 / 2 := hLS hz₁
  refine ⟨max |z₁.im| (1 / 4), by positivity, max_lt h1 (by norm_num), fun z hz => ?_⟩
  exact (hmax hz).trans (le_max_left _ _)

open Gap in
/-- **`prop:rouche-route`.** -/
theorem rouche_route (ℓ : ℕ → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (𝓔 : ∀ j, Submodule ℂ (L2I (ℓ j))) [∀ j, FiniteDimensional ℂ (𝓔 j)]
    (A : ∀ j, 𝓔 j →ₗ[ℂ] 𝓔 j) (hA : ∀ j, (A j).IsSymmetric) (v : ∀ j, 𝓔 j) (c : ℕ → ℂ)
    (hv : ∀ j, A j (v j) = c j • v j) (μ : ℕ → ℝ) (d : ℕ → ℝ) (hd : ∀ j, 0 < d j)
    (hgap : ∀ j, ∀ c' : ℂ,
      Module.End.HasEigenvalue ((A j).restrict (orth_invariant (hA j) (hv j))) c' →
        d j ≤ ‖c' - μ j‖)
    (k : ∀ j, 𝓔 j)
    (ha : ∀ j, ∀ z, hat ((v j : 𝓔 j) : L2I (ℓ j)) z = 0 → z.im = 0)
    (hb : TendstoLocallyUniformlyOn (fun j z => hat ((k j : 𝓔 j) : L2I (ℓ j)) z)
      riemannXiUpper atTop strip)
    (hc : ∀ b, 0 < b → b < 1 / 2 →
      Tendsto (fun j => C (ℓ j) b * (‖A j (k j) - (μ j : ℂ) • k j‖ / d j)) atTop (𝓝 0)) :
    ∀ z, riemannXiUpper z = 0 → z.im = 0 := by
  -- the projections `w_j`
  set w : ∀ j, 𝓔 j := fun j => (ℂ ∙ v j).starProjection (k j)
  set W : ℕ → ℂ → ℂ := fun j z => hat ((w j : 𝓔 j) : L2I (ℓ j)) z
  have hW : ∀ j, DifferentiableOn ℂ (W j) strip :=
    fun j => (differentiable_hat _).differentiableOn
  have hFd : DifferentiableOn ℂ riemannXiUpper strip :=
    ((differentiable_completedXi.comp (by fun_prop : Differentiable ℂ fun z : ℂ => 1 / 2 - I * z))
      ).differentiableOn
  -- `ŵ_j → F` locally uniformly on `𝕊`
  have hconv : TendstoLocallyUniformlyOn W riemannXiUpper atTop strip := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_strip] at hb ⊢
    intro L hLS hL
    obtain ⟨b, hb0, hb1, hbL⟩ := exists_b_of_isCompact hL hLS
    have hu := hb L hLS hL
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε hε
    have h0 := (hc b hb0 hb1).eventually (gt_mem_nhds (half_pos hε))
    filter_upwards [hu (ε / 2) (half_pos hε), h0] with j hj hj0 z hz
    have hg := (gap (hℓ j) (𝓔 j) (hA j) (hv j) (μ j) (hd j) (hgap j) (k j)).2 b hb0.le z (hbL z hz)
    calc dist (riemannXiUpper z) (W j z)
        ≤ dist (riemannXiUpper z) (hat ((k j : 𝓔 j) : L2I (ℓ j)) z) +
          dist (hat ((k j : 𝓔 j) : L2I (ℓ j)) z) (W j z) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add (hj z hz) ?_
          rw [dist_eq_norm]
          exact hg.trans_lt hj0
      _ = ε := by ring
  -- eventually `ŵ_j(0) ≠ 0`, hence the zeros of `ŵ_j` are those of `v̂_j`
  have h0S : (0 : ℂ) ∈ strip := by simp [strip]
  have hF0 : riemannXiUpper 0 ≠ 0 := by
    obtain ⟨h1, h2, h3⟩ := F_zero_pos
    intro h; rw [h1] at h; rw [h] at h3; simp at h3
  have hpt : Tendsto (fun j => W j 0) atTop (𝓝 (riemannXiUpper 0)) :=
    hconv.tendsto_at h0S
  have hev0 : ∀ᶠ j in atTop, W j 0 ≠ 0 := hpt.eventually_ne hF0
  have hreal : ∀ᶠ j in atTop, ∀ z ∈ strip, W j z = 0 → z.im = 0 := by
    filter_upwards [hev0] with j hj z _ hz
    have hw : ((w j : 𝓔 j) : L2I (ℓ j)) =
        (⟪(v j : 𝓔 j), k j⟫_ℂ / ((‖v j‖ : ℂ) ^ 2)) • ((v j : 𝓔 j) : L2I (ℓ j)) := by
      simp only [w, Submodule.starProjection_singleton, Submodule.coe_smul]
      congr 2
      push_cast; rfl
    have hWz : ∀ z, W j z =
        (⟪(v j : 𝓔 j), k j⟫_ℂ / ((‖v j‖ : ℂ) ^ 2)) * hat ((v j : 𝓔 j) : L2I (ℓ j)) z := by
      intro z; simp only [W]; rw [hw, hat_smul]
    have hcoef : ⟪(v j : 𝓔 j), k j⟫_ℂ / ((‖v j‖ : ℂ) ^ 2) ≠ 0 := by
      intro h; apply hj; rw [hWz, h, zero_mul]
    rw [hWz] at hz
    exact ha j z ((mul_eq_zero.1 hz).resolve_left hcoef)
  intro z hz
  exact Hurwitz.im_eq_zero_of_tendsto isOpen_strip isPreconnected_strip hFd h0S hF0 hW hreal hconv
    z (riemannXiUpper_eq_zero_mem_strip hz) hz

end WeilRH
