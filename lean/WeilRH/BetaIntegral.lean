/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import WeilRH.BetaP

/-!
# The Beta integral of `prop:beta`

`latex/notes.tex`, `prop:beta`: for `a ∈ ℂ ∖ (-∞, 0]` and `0 < Re w < 2`, with the principal power,
`a^{-w} = P(w) ∫_0^∞ x^{1-w}(x + a)^{-2} dx`, where `P(w) = sin(πw)/(π(1 - w))`; moreover
`(2π)^w P(w) = w + (1 + log 2π)w² + O(w³)` at `w = 0`. (That `P` is entire with `P(1) = 1` is
`WeilRH.BetaP`.)

* `integral_pos`: for `a = r > 0`, `∫_0^∞ x^{1-w}(x + r)^{-2} dx = Γ(2 - w)Γ(w) r^{-w}`, by writing
  `(x + r)^{-2} = ∫_0^∞ u e^{-(x+r)u} du` and exchanging the integrals (the manuscript substitutes
  `x = at` and uses the Beta function; the value is the same);
* `P_mul_Gamma`: `P(w)Γ(2 - w)Γ(w) = 1` on the strip;
* `beta_identity`: the identity of `prop:beta` for every `a` in the slit plane, by holomorphy in `a`
  (`|x + a| ≥ c(1 + x)` locally uniformly) and the identity theorem;
* `expansion`: `(2π)^w P(w) - w - (1 + log 2π)w² = O(w³)` as `w → 0`.
-/

namespace WeilRH

namespace BetaIntegral

open Complex MeasureTheory Set Filter Asymptotics Topology

noncomputable section

/-- The integrand `x^{1-w}(x + a)^{-2}`. -/
def integrand (w a : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (1 - w) * (((x : ℂ) + a) ^ 2)⁻¹

/-- `(b^2)⁻¹ = ∫_0^∞ u e^{-bu} du` for `b > 0`. -/
lemma inv_sq_eq_integral {b : ℝ} (hb : 0 < b) :
    (b ^ 2)⁻¹ = ∫ u in Ioi (0 : ℝ), u * Real.exp (-(b * u)) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) two_pos hb
  have h1 : ∀ u : ℝ, u ^ ((2 : ℝ) - 1) = u := fun u => by norm_num
  simp only [h1] at h
  rw [h, Real.Gamma_two, mul_one, Real.rpow_two, one_div, inv_pow]

/-- `x^s e^{-bx}` is integrable on `(0, ∞)` for `s > -1`, `b > 0`. -/
lemma integrableOn_rpow_exp {s b : ℝ} (hs : -1 < s) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ s * Real.exp (-(b * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos hb
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

/-- `∫_0^∞ x^{a-1} e^{-ux} dx = u^{-a}Γ(a)` in the form used below. -/
lemma u_mul_one_div_cpow {u : ℝ} (hu : 0 < u) (w : ℂ) :
    (u : ℂ) * (1 / (u : ℂ)) ^ (2 - w) = (u : ℂ) ^ (w - 1) := by
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have harg : (u : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hu.le]; exact Real.pi_ne_zero.symm
  rw [one_div, Complex.inv_cpow _ _ harg]
  have hne : (u : ℂ) ^ (2 - w) ≠ 0 := fun h => hu0 ((Complex.cpow_eq_zero_iff _ _).1 h).1
  rw [mul_inv_eq_iff_eq_mul₀ hne, ← Complex.cpow_add _ _ hu0,
    show (w - 1) + (2 - w) = 1 by ring, Complex.cpow_one]

lemma u_mul_one_div_rpow {u : ℝ} (hu : 0 < u) (σ : ℝ) :
    u * (1 / u) ^ (2 - σ) = u ^ (σ - 1) := by
  rw [one_div, Real.inv_rpow hu.le]
  have hne : u ^ (2 - σ) ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
  rw [mul_inv_eq_iff_eq_mul₀ hne, ← Real.rpow_add hu,
    show (σ - 1) + (2 - σ) = 1 by ring, Real.rpow_one]

section Pos

variable {r : ℝ} {w : ℂ}

/-- The two-variable integrand `x^{1-w} · u e^{-(x+r)u}`. -/
def F (r : ℝ) (w : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (1 - w) * ((p.2 * Real.exp (-((p.1 + r) * p.2)) : ℝ) : ℂ)

lemma measurable_F : Measurable (F r w) := by
  unfold F; fun_prop

lemma norm_F {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) :
    ‖F r w (x, u)‖ = x ^ (1 - w.re) * (u * Real.exp (-((x + r) * u))) := by
  simp only [F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re,
    Complex.one_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu, Real.abs_exp]

lemma F_inner_x (hr : 0 < r) {x : ℝ} (hx : 0 < x) :
    integrand w r x = ∫ u in Ioi (0 : ℝ), F r w (x, u) := by
  simp only [F]
  rw [integral_const_mul, integral_complex_ofReal, ← inv_sq_eq_integral (by linarith : 0 < x + r)]
  simp only [integrand]
  push_cast; rfl

lemma F_inner_u (h2 : w.re < 2) {u : ℝ} (hu : 0 < u) :
    ∫ x in Ioi (0 : ℝ), F r w (x, u) =
      Gamma (2 - w) * ((u : ℂ) ^ (w - 1) * Complex.exp (-((r : ℂ) * u))) := by
  have hre : 0 < (2 - w).re := by simp; linarith
  have key := Complex.integral_cpow_mul_exp_neg_mul_Ioi hre hu
  have e : ∀ x : ℝ, F r w (x, u) =
      ((u : ℂ) * Complex.exp (-((r : ℂ) * u))) *
        ((x : ℂ) ^ ((2 - w) - 1) * Complex.exp (-((u : ℂ) * x))) := by
    intro x
    simp only [F]
    have : (2 - w) - 1 = 1 - w := by ring
    rw [this]
    push_cast
    rw [show -(((x : ℂ) + r) * u) = -((u : ℂ) * x) + -((r : ℂ) * u) by ring, Complex.exp_add]
    ring
  simp_rw [e]
  rw [integral_const_mul, key]
  rw [show (u : ℂ) * Complex.exp (-((r : ℂ) * u)) * ((1 / (u : ℂ)) ^ (2 - w) * Gamma (2 - w)) =
      Gamma (2 - w) * (((u : ℂ) * (1 / (u : ℂ)) ^ (2 - w)) * Complex.exp (-((r : ℂ) * u))) by ring,
    u_mul_one_div_cpow hu]

lemma F_norm_inner_u (h2 : w.re < 2) {u : ℝ} (hu : 0 < u) :
    ∫ x in Ioi (0 : ℝ), ‖F r w (x, u)‖ =
      Real.Gamma (2 - w.re) * (u ^ (w.re - 1) * Real.exp (-(r * u))) := by
  have hre : 0 < 2 - w.re := by linarith
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi hre hu
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x : ℝ =>
      (u * Real.exp (-(r * u))) * (x ^ ((2 - w.re) - 1) * Real.exp (-(u * x))))]
  · rw [integral_const_mul, key]
    rw [show u * Real.exp (-(r * u)) * ((1 / u) ^ (2 - w.re) * Real.Gamma (2 - w.re)) =
        Real.Gamma (2 - w.re) * ((u * (1 / u) ^ (2 - w.re)) * Real.exp (-(r * u))) by ring,
      u_mul_one_div_rpow hu]
  · intro x hx
    simp only [mem_Ioi] at hx
    dsimp only
    rw [norm_F hx hu.le]
    have : (2 - w.re) - 1 = 1 - w.re := by ring
    rw [this, show -((x + r) * u) = -(u * x) + -(r * u) by ring, Real.exp_add]
    ring

lemma integrable_F (hr : 0 < r) (h0 : 0 < w.re) (h2 : w.re < 2) :
    Integrable (F r w) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [integrable_prod_iff' measurable_F.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [mem_Ioi] at hu
    have hI : IntegrableOn (fun x : ℝ =>
        (u * Real.exp (-(r * u))) * (x ^ (1 - w.re) * Real.exp (-(u * x)))) (Ioi 0) :=
      (integrableOn_rpow_exp (by linarith) hu).const_mul _
    refine Integrable.mono' hI (measurable_F.comp measurable_prodMk_right).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [mem_Ioi] at hx
    rw [norm_F hx hu.le, show -((x + r) * u) = -(u * x) + -(r * u) by ring, Real.exp_add]
    exact le_of_eq (by ring)
  · have hI : IntegrableOn (fun u : ℝ =>
        Real.Gamma (2 - w.re) * (u ^ (w.re - 1) * Real.exp (-(r * u)))) (Ioi 0) :=
      (integrableOn_rpow_exp (by linarith) hr).const_mul _
    refine hI.congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (F_norm_inner_u h2 hu).symm

/-- **`prop:beta` for `a = r > 0`.** `∫_0^∞ x^{1-w}(x + r)^{-2} dx = Γ(2 - w)Γ(w) r^{-w}`, and the
integrand is integrable. -/
theorem integral_pos (hr : 0 < r) (h0 : 0 < w.re) (h2 : w.re < 2) :
    IntegrableOn (integrand w r) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), integrand w r x = Gamma (2 - w) * Gamma w * (r : ℂ) ^ (-w) := by
  have hF := integrable_F hr h0 h2
  have hEq : EqOn (integrand w r) (fun x => ∫ u in Ioi (0 : ℝ), F r w (x, u)) (Ioi 0) :=
    fun x hx => F_inner_x hr hx
  refine ⟨?_, ?_⟩
  · exact (hF.integral_prod_left).congr
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => (hEq hx).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi hEq]
    have hswap := integral_integral_swap (f := fun x u => F r w (x, u)) hF
    rw [hswap, setIntegral_congr_fun measurableSet_Ioi (fun u hu => F_inner_u h2 hu),
      integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi h0 hr]
    have hr0 : (r : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm
    rw [one_div, Complex.inv_cpow _ _ hr0, ← Complex.cpow_neg]
    ring

end Pos

/-- `P(w)Γ(2 - w)Γ(w) = 1` for `0 < Re w < 2`. -/
theorem P_mul_Gamma {w : ℂ} (h0 : 0 < w.re) (h2 : w.re < 2) :
    BetaP.P w * (Gamma (2 - w) * Gamma w) = 1 := by
  by_cases hw : w = 1
  · subst hw; norm_num [BetaP.P_one]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  have hsin : Complex.sin (Real.pi * w) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hwk : w = k := by
      have := mul_left_cancel₀ hπ (hk.trans (mul_comm _ _))
      exact this
    have hre : w.re = k := by rw [hwk]; simp
    rw [hre] at h0 h2
    have hk0 : (0 : ℤ) < k := by exact_mod_cast h0
    have hk2 : k < (2 : ℤ) := by exact_mod_cast h2
    have : k = 1 := by omega
    exact hw (by rw [hwk, this]; simp)
  rw [BetaP.P_eq hw, show (2 : ℂ) - w = (1 - w) + 1 by ring, Complex.Gamma_add_one _ h1,
    mul_assoc, mul_comm (Gamma (1 - w)) (Gamma w), Complex.Gamma_mul_Gamma_one_sub]
  field_simp

/-- `x + a ∈ slitPlane`-type lower bound: near every point of the slit plane,
`‖x + a‖ ≥ c(1 + x)` for `x ≥ 0`, uniformly in `a`. -/
lemma lower_bound {a₀ : ℂ} (ha : a₀ ∈ slitPlane) :
    ∃ ε > 0, ∃ c > 0, ∀ a ∈ Metric.ball a₀ ε, ∀ x : ℝ, 0 ≤ x → c * (1 + x) ≤ ‖(x : ℂ) + a‖ := by
  rcases mem_slitPlane_iff.1 ha with h | h
  · refine ⟨a₀.re / 2, by linarith, min 1 (a₀.re / 2), lt_min one_pos (by linarith), ?_⟩
    intro a hal x hx
    rw [Metric.mem_ball, dist_eq_norm] at hal
    have h1 := Complex.abs_re_le_norm (a - a₀)
    rw [Complex.sub_re] at h1
    have h2 := Complex.re_le_norm ((x : ℂ) + a)
    rw [Complex.add_re, Complex.ofReal_re] at h2
    have hm1 : min 1 (a₀.re / 2) ≤ 1 := min_le_left _ _
    have hm2 : min 1 (a₀.re / 2) ≤ a₀.re / 2 := min_le_right _ _
    have hre : a₀.re / 2 < a.re := by
      have := neg_abs_le (a.re - a₀.re); linarith
    nlinarith
  · set m := |a₀.im| / 2 with hm
    have hm0 : 0 < m := by rw [hm]; exact half_pos (abs_pos.2 h)
    set M := ‖a₀‖ + m with hM
    have hM0 : 0 ≤ M := by positivity
    set c := m / (2 * (2 * M + m + 1)) with hc
    have hden : 0 < 2 * (2 * M + m + 1) := by positivity
    have hc0 : 0 < c := div_pos hm0 hden
    have hcm : c * (2 * (2 * M + m + 1)) = m := div_mul_cancel₀ _ hden.ne'
    refine ⟨m, hm0, c, hc0, ?_⟩
    intro a hal x hx
    rw [Metric.mem_ball, dist_eq_norm] at hal
    have hA : m ≤ ‖(x : ℂ) + a‖ := by
      have h1 := Complex.abs_im_le_norm (a - a₀)
      rw [Complex.sub_im] at h1
      have h2 := Complex.abs_im_le_norm ((x : ℂ) + a)
      rw [Complex.add_im, Complex.ofReal_im, zero_add] at h2
      have h3 : |a₀.im| ≤ |a.im| + |a.im - a₀.im| := by
        have := abs_sub_abs_le_abs_sub a₀.im a.im
        rw [abs_sub_comm a₀.im] at this; linarith
      linarith
    have hB : x - M ≤ ‖(x : ℂ) + a‖ := by
      have h1 := norm_sub_le ((x : ℂ) + a) a
      rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at h1
      have h2 := norm_le_of_mem_closedBall (show a ∈ Metric.closedBall a₀ m from
        Metric.mem_closedBall.2 (by rw [dist_eq_norm]; exact hal.le))
      have h3 : ‖a‖ ≤ ‖a₀‖ + m := by
        have := norm_le_norm_add_norm_sub' a a₀
        linarith [norm_sub_rev a a₀]
      linarith
    by_cases hx' : x ≤ 2 * M + m + 1
    · nlinarith
    · push Not at hx'
      have hc2 : c ≤ 1 / 2 := by
        rw [hc, div_le_iff₀ hden]; nlinarith
      nlinarith

lemma ne_zero_of_lower {c x : ℝ} {z : ℂ} (hc : 0 < c) (hx : 0 ≤ x) (h : c * (1 + x) ≤ ‖z‖) :
    z ≠ 0 := by
  intro hz; rw [hz, norm_zero] at h; nlinarith

lemma measurable_integrand (w a : ℂ) : Measurable (integrand w a) := by
  unfold integrand; fun_prop

/-- The `a`-derivative of the integrand. -/
def integrand' (w a : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (1 - w) * (-2 * (((x : ℂ) + a) ^ 3)⁻¹)

lemma measurable_integrand' (w a : ℂ) : Measurable (integrand' w a) := by
  unfold integrand'; fun_prop

lemma norm_integrand_one {w : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖integrand w 1 x‖ = x ^ (1 - w.re) / (1 + x) ^ 2 := by
  have : ((x : ℂ) + 1) = ((x + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [integrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, this, norm_inv, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  simp [div_eq_mul_inv, add_comm]

/-- The integral `∫_0^∞ x^{1-w}(x + a)^{-2} dx` is holomorphic in `a` on the slit plane. -/
theorem differentiableOn_integral {w : ℂ} (h0 : 0 < w.re) (h2 : w.re < 2) :
    DifferentiableOn ℂ (fun a => ∫ x in Ioi (0 : ℝ), integrand w a x) slitPlane := by
  intro a₀ ha₀
  obtain ⟨ε, hε, c, hc, hlow⟩ := lower_bound ha₀
  have hint1 := (integral_pos one_pos h0 h2).1
  have hint1' : Integrable (fun x => ‖integrand w ((1 : ℝ) : ℂ) x‖) (volume.restrict (Ioi 0)) :=
    hint1.norm
  simp only [Complex.ofReal_one] at hint1'
  set σ := w.re
  -- bounds
  have hbound : ∀ a ∈ Metric.ball a₀ ε, ∀ x : ℝ, 0 < x →
      ‖integrand w a x‖ ≤ (c ^ 2)⁻¹ * ‖integrand w 1 x‖ ∧
      ‖integrand' w a x‖ ≤ 2 * (c ^ 3)⁻¹ * ‖integrand w 1 x‖ := by
    intro a ha x hx
    have hl := hlow a ha x hx.le
    have hpos : 0 < c * (1 + x) := by positivity
    have hz : 0 < ‖(x : ℂ) + a‖ := lt_of_lt_of_le hpos hl
    rw [norm_integrand_one hx]
    have hxp : 0 ≤ x ^ (1 - σ) := Real.rpow_nonneg hx.le _
    have h1x : 1 ≤ 1 + x := by linarith
    constructor
    · rw [integrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, norm_inv, norm_pow,
        Complex.sub_re, Complex.one_re]
      have : ((‖(x : ℂ) + a‖) ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ * ((1 + x) ^ 2)⁻¹ := by
        rw [← mul_inv, ← mul_pow]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hl 2)
      calc x ^ (1 - σ) * ((‖(x : ℂ) + a‖) ^ 2)⁻¹ ≤ x ^ (1 - σ) * ((c ^ 2)⁻¹ * ((1 + x) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left this hxp
        _ = (c ^ 2)⁻¹ * (x ^ (1 - σ) / (1 + x) ^ 2) := by ring
    · rw [integrand', norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, norm_mul, norm_neg,
        norm_inv, norm_pow, Complex.sub_re, Complex.one_re]
      have h2n : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2n]
      have : ((‖(x : ℂ) + a‖) ^ 3)⁻¹ ≤ (c ^ 3)⁻¹ * ((1 + x) ^ 2)⁻¹ := by
        have e1 : ((‖(x : ℂ) + a‖) ^ 3)⁻¹ ≤ ((c * (1 + x)) ^ 3)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hl 3)
        have e2 : ((c * (1 + x)) ^ 3)⁻¹ ≤ (c ^ 3)⁻¹ * ((1 + x) ^ 2)⁻¹ := by
          rw [mul_pow, mul_inv]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1x (by norm_num))
        exact e1.trans e2
      calc x ^ (1 - σ) * (2 * ((‖(x : ℂ) + a‖) ^ 3)⁻¹)
          ≤ x ^ (1 - σ) * (2 * ((c ^ 3)⁻¹ * ((1 + x) ^ 2)⁻¹)) := by gcongr
        _ = 2 * (c ^ 3)⁻¹ * (x ^ (1 - σ) / (1 + x) ^ 2) := by ring
  have hball : Metric.ball a₀ ε ∈ 𝓝 a₀ := Metric.ball_mem_nhds _ hε
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun a x => integrand w a x) (F' := fun a x => integrand' w a x)
    (bound := fun x => 2 * (c ^ 3)⁻¹ * ‖integrand w 1 x‖) hball
    (Eventually.of_forall fun a => (measurable_integrand w a).aestronglyMeasurable)
    (Integrable.mono' (hint1'.const_mul (c ^ 2)⁻¹)
      (measurable_integrand w a₀).aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
        (hbound a₀ (Metric.mem_ball_self hε) x hx).1))
    (measurable_integrand' w a₀).aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioi).mono fun x hx a ha => (hbound a ha x hx).2)
    (hint1'.const_mul _)
    ((ae_restrict_mem measurableSet_Ioi).mono fun x hx a ha => by
      have hne : (x : ℂ) + a ≠ 0 := ne_zero_of_lower hc (le_of_lt hx) (hlow a ha x (le_of_lt hx))
      have hd : HasDerivAt (fun b : ℂ => ((x : ℂ) + b) ^ 2) (2 * ((x : ℂ) + a)) a := by
        have h := (hasDerivAt_pow 2 ((x : ℂ) + a)).comp a ((hasDerivAt_id a).const_add (x : ℂ))
        convert h using 1
        · rfl
        · rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_one]
          norm_cast
      have hd2 := (hd.inv (pow_ne_zero 2 hne)).const_mul ((x : ℂ) ^ (1 - w))
      refine hd2.congr_deriv ?_
      simp only [integrand']
      field_simp)
  exact key.2.differentiableAt.differentiableWithinAt

/-- **`prop:beta`, the integral identity.** For `a ∈ ℂ ∖ (-∞, 0]` and `0 < Re w < 2`, with the
principal power, `a^{-w} = P(w) ∫_0^∞ x^{1-w}(x + a)^{-2} dx`. -/
theorem beta_identity {a w : ℂ} (ha : a ∈ slitPlane) (h0 : 0 < w.re) (h2 : w.re < 2) :
    a ^ (-w) = BetaP.P w * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (1 - w) * (((x : ℂ) + a) ^ 2)⁻¹ := by
  have hf : AnalyticOnNhd ℂ (fun a : ℂ => a ^ (-w)) slitPlane :=
    DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_id.cpow_const hz).differentiableWithinAt)
      isOpen_slitPlane
  have hg : AnalyticOnNhd ℂ (fun a => BetaP.P w * ∫ x in Ioi (0 : ℝ), integrand w a x) slitPlane :=
    ((differentiableOn_integral h0 h2).const_mul _).analyticOnNhd isOpen_slitPlane
  have hpre : IsPreconnected slitPlane :=
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  have hT : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := {(1 : ℝ)}ᶜ))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using hr
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), z ^ (-w) = BetaP.P w * ∫ x in Ioi (0 : ℝ), integrand w z x := by
    refine hT.frequently (Eventually.frequently ?_)
    have : ∀ᶠ r : ℝ in 𝓝[≠] 1, 0 < r :=
      nhdsWithin_le_nhds (Ioi_mem_nhds one_pos)
    filter_upwards [this] with r hr
    rw [(integral_pos hr h0 h2).2, ← mul_assoc, ← mul_assoc, mul_assoc (BetaP.P w), P_mul_Gamma h0 h2,
      one_mul]
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hpre one_mem_slitPlane hfreq ha

/-- `exp(cw) = 1 + cw + c²w²/2 + O(w³)` as `w → 0`. -/
lemma exp_mul_isBigO (c : ℂ) :
    (fun w : ℂ => Complex.exp (c * w) - (1 + c * w + c ^ 2 * w ^ 2 / 2)) =O[𝓝 0] (fun w => w ^ 3) := by
  have h := (Complex.exp_sub_sum_range_isBigO_pow 3).comp_tendsto
    (show Tendsto (fun w : ℂ => c * w) (𝓝 0) (𝓝 0) by
      have := (tendsto_const_nhds (x := c)).mul (tendsto_id (x := 𝓝 (0 : ℂ)))
      simpa using this)
  have h2 : (fun w : ℂ => (c * w) ^ 3) =O[𝓝 0] (fun w => w ^ 3) := by
    have := (isBigO_refl (fun w : ℂ => w ^ 3) (𝓝 0)).const_mul_left (c ^ 3)
    simpa [mul_pow] using this
  refine (h.trans h2).congr_left (fun w => ?_)
  simp [Finset.sum_range_succ, Function.comp, Nat.factorial]
  ring

/-- **`prop:beta`, the expansion.** `(2π)^w P(w) = w + (1 + log 2π)w² + O(w³)` at `w = 0`. -/
theorem expansion :
    (fun w : ℂ => (2 * Real.pi : ℂ) ^ w * BetaP.P w - (w + (1 + Real.log (2 * Real.pi)) * w ^ 2))
      =O[𝓝 0] (fun w => w ^ 3) := by
  set L : ℂ := (Real.log (2 * Real.pi) : ℂ) with hL
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hπ
  have hlog : Complex.log (2 * Real.pi : ℂ) = L := by
    rw [hL, Complex.ofReal_log (by positivity)]; push_cast; rfl
  -- the numerator
  set N : ℂ → ℂ := fun w => (I / 2) * ((Complex.exp ((L - Real.pi * I) * w) -
      (1 + (L - Real.pi * I) * w + (L - Real.pi * I) ^ 2 * w ^ 2 / 2)) -
      (Complex.exp ((L + Real.pi * I) * w) -
      (1 + (L + Real.pi * I) * w + (L + Real.pi * I) ^ 2 * w ^ 2 / 2))) +
      (Real.pi * (1 + L)) * w ^ 3 with hN
  have hNO : N =O[𝓝 0] (fun w => w ^ 3) :=
    (((exp_mul_isBigO (L - Real.pi * I)).sub (exp_mul_isBigO (L + Real.pi * I))).const_mul_left (I / 2)).add
      ((isBigO_refl (fun w : ℂ => w ^ 3) (𝓝 0)).const_mul_left _)
  have hinv : (fun w : ℂ => ((Real.pi : ℂ) * (1 - w))⁻¹) =O[𝓝 0] (fun _ => (1 : ℂ)) := by
    have hc : ContinuousAt (fun w : ℂ => ((Real.pi : ℂ) * (1 - w))⁻¹) 0 :=
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).inv₀ (by simp [hπ])
    exact hc.tendsto.isBigO_one ℂ
  have hprod := hNO.mul hinv
  simp only [mul_one] at hprod
  refine hprod.congr' ?_ (Eventually.of_forall fun _ => rfl)
  have hne : ∀ᶠ w : ℂ in 𝓝 0, w ≠ 1 := isOpen_ne.mem_nhds (by norm_num)
  filter_upwards [hne] with w hw
  have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  have hsin : Complex.exp (L * w) * Complex.sin (Real.pi * w) =
      (Complex.exp ((L - Real.pi * I) * w) - Complex.exp ((L + Real.pi * I) * w)) * I / 2 := by
    have h := Complex.two_sin (x := (Real.pi : ℂ) * w)
    have ea : Complex.exp (L * w) * Complex.exp (-(Real.pi * w) * I) = Complex.exp ((L - Real.pi * I) * w) := by
      rw [← Complex.exp_add]; congr 1; ring
    have eb : Complex.exp (L * w) * Complex.exp ((Real.pi * w) * I) = Complex.exp ((L + Real.pi * I) * w) := by
      rw [← Complex.exp_add]; congr 1; ring
    linear_combination (Complex.exp (L * w) / 2) * h + (I / 2) * ea - (I / 2) * eb
  have hcpow : (2 * Real.pi : ℂ) ^ w = Complex.exp (L * w) := by
    rw [Complex.cpow_def_of_ne_zero h2π, hlog]
  have hD : (Real.pi : ℂ) * (1 - w) * ((Real.pi : ℂ) * (1 - w))⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero hπ h1)
  rw [BetaP.P_eq hw, hcpow, hN]
  linear_combination (-((Real.pi : ℂ) * (1 - w))⁻¹) * hsin +
    (((Real.pi : ℂ) * (1 - w))⁻¹ * (Real.pi * w + Real.pi * L * w ^ 2)) * Complex.I_sq -
    (w + (1 + L) * w ^ 2) * hD

end

end BetaIntegral

end WeilRH
