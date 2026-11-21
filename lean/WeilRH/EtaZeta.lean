/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib
import WeilRH.XiHalf

/-!
# `ζ(σ) < 0` on `(0, 1)` via the Dirichlet eta function (round 73, `prop:F0`)

The manuscript's `prop:F0` (step (a) of its proof) uses `ζ(1/2) < 0`. We prove `ζ(σ) < 0` for every
`σ ∈ (0, 1)` by the classical route through the alternating zeta function, written with paired terms
so that it converges absolutely on `Re s > 0`:

`η(s) = ∑_{k ≥ 0} ((2k+1)^{-s} - (2k+2)^{-s})`.

* `etaPair` is holomorphic on `Re s > 0` (locally uniform bound `|s| (2k+1)^{-σ-1}`, by the mean
  value inequality);
* on `Re s > 1`, `etaPair s = (1 - 2^{1-s}) ζ(s)` (split `∑ n^{-s}` into odd and even `n`);
* by the identity theorem on the convex open set `{0 < Re s, Re s - 1 < Im s}` (which avoids `s = 1`)
  the identity holds on `(0, 1)`;
* there each paired term is a positive real, so `η(σ) > 0`, while `1 - 2^{1-σ} < 0`.

This closes obligation 24: `prop:F0` is now unconditional (`F_zero_pos`).
-/

open Complex Set Filter Topology

namespace WeilRH

namespace EtaZeta

/-- The `k`-th paired term `(2k+1)^{-s} - (2k+2)^{-s}` of the alternating zeta function. -/
noncomputable def term (k : ℕ) (s : ℂ) : ℂ :=
  ((2 * k + 1 : ℝ) : ℂ) ^ (-s) - ((2 * k + 2 : ℝ) : ℂ) ^ (-s)

/-- The alternating zeta function, as a series of paired terms. -/
noncomputable def eta (s : ℂ) : ℂ := ∑' k : ℕ, term k s

lemma two_k_add_one_pos (k : ℕ) : (0 : ℝ) < 2 * k + 1 := by positivity

/-- Mean-value bound: `‖term k s‖ ≤ ‖s‖ (2k+1)^{-(Re s + 1)}`. -/
lemma norm_term_le (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖term k s‖ ≤ ‖s‖ * (2 * k + 1 : ℝ) ^ (-(s.re + 1)) := by
  set a : ℝ := 2 * k + 1
  have ha : 0 < a := two_k_add_one_pos k
  have ha1 : 1 ≤ a := by simp [a]
  have hs0 : -s ≠ 0 := neg_ne_zero.2 (fun h => by simp [h] at hs)
  let f : ℝ → ℂ := fun y => (y : ℂ) ^ (-s)
  have hderiv : ∀ y ∈ Icc a (a + 1),
      HasDerivWithinAt f (-s * (y : ℂ) ^ (-s - 1)) (Icc a (a + 1)) y := by
    intro y hy
    have hy0 : y ≠ 0 := (ha.trans_le hy.1).ne'
    exact (hasDerivAt_ofReal_cpow_const hy0 hs0).hasDerivWithinAt
  have hbound : ∀ y ∈ Ico a (a + 1),
      ‖-s * (y : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-(s.re + 1)) := by
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hy0]
    gcongr
    simp only [sub_re, neg_re, one_re]
    rw [show -s.re - 1 = -(s.re + 1) by ring]
    exact Real.rpow_le_rpow_of_nonpos ha hy.1 (by linarith)
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (a + 1)
    ⟨by linarith, le_rfl⟩
  have e2 : (2 * (k : ℝ) + 2) = a + 1 := by simp [a]; ring
  have hterm : term k s = -(f (a + 1) - f a) := by
    simp only [term, f, a, neg_sub]
    rw [show (2 * (k : ℝ) + 2) = 2 * k + 1 + 1 by ring]
  calc ‖term k s‖ = ‖f (a + 1) - f a‖ := by rw [hterm, norm_neg]
    _ ≤ ‖s‖ * a ^ (-(s.re + 1)) * (a + 1 - a) := key
    _ = ‖s‖ * a ^ (-(s.re + 1)) := by ring

lemma summable_rpow_two_k_add_one {r : ℝ} (hr : 1 < r) :
    Summable (fun k : ℕ => (2 * k + 1 : ℝ) ^ (-r)) := by
  have hsum : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-r)) := by
    have := (Real.summable_nat_rpow (p := -r)).2 (by linarith)
    exact (summable_nat_add_iff 1).2 this |>.congr (fun k => by push_cast; ring_nf)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsum
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
    (by linarith)

lemma summable_norm_term {s : ℂ} (hs : 0 < s.re) : Summable (fun k => ‖term k s‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_term_le k hs)
    ((summable_rpow_two_k_add_one (by linarith)).mul_left _)

/-- The alternating zeta function is holomorphic on `Re s > 0`. -/
theorem differentiableOn_eta : DifferentiableOn ℂ eta {s | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  set δ := s₀.re / 2
  set R := ‖s₀‖ + 1
  have hδ : 0 < δ := by simp only [δ]; linarith
  set V : Set ℂ := {s | δ < s.re} ∩ Metric.ball 0 R
  have hV : IsOpen V :=
    (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball
  have hs₀V : s₀ ∈ V := ⟨by show δ < s₀.re; simp only [δ]; linarith,
    by simp [R]⟩
  have hdiff : DifferentiableOn ℂ eta V := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_rpow_two_k_add_one (r := δ + 1) (by linarith)).mul_left R) (fun k => ?_) hV
      (fun k s hs => ?_)
    · intro s hs
      have h1 : (((2 * k + 1 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (two_k_add_one_pos k).ne'
      have h2 : (((2 * k + 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 2 * k + 2).ne'
      exact ((differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
        (differentiableAt_id.neg.const_cpow (Or.inl h2))).differentiableWithinAt
    · have hre : δ < s.re := hs.1
      have hnorm : ‖s‖ < R := by simpa using hs.2
      refine (norm_term_le k (by linarith)).trans ?_
      gcongr
      all_goals linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  exact (hdiff s₀ hs₀V).differentiableAt (hV.mem_nhds hs₀V) |>.differentiableWithinAt

/-- On `Re s > 1`, `η(s) = (1 - 2^{1-s}) ζ(s)`. -/
theorem eta_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    eta s = (1 - 2 ^ (1 - s)) * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have := (Complex.summable_one_div_nat_cpow (p := s)).2 hs
    exact (summable_nat_add_iff 1).2 this |>.congr (fun n => by push_cast; rfl)
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hsplit := tsum_even_add_odd (f := fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s)
    (hsum.comp_injective (mul_right_injective₀ two_ne_zero))
    (hsum.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ two_ne_zero)))
  -- odd part `A = ∑ (2k+1)^{-s}`, even part `B = ∑ (2k+2)^{-s} = 2^{-s} ζ(s)`
  have hodd : ∀ k : ℕ, 1 / (((2 * k : ℕ) : ℂ) + 1) ^ s = ((2 * k + 1 : ℝ) : ℂ) ^ (-s) := by
    intro k; rw [cpow_neg, one_div]; push_cast; ring_nf
  have heven : ∀ k : ℕ, 1 / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s = ((2 * k + 2 : ℝ) : ℂ) ^ (-s) := by
    intro k; rw [cpow_neg, one_div]; push_cast; ring_nf
  have hB : ∑' k : ℕ, ((2 * k + 2 : ℝ) : ℂ) ^ (-s) = 2 ^ (-s) * riemannZeta s := by
    rw [hz, ← tsum_mul_left]
    congr 1; ext k
    have : ((2 * k + 2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, mul_cpow_ofReal_nonneg (by norm_num) (by positivity), cpow_neg, cpow_neg]
    push_cast; rw [one_div, cpow_neg]
  simp only [hodd, heven] at hsplit
  have hA := hsplit
  have hsA : Summable (fun k : ℕ => ((2 * k + 1 : ℝ) : ℂ) ^ (-s)) :=
    (hsum.comp_injective (mul_right_injective₀ two_ne_zero)).congr (fun k => hodd k)
  have hsB : Summable (fun k : ℕ => ((2 * k + 2 : ℝ) : ℂ) ^ (-s)) :=
    (hsum.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ two_ne_zero))).congr
      (fun k => heven k)
  unfold eta term
  rw [hsA.tsum_sub hsB, hB]
  have hA' : ∑' k : ℕ, ((2 * k + 1 : ℝ) : ℂ) ^ (-s) = riemannZeta s - 2 ^ (-s) * riemannZeta s := by
    have h' := hA
    rw [← hz] at h'
    rw [← hB, ← h']; ring
  rw [hA', show (2 : ℂ) ^ (1 - s) = 2 * 2 ^ (-s) by
    rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one]]
  ring

/-- The convex open region `{0 < Re s, Re s - 1 < Im s}`: it contains `(0, 1)` and `2 + 2i`, and
not `1`. -/
def region : Set ℂ := {s | 0 < s.re} ∩ {s | s.re - s.im < 1}

lemma isOpen_region : IsOpen region :=
  (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt (continuous_re.sub continuous_im) continuous_const)

lemma isPreconnected_region : IsPreconnected region := by
  have hlin : IsLinearMap ℝ (fun s : ℂ => s.re - s.im) :=
    ⟨fun x y => by simp; ring, fun c x => by simp; ring⟩
  have hre : IsLinearMap ℝ (fun s : ℂ => s.re) := ⟨fun x y => by simp, fun c x => by simp⟩
  exact ((convex_halfSpace_gt hre 0).inter (convex_halfSpace_lt hlin 1)).isPreconnected

lemma one_notMem_region : (1 : ℂ) ∉ region := by simp [region]

/-- The identity `η(s) = (1 - 2^{1-s}) ζ(s)` on the whole region, in particular on `(0, 1)`. -/
theorem eta_eq_on_region : EqOn eta (fun s => (1 - 2 ^ (1 - s)) * riemannZeta s) region := by
  have hf : AnalyticOnNhd ℂ eta region :=
    (differentiableOn_eta.mono (fun s hs => hs.1)).analyticOnNhd isOpen_region
  have hg : AnalyticOnNhd ℂ (fun s => (1 - 2 ^ (1 - s)) * riemannZeta s) region := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_region
    have hs1 : s ≠ 1 := fun h => one_notMem_region (h ▸ hs)
    exact ((differentiableAt_const _).sub
      ((differentiableAt_const _).sub differentiableAt_id |>.const_cpow (Or.inl two_ne_zero))).mul
      (differentiableAt_riemannZeta hs1) |>.differentiableWithinAt
  have h₀ : (2 + 2 * I : ℂ) ∈ region := by simp [region]
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_region h₀ ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 + 2 * I : ℂ).re)] with s hs
  exact eta_eq_of_one_lt hs

/-- On `(0, 1)`, `η(σ)` is a positive real number. -/
theorem eta_ofReal_pos {σ : ℝ} (hσ : 0 < σ) :
    ∃ r : ℝ, 0 < r ∧ eta σ = r := by
  let t : ℕ → ℝ := fun k => (2 * k + 1 : ℝ) ^ (-σ) - (2 * k + 2 : ℝ) ^ (-σ)
  have ht : ∀ k, term k σ = (t k : ℂ) := by
    intro k
    simp only [term, t, ofReal_sub]
    rw [ofReal_cpow (by positivity), ofReal_cpow (by positivity)]
    push_cast; rfl
  have htpos : ∀ k, 0 < t k := by
    intro k
    simp only [t, sub_pos]
    exact Real.rpow_lt_rpow_of_neg (two_k_add_one_pos k) (by linarith) (by linarith)
  have hts : Summable t :=
    Summable.of_norm_bounded (summable_norm_term (s := (σ : ℂ)) (by simpa using hσ))
      (fun k => le_of_eq (by rw [ht k, Complex.norm_real]))
  refine ⟨∑' k, t k, hts.tsum_pos (fun k => (htpos k).le) 0 (htpos 0), ?_⟩
  unfold eta
  simp_rw [ht]
  exact (ofReal_tsum t).symm

/-- **`ζ(σ) < 0` for `0 < σ < 1`.** `ζ(σ)` is real and negative. -/
theorem riemannZeta_neg_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ r : ℝ, r < 0 ∧ riemannZeta σ = r := by
  obtain ⟨e, he, hee⟩ := eta_ofReal_pos h0
  have hmem : (σ : ℂ) ∈ region := by simp [region, h0, h1]
  have hid := eta_eq_on_region hmem
  simp only at hid
  set c : ℝ := 1 - (2 : ℝ) ^ (1 - σ)
  have hc : c < 0 := by
    simp only [c, sub_neg]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  have hcC : (1 - 2 ^ (1 - (σ : ℂ))) = (c : ℂ) := by
    simp only [c, ofReal_sub, ofReal_one]
    rw [ofReal_cpow (by norm_num)]; push_cast; rfl
  rw [hcC, hee] at hid
  refine ⟨e / c, div_neg_of_pos_of_neg he hc, ?_⟩
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne
  rw [ofReal_div, hid, mul_div_cancel_left₀ _ hc0]

/-- `ζ(1/2) < 0`, in the form used by `F_zero_pos_of_zeta_half_neg`. -/
theorem riemannZeta_half_re_neg : (riemannZeta (1 / 2)).re < 0 := by
  obtain ⟨r, hr, h⟩ := riemannZeta_neg_of_mem_Ioo (σ := 1 / 2) (by norm_num) (by norm_num)
  have : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; rfl
  rw [this] at h
  rw [h, ofReal_re]; exact hr

end EtaZeta

/-- **`prop:F0`, unconditional.** `F(0) = ξ(1/2)` is real and positive. -/
theorem F_zero_pos :
    riemannXiUpper 0 = completedXi (1 / 2) ∧ (completedXi (1 / 2)).im = 0 ∧
      0 < (completedXi (1 / 2)).re :=
  F_zero_pos_of_zeta_half_neg EtaZeta.riemannZeta_half_re_neg

end WeilRH
