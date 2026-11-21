import Mathlib
import WeilRH.BlackBoxes2
import WeilRH.XiKPrimeSum

/-!
# `prop:xiK-asymp`: the expansion of the standard branch of `log ξ_K`

`notes.tex`, `def:deninger-gamma` (d)–(e) and `prop:xiK-asymp`. For a number field `K` with `r₁`
real and `r₂` complex places, degree `n` and discriminant `D_K`, the Stirling constants are
`A = n/2`, `B = ½ log|D_K| − (n/2)(1 + log 2π)`, `C = 2 − (r₁ + r₂)/2`,
`E = (r₁/2) log 4π + (r₂/2) log 8π`, and the standard branch of `log ξ_K` on `Re z > 1` is
`f(z) = log z + log(z − 1) + (z/2) log|D_K| + r₁(−(z/2) log π + log Γ(z/2))
  + r₂(log 2 − z log 2π + log Γ(z)) + ∑_𝔭 ∑_k N𝔭^{-kz}/k`.

Here `log Γ` is the holomorphic logarithm `L` of B4' (`LogGammaStirling`), with `exp ∘ L = Γ` and
`L 2 = 0`; `logGamma_eq_real` shows it is the branch that is real on `(0, ∞)`, as the manuscript
requires.

* `stdBranch_sub_main`: the exact identity `f − (Az log z + Bz + C log z + E) =
  (log(z − 1) − log z) + r₁ R(z/2) + r₂ R(z) + P(z)`, with `R` the Stirling remainder of `L`.
* `stdBranch_asymp` (**`prop:xiK-asymp`, first expansion**): for every `s ∈ ℂ`, along
  `z = s + x`, `x → +∞`, `f(z) = Az log z + Bz + C log z + E + O(|z|^{-1})`, conditional on B4'.

The expansions of `f'` and `G_ξ = −f''` are not formalized here (obligation 39).
-/

namespace WeilRH.XiKAsymp

open Complex NumberField Filter Asymptotics
open scoped Topology

variable (K : Type) [Field K] [NumberField K]

/-- `r₁`, `r₂`, `n` as reals. -/
noncomputable abbrev r₁ : ℝ := InfinitePlace.nrRealPlaces K
noncomputable abbrev r₂ : ℝ := InfinitePlace.nrComplexPlaces K
noncomputable abbrev n : ℝ := Module.finrank ℚ K

/-- The Stirling constants of `K` (`def:deninger-gamma` (d)). -/
noncomputable def A : ℝ := n K / 2
noncomputable def B : ℝ := Real.log |(discr K : ℝ)| / 2 - n K / 2 * (1 + Real.log (2 * Real.pi))
noncomputable def C : ℝ := 2 - (r₁ K + r₂ K) / 2
noncomputable def E : ℝ :=
  r₁ K / 2 * Real.log (4 * Real.pi) + r₂ K / 2 * Real.log (8 * Real.pi)

/-- The standard branch of `log ξ_K` (`def:deninger-gamma` (e)), with `log Γ = L`. -/
noncomputable def stdBranch (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  log z + log (z - 1) + z / 2 * (Real.log |(discr K : ℝ)| : ℂ)
    + (r₁ K : ℂ) * (-(z / 2) * (Real.log Real.pi : ℂ) + L (z / 2))
    + (r₂ K : ℂ) * ((Real.log 2 : ℂ) - z * (Real.log (2 * Real.pi) : ℂ) + L z)
    + XiKPrimeSum.primeSum K z

/-- The main term `A z log z + B z + C log z + E`. -/
noncomputable def main (z : ℂ) : ℂ :=
  (A K : ℂ) * z * log z + (B K : ℂ) * z + (C K : ℂ) * log z + (E K : ℂ)

/-- Stirling's main term `(w − ½) log w − w + ½ log 2π`. -/
noncomputable def stirling (w : ℂ) : ℂ :=
  (w - 1 / 2) * log w - w + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)

/-- `n = r₁ + 2 r₂`. -/
theorem n_eq : n K = r₁ K + 2 * r₂ K := by
  have := InfinitePlace.card_add_two_mul_card_eq_rank K
  simp only [n, r₁, r₂]
  exact_mod_cast this.symm

/-- B4''s `L` is the branch of `log Γ` that is real on `(0, ∞)` (`def:deninger-gamma` (e)):
`L x = log Γ(x)` for `x > 0`. -/
theorem logGamma_eq_real {L : ℂ → ℂ} (hLd : DifferentiableOn ℂ L slitPlane)
    (hLe : Set.EqOn (Complex.exp ∘ L) Complex.Gamma slitPlane) (hL2 : L 2 = 0) {x : ℝ} (hx : 0 < x) :
    L x = (Real.log (Real.Gamma x) : ℂ) := by
  have hmem : ∀ t : ℝ, 0 < t → (t : ℂ) ∈ slitPlane := fun t ht => ofReal_mem_slitPlane.mpr ht
  -- `L t = log Γ(t) + 2πik`
  have hform : ∀ t : ℝ, 0 < t → ∃ k : ℤ, L t = (Real.log (Real.Gamma t) : ℂ) + k * (2 * Real.pi * I) := by
    intro t ht
    have he := hLe (hmem t ht)
    simp only [Function.comp_apply] at he
    have hGpos : 0 < Real.Gamma t := Real.Gamma_pos_of_pos ht
    have : Complex.exp (L t - (Real.log (Real.Gamma t) : ℂ)) = 1 := by
      rw [Complex.exp_sub, he, Complex.Gamma_ofReal, ← Complex.ofReal_exp, Real.exp_log hGpos,
        div_self]
      exact_mod_cast hGpos.ne'
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp this
    exact ⟨k, by rw [← hk]; ring⟩
  set f : ℝ → ℝ := fun t => (L t).im / (2 * Real.pi) with hf
  have hmaps : Set.MapsTo f (Set.Ioi 0) (Set.range ((↑) : ℤ → ℝ)) := by
    intro t ht
    obtain ⟨k, hk⟩ := hform t ht
    refine ⟨k, ?_⟩
    simp only [hf, hk, add_im, ofReal_im, zero_add, mul_im, intCast_re, intCast_im, zero_mul,
      add_zero]
    simp only [mul_re, ofReal_re, re_ofNat, I_re, mul_zero, ofReal_im, im_ofNat, I_im, mul_one,
      sub_zero, zero_mul, mul_im, re_ofNat, ofReal_re]
    field_simp
    ring
  have hcont : ContinuousOn f (Set.Ioi 0) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div_const
    exact continuous_im.continuousAt.comp
      (((hLd.differentiableAt (isOpen_slitPlane.mem_nhds (hmem t ht))).continuousAt).comp
        continuous_ofReal.continuousAt)
  have hdisc : IsDiscrete (Set.range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  have hc := isPreconnected_Ioi.constant_of_mapsTo hdisc hcont hmaps hx (show (2:ℝ) ∈ Set.Ioi 0 by norm_num)
  have h2 : f 2 = 0 := by simp [hf, hL2]
  rw [h2, hf] at hc
  simp only at hc
  have him : (L x).im = 0 := by
    rcases div_eq_zero_iff.mp hc with h | h
    · exact h
    · exfalso; linarith [Real.pi_pos]
  obtain ⟨k, hk⟩ := hform x hx
  have hk0 : (k : ℝ) = 0 := by
    have := congrArg Complex.im hk
    simp at this
    rw [him] at this
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    nlinarith [this, Real.pi_pos]
  rw [hk]
  simp [show (k : ℂ) = 0 by exact_mod_cast hk0]

/-- **The exact decomposition.** For `z ≠ 0`, `f − main = (log(z − 1) − log z) + r₁ R(z/2) +
r₂ R(z) + P(z)`, where `R = L − stirling`. -/
theorem stdBranch_sub_main (L : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    stdBranch K L z - main K z =
      (log (z - 1) - log z) + (r₁ K : ℂ) * (L (z / 2) - stirling (z / 2))
        + (r₂ K : ℂ) * (L z - stirling z) + XiKPrimeSum.primeSum K z := by
  have hlog2 : log (z / 2) = log z - (Real.log 2 : ℂ) := by
    have : z / 2 = z * ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, log_mul_ofReal _ (by norm_num) _ hz, Real.log_div one_ne_zero two_ne_zero,
      Real.log_one]
    push_cast; ring
  have hpi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul two_ne_zero Real.pi_ne_zero
  have h4 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]; push_cast; ring
  have h8 : Real.log (8 * Real.pi) = 3 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow]; push_cast; ring
  have hn := n_eq K
  simp only [stdBranch, main, stirling, A, B, C, E, hlog2]
  rw [hpi, h4, h8, hn]
  push_cast
  ring

/-- Points `z = s + x` with `x` large. -/
theorem eventually_large (s : ℂ) (M : ℝ) :
    ∀ᶠ x : ℝ in atTop, M ≤ (s + x).re ∧ M ≤ ‖s + x‖ ∧ ‖s + x‖ ≤ 2 * x ∧ 1 ≤ x := by
  have h1 : ∀ᶠ x : ℝ in atTop, M - s.re ≤ x := eventually_ge_atTop _
  have h2 : ∀ᶠ x : ℝ in atTop, M + ‖s‖ ≤ x := eventually_ge_atTop _
  have h3 : ∀ᶠ x : ℝ in atTop, ‖s‖ ≤ x := eventually_ge_atTop _
  have h4 : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ x := eventually_ge_atTop _
  filter_upwards [h1, h2, h3, h4] with x h1 h2 h3 h4
  have hre : (s + x).re = s.re + x := by simp
  refine ⟨by rw [hre]; linarith, ?_, ?_, h4⟩
  · have : ‖(x : ℂ)‖ - ‖s‖ ≤ ‖s + x‖ := by
      have := norm_sub_norm_le (x : ℂ) (-s)
      simpa [sub_neg_eq_add, add_comm] using this
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] at this
    linarith
  · calc ‖s + x‖ ≤ ‖s‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ = ‖s‖ + x := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      _ ≤ 2 * x := by linarith

/-- `log(z − 1) − log z = O(1/|z|)` along `z = s + x`. -/
theorem log_sub_isBigO (s : ℂ) :
    (fun x : ℝ => log (s + x - 1) - log (s + x)) =O[atTop] (fun x : ℝ => ‖s + x‖⁻¹) := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_large s 2] with x hxx
  obtain ⟨hre, hnorm, _, _⟩ := hxx
  set z : ℂ := s + x with hzdef
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; linarith
  have hw : ‖-z⁻¹‖ ≤ 1 / 2 := by
    rw [norm_neg, norm_inv]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hz1 : z - 1 = z * (1 + -z⁻¹) := by field_simp; ring
  have hre1 : 0 < (1 + -z⁻¹).re := by
    have : |(-z⁻¹).re| ≤ 1 / 2 := (abs_re_le_norm _).trans hw
    simp only [add_re, one_re]
    linarith [abs_le.mp this]
  have hargz : |z.arg| < Real.pi / 2 := by
    rw [abs_arg_lt_pi_div_two_iff]; left; linarith
  have hargw : |(1 + -z⁻¹).arg| < Real.pi / 2 := by
    rw [abs_arg_lt_pi_div_two_iff]; left; exact hre1
  have hw0 : (1 + -z⁻¹) ≠ 0 := fun h => by rw [h, zero_re] at hre1; exact lt_irrefl _ hre1
  have hlog : log (z - 1) = log z + log (1 + -z⁻¹) := by
    rw [hz1, log_mul hz0 hw0]
    constructor
    · linarith [abs_lt.mp hargz, abs_lt.mp hargw]
    · linarith [abs_lt.mp hargz, abs_lt.mp hargw]
  have hb := norm_log_one_add_le (z := -z⁻¹) (by linarith)
  rw [hlog, add_sub_cancel_left]
  have hzn : ‖-z⁻¹‖ = ‖z‖⁻¹ := by rw [norm_neg, norm_inv]
  rw [hzn] at hb hw
  have hpos : 0 < ‖z‖⁻¹ := inv_pos.mpr (by linarith)
  set t : ℝ := ‖z‖⁻¹ with ht
  have h1 : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h2 : t ^ 2 ≤ t * (1 / 2) := by nlinarith
  have h3 : t ^ 2 * (1 - t)⁻¹ ≤ t * (1 / 2) * 2 :=
    mul_le_mul h2 h1 (inv_nonneg.mpr (by linarith)) (by positivity)
  rw [norm_inv, norm_norm, ← ht]
  linarith

/-- The Stirling remainder is `O(1/|w|)` on `Re w ≥ 0`, from B4'. -/
theorem remainder_bound {L : ℂ → ℂ}
    (hL : ∀ δ : ℝ, 0 < δ → δ < Real.pi → ∃ C : ℝ, ∀ s : ℂ, |s.arg| ≤ Real.pi - δ → s ≠ 0 →
      ‖L s - ((s - 1 / 2) * Complex.log s - s + (Real.log (2 * Real.pi) / 2 : ℝ))‖ ≤ C / ‖s‖) :
    ∃ C : ℝ, ∀ w : ℂ, 0 ≤ w.re → w ≠ 0 → ‖L w - stirling w‖ ≤ C / ‖w‖ := by
  obtain ⟨C, hC⟩ := hL (Real.pi / 2) (by positivity) (by linarith [Real.pi_pos])
  refine ⟨C, fun w hw hw0 => ?_⟩
  have harg : |w.arg| ≤ Real.pi - Real.pi / 2 := by
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
    exact abs_arg_le_pi_div_two_iff.mpr hw
  have := hC w harg hw0
  simpa [stirling] using this

/-- `2^{2 − Re z} = O(1/|z|)` along `z = s + x`. -/
theorem two_rpow_isBigO (s : ℂ) :
    (fun x : ℝ => (2 : ℝ) ^ (2 - (s + x).re)) =O[atTop] (fun x : ℝ => ‖s + x‖⁻¹) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine IsBigO.of_bound (8 * (2 : ℝ) ^ (-s.re) / Real.log 2) ?_
  filter_upwards [eventually_large s 1] with x hxx
  obtain ⟨_, hnorm, hle, hx1⟩ := hxx
  have hre : (s + x).re = s.re + x := by simp
  rw [hre, norm_inv, norm_norm, Real.norm_of_nonneg (by positivity)]
  have hsplit : (2 : ℝ) ^ (2 - (s.re + x)) = 4 * (2 : ℝ) ^ (-s.re) * ((2 : ℝ) ^ x)⁻¹ := by
    rw [← Real.rpow_neg (by norm_num), show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1; ring
  have hexp : x * Real.log 2 ≤ (2 : ℝ) ^ x := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    linarith [Real.add_one_le_exp (Real.log 2 * x), mul_comm x (Real.log 2)]
  have hxpos : 0 < x := by linarith
  have hzpos : 0 < ‖s + x‖ := by linarith
  rw [hsplit]
  have h2x : ((2 : ℝ) ^ x)⁻¹ ≤ (x * Real.log 2)⁻¹ :=
    inv_anti₀ (by positivity) hexp
  have hxz : (x * Real.log 2)⁻¹ ≤ 2 / (Real.log 2) * ‖s + x‖⁻¹ := by
    rw [mul_inv, div_eq_mul_inv]
    have : x⁻¹ ≤ 2 * ‖s + x‖⁻¹ := by
      rw [inv_le_comm₀ hxpos (by positivity), mul_inv, inv_inv]
      linarith [show (2 : ℝ)⁻¹ * ‖s + x‖ ≤ x by linarith]
    calc x⁻¹ * (Real.log 2)⁻¹ ≤ (2 * ‖s + x‖⁻¹) * (Real.log 2)⁻¹ :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 * (Real.log 2)⁻¹ * ‖s + x‖⁻¹ := by ring
  calc 4 * (2 : ℝ) ^ (-s.re) * ((2 : ℝ) ^ x)⁻¹
      ≤ 4 * (2 : ℝ) ^ (-s.re) * (2 / Real.log 2 * ‖s + x‖⁻¹) :=
        mul_le_mul_of_nonneg_left (h2x.trans hxz) (by positivity)
    _ = 8 * (2 : ℝ) ^ (-s.re) / Real.log 2 * ‖s + x‖⁻¹ := by ring

/-- **`prop:xiK-asymp`, the expansion of `f`.** Conditional on B4' (`LogGammaStirling`): for
every `s ∈ ℂ`, along `z = s + x`, `x → +∞`,
`f(z) = A z log z + B z + C log z + E + O(|z|^{-1})`. -/
theorem stdBranch_asymp (hB : LogGammaStirling) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L slitPlane ∧ Set.EqOn (Complex.exp ∘ L) Complex.Gamma slitPlane ∧
      L 2 = 0 ∧ ∀ s : ℂ,
        (fun x : ℝ => stdBranch K L (s + x) - main K (s + x)) =O[atTop]
          (fun x : ℝ => ‖s + x‖⁻¹) := by
  obtain ⟨L, hLd, hLe, hL2, hLst⟩ := hB
  refine ⟨L, hLd, hLe, hL2, fun s => ?_⟩
  obtain ⟨CR, hCR⟩ := remainder_bound hLst
  -- the four pieces
  have hP1 := log_sub_isBigO s
  have hP2 : (fun x : ℝ => (r₁ K : ℂ) * (L ((s + x) / 2) - stirling ((s + x) / 2))) =O[atTop]
      (fun x : ℝ => ‖s + x‖⁻¹) := by
    refine IsBigO.of_bound (r₁ K * (2 * |CR|)) ?_
    filter_upwards [eventually_large s 1] with x hxx
    obtain ⟨hre, hnorm, _, _⟩ := hxx
    have hw : 0 ≤ ((s + x) / 2).re := by
      have h2 : ((s + x) / 2).re = (s + x).re / 2 := by simp
      rw [h2]; linarith
    have hw0 : (s + x) / 2 ≠ 0 := by
      intro h; rw [div_eq_zero_iff] at h
      rcases h with h | h
      · rw [h, norm_zero] at hnorm; linarith
      · norm_num at h
    have h := hCR _ hw hw0
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_inv, norm_norm]
    have hzz : ‖(s + ↑x) / 2‖ = ‖s + x‖ / 2 := by rw [norm_div]; norm_num
    rw [hzz] at h
    have : CR / (‖s + ↑x‖ / 2) ≤ 2 * |CR| * ‖s + x‖⁻¹ := by
      rw [div_div_eq_mul_div, div_eq_mul_inv]
      nlinarith [le_abs_self CR, inv_pos.mpr (show 0 < ‖s + x‖ by linarith)]
    calc r₁ K * ‖L ((s + ↑x) / 2) - stirling ((s + ↑x) / 2)‖ ≤ r₁ K * (2 * |CR| * ‖s + x‖⁻¹) :=
          mul_le_mul_of_nonneg_left (h.trans this) (by positivity)
      _ = r₁ K * (2 * |CR|) * ‖s + x‖⁻¹ := by ring
  have hP3 : (fun x : ℝ => (r₂ K : ℂ) * (L (s + x) - stirling (s + x))) =O[atTop]
      (fun x : ℝ => ‖s + x‖⁻¹) := by
    refine IsBigO.of_bound (r₂ K * |CR|) ?_
    filter_upwards [eventually_large s 1] with x hxx
    obtain ⟨hre, hnorm, _, _⟩ := hxx
    have hw0 : s + x ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; linarith
    have h := hCR _ (by linarith) hw0
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_inv, norm_norm]
    have : CR / ‖s + ↑x‖ ≤ |CR| * ‖s + x‖⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    calc r₂ K * ‖L (s + ↑x) - stirling (s + ↑x)‖ ≤ r₂ K * (|CR| * ‖s + x‖⁻¹) :=
          mul_le_mul_of_nonneg_left (h.trans this) (by positivity)
      _ = r₂ K * |CR| * ‖s + x‖⁻¹ := by ring
  have hP4 : (fun x : ℝ => XiKPrimeSum.primeSum K (s + x)) =O[atTop] (fun x : ℝ => ‖s + x‖⁻¹) := by
    refine IsBigO.trans ?_ (two_rpow_isBigO s)
    refine IsBigO.of_bound (XiKPrimeSum.S K) ?_
    filter_upwards [eventually_large s 2] with x hxx
    obtain ⟨hre, _, _, _⟩ := hxx
    rw [Real.norm_of_nonneg (by positivity), mul_comm]
    exact XiKPrimeSum.norm_primeSum_le K hre
  have hsum := ((hP1.add hP2).add hP3).add hP4
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_large s 1] with x hxx
  obtain ⟨_, hnorm, _, _⟩ := hxx
  have hz0 : s + x ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; linarith
  rw [stdBranch_sub_main K L hz0]

end WeilRH.XiKAsymp
