/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import WeilRH.R15Tail
import WeilRH.Completed

/-!
# `prop:R15` (ii): the Mellin transform of the periodization is `ξ/4`

`latex/notes.tex`, `def:ccm-kernel` and `prop:R15` (ii). The periodization is
`𝓔k₀(u) = u^{1/2} Σ_{n ≥ 1} k₀(nu)`. For `Re s > 1`, `∫₀^∞ 𝓔k₀(u) u^{s−1/2} du/u` converges
absolutely and equals `ζ(s) M_{k₀}(s) = ξ(s)/4`.

* `R15Periodization.hasMellin_sum`: the Mellin transform of `u ↦ Σ_{n} k₀(nu)` at `s` exists
  (absolutely) and is `ζ(s) M_{k₀}(s)`. Since `𝓔k₀(u) u^{s−1/2} u^{−1} = u^{s−1} Σ k₀(nu)` on `u > 0`,
  this is the manuscript's integral (`integrand_eq`).
* `zeta_mul_M`: `ζ(s) M_{k₀}(s) = ξ(s)/4` for `Re s > 1`, with `ξ = completedXi`.
* `R15_ii`: the manuscript's statement.

The proof is the manuscript's: Mellin transforms scale as `M[f(n·)](s) = n^{−s} M[f](s)`, the
interchange of sum and integral is justified by `Σ_n ∫ |k₀(nu)| u^{σ−1} du = Σ n^{−σ} ∫ |k₀| u^{σ−1}`
with `σ = Re s > 1` (`integral_tsum_of_summable_integral_norm`), and `Σ n^{−s} = ζ(s)`.
-/

open Complex MeasureTheory Set Filter Real Topology

namespace WeilRH
namespace R15Periodization

open R15Mellin R15Tail

/-- `M_{k₀}(s) = (1/8) s (s−1) π^{−s/2} Γ(s/2)` (`prop:R15` (i)). -/
noncomputable def M (s : ℂ) : ℂ := 1 / 8 * s * (s - 1) * (π : ℂ) ^ (-(s / 2)) * Gamma (s / 2)

/-- `def:ccm-kernel`: the periodization `𝓔k₀(u) = u^{1/2} Σ_{n ≥ 1} k₀(nu)` (the `n = 0` term is
`k₀(0) = 0`). -/
noncomputable def Ek0 (u : ℝ) : ℝ := u ^ (1 / 2 : ℝ) * ∑' n : ℕ, k0 (n * u)

/-- The `n`-th term of the Mellin integrand. -/
noncomputable def F (s : ℂ) (n : ℕ) (u : ℝ) : ℂ := (u : ℂ) ^ (s - 1) • ((k0 ((n : ℝ) * u) : ℝ) : ℂ)

theorem continuous_k0 : Continuous k0 := by unfold k0; fun_prop

theorem hasMellin_scaled {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    MellinConvergent (fun u => ((k0 ((n : ℝ) * u) : ℝ) : ℂ)) s ∧
      mellin (fun u => ((k0 ((n : ℝ) * u) : ℝ) : ℂ)) s = (n : ℂ) ^ (-s) * M s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (fun u : ℝ => ((k0 (((0 : ℕ) : ℝ) * u) : ℝ) : ℂ)) = fun _ => 0 := by
      funext u; simp [k0_zero]
    have hs0 : -s ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [h0]
    refine ⟨by simp [MellinConvergent], ?_⟩
    simp [mellin, zero_cpow hs0]
  · have hb : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨(MellinConvergent.comp_mul_left hb).2 (hasMellin_k0 hs).1, ?_⟩
    have h := mellin_comp_mul_left (fun u : ℝ => ((k0 u : ℝ) : ℂ)) s hb
    rw [h, (hasMellin_k0 hs).2, smul_eq_mul]
    simp [M]

theorem integrable_F {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Integrable (F s n) (volume.restrict (Ioi 0)) :=
  (hasMellin_scaled hs n).1

theorem integral_F {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ∫ u in Ioi 0, F s n u = (n : ℂ) ^ (-s) * M s :=
  (hasMellin_scaled hs n).2

/-- The norm of the base integrand, `G(v) = v^{σ−1} |k₀(v)|`. -/
noncomputable def G (s : ℂ) (v : ℝ) : ℝ := ‖(v : ℂ) ^ (s - 1) • ((k0 v : ℝ) : ℂ)‖

theorem norm_F {s : ℂ} (n : ℕ) (hn : 0 < n) {u : ℝ} (hu : 0 < u) :
    ‖F s n u‖ = (n : ℝ) ^ (1 - s.re) * G s ((n : ℝ) * u) := by
  have hb : (0 : ℝ) < n := by exact_mod_cast hn
  unfold F G
  rw [norm_smul, norm_smul, norm_cpow_eq_rpow_re_of_pos hu,
    norm_cpow_eq_rpow_re_of_pos (mul_pos hb hu), Real.mul_rpow hb.le hu.le]
  have : (n : ℝ) ^ (1 - s.re) * (n : ℝ) ^ (s - 1).re = 1 := by
    rw [← Real.rpow_add hb]; simp
  calc u ^ (s - 1).re * ‖((k0 ((n : ℝ) * u) : ℝ) : ℂ)‖
      = ((n : ℝ) ^ (1 - s.re) * (n : ℝ) ^ (s - 1).re) * (u ^ (s - 1).re *
          ‖((k0 ((n : ℝ) * u) : ℝ) : ℂ)‖) := by rw [this, one_mul]
    _ = _ := by ring

theorem integral_norm_F {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ∫ u in Ioi 0, ‖F s n u‖ = ((n : ℝ) ^ s.re)⁻¹ * ∫ v in Ioi 0, G s v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hσ : s.re ≠ 0 := by linarith
    simp [F, k0_zero, Real.zero_rpow hσ]
  · have hb : (0 : ℝ) < n := by exact_mod_cast hn
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => norm_F (s := s) n hn hu),
      integral_const_mul, integral_comp_mul_left_Ioi (G s) 0 hb, mul_zero, smul_eq_mul, ← mul_assoc]
    congr 1
    rw [← Real.rpow_neg_one, ← Real.rpow_add hb, ← Real.rpow_neg hb.le]
    congr 1; ring

theorem summable_integral_norm {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ∫ u in Ioi 0, ‖F s n u‖ := by
  simp_rw [integral_norm_F hs]
  exact (Real.summable_nat_rpow_inv.2 hs).mul_right _

theorem tsum_F {s : ℂ} {u : ℝ} :
    ∑' n : ℕ, F s n u = (u : ℂ) ^ (s - 1) • (((∑' n : ℕ, k0 ((n : ℝ) * u)) : ℝ) : ℂ) := by
  simp only [F, smul_eq_mul]
  rw [tsum_mul_left, Complex.ofReal_tsum]

theorem summable_F {s : ℂ} {u : ℝ} (hu : 0 < u) : Summable fun n : ℕ => F s n u := by
  simp only [F, smul_eq_mul]
  refine Summable.mul_left _ ?_
  exact (Complex.ofRealCLM.summable (summable_k0 hu))

/-- The Mellin transform of `u ↦ Σ_n k₀(nu)` exists absolutely at `Re s > 1` and is
`ζ(s) M_{k₀}(s)`. -/
theorem hasMellin_sum {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u => (((∑' n : ℕ, k0 ((n : ℝ) * u)) : ℝ) : ℂ)) s (riemannZeta s * M s) := by
  have hs0 : 0 < s.re := by linarith
  -- integrability of the tsum
  have hmeas : AEStronglyMeasurable (fun u => ∑' n : ℕ, F s n u) (volume.restrict (Ioi 0)) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun N u => ∑ n ∈ Finset.range N, F s n u) (fun N => ?_) ?_
    · exact Finset.aestronglyMeasurable_fun_sum _ (fun n _ => (integrable_F hs0 n).1)
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall (fun u hu => (summable_F hu).hasSum.tendsto_sum_nat)
  have hint : Integrable (fun u => ∑' n : ℕ, F s n u) (volume.restrict (Ioi 0)) := by
    refine ⟨hmeas, ?_⟩
    have hle : ∫⁻ u in Ioi 0, ‖∑' n : ℕ, F s n u‖ₑ ≤ ∑' n : ℕ, ∫⁻ u in Ioi 0, ‖F s n u‖ₑ := by
      rw [← lintegral_tsum (fun n => (integrable_F hs0 n).1.enorm)]
      exact lintegral_mono (fun u => enorm_tsum_le_tsum_enorm)
    have heq : ∀ n : ℕ, ∫⁻ u in Ioi 0, ‖F s n u‖ₑ =
        ENNReal.ofReal (∫ u in Ioi 0, ‖F s n u‖) := fun n =>
      (ofReal_integral_norm_eq_lintegral_enorm (integrable_F hs0 n)).symm
    refine lt_of_le_of_lt hle ?_
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun _ => norm_nonneg _))
      (summable_integral_norm hs)]
    exact ENNReal.ofReal_lt_top
  have hF : ∫ u in Ioi 0, ∑' n : ℕ, F s n u = riemannZeta s * M s := by
    rw [← integral_tsum_of_summable_integral_norm (integrable_F hs0) (summable_integral_norm hs)]
    simp_rw [integral_F hs0]
    rw [tsum_mul_right, zeta_eq_tsum_one_div_nat_cpow hs]
    congr 2
    funext n
    rw [cpow_neg, one_div]
  refine ⟨?_, ?_⟩
  · refine (integrableOn_congr_fun (fun u hu => ?_) measurableSet_Ioi).1 hint
    exact tsum_F
  · rw [mellin, ← hF]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => tsum_F.symm)

/-- `ζ(s) M_{k₀}(s) = ξ(s)/4` for `Re s > 1`. -/
theorem zeta_mul_M {s : ℂ} (hs : 1 < s.re) : riemannZeta s * M s = completedXi s / 4 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  rw [completedXi_eq hs0 hs1, completedZeta_eq_tsum_of_one_lt_re hs,
    ← zeta_eq_tsum_one_div_nat_cpow hs, M]
  have : (π : ℂ) ^ (-s / 2) = (π : ℂ) ^ (-(s / 2)) := by rw [neg_div]
  rw [this]
  ring

/-- On `u > 0`, `𝓔k₀(u) u^{s−1/2} u^{−1} = u^{s−1} Σ_n k₀(nu)`. -/
theorem integrand_eq {s : ℂ} {u : ℝ} (hu : 0 < u) :
    ((Ek0 u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1 / 2) / u =
      (u : ℂ) ^ (s - 1) • (((∑' n : ℕ, k0 ((n : ℝ) * u)) : ℝ) : ℂ) := by
  have hu' : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
  rw [Ek0, smul_eq_mul, ofReal_mul, Complex.ofReal_cpow hu.le]
  have h1 : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rw [h1]
  have key : (u : ℂ) ^ (1 / 2 : ℂ) * (u : ℂ) ^ (s - 1 / 2) / u = (u : ℂ) ^ (s - 1) := by
    rw [← cpow_add _ _ hu', div_eq_mul_inv, ← cpow_neg_one, ← cpow_add _ _ hu']
    congr 1; ring
  calc ((u : ℂ) ^ (1 / 2 : ℂ) * (((∑' n : ℕ, k0 ((n : ℝ) * u)) : ℝ) : ℂ)) * (u : ℂ) ^ (s - 1 / 2) / u
      = ((u : ℂ) ^ (1 / 2 : ℂ) * (u : ℂ) ^ (s - 1 / 2) / u) *
          (((∑' n : ℕ, k0 ((n : ℝ) * u)) : ℝ) : ℂ) := by ring
    _ = _ := by rw [key]

/-- **`prop:R15` (ii).** For `Re s > 1`, `∫₀^∞ 𝓔k₀(u) u^{s−1/2} du/u` converges absolutely and
equals `ζ(s) M_{k₀}(s) = ξ(s)/4`. -/
theorem R15_ii {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => ((Ek0 u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1 / 2) / u) (Ioi 0) ∧
      ∫ u in Ioi 0, ((Ek0 u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1 / 2) / u = riemannZeta s * M s ∧
      riemannZeta s * M s = completedXi s / 4 := by
  obtain ⟨hc, hm⟩ := hasMellin_sum hs
  refine ⟨?_, ?_, zeta_mul_M hs⟩
  · exact (integrableOn_congr_fun (fun u hu => (integrand_eq hu).symm) measurableSet_Ioi).1 hc
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => integrand_eq hu)]
    rw [← hm]; rfl

end R15Periodization
end WeilRH
