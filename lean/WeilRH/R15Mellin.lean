/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# `prop:R15` (i): the Mellin transform of the displayed CCM kernel

`latex/notes.tex`, `def:ccm-kernel` and `prop:R15`. The displayed kernel is
`k₀(u) = (π/2) u² (2πu² − 3) e^{−πu²}` and its Mellin transform is `M_{k₀}(s) = ∫₀^∞ k₀(u) u^{s−1} du`.

* (i) `R15Mellin.hasMellin_k0`: for `Re s > 0` the integral converges absolutely and
  `M_{k₀}(s) = (1/8) s(s−1) π^{−s/2} Γ(s/2)`.
* (ii) and (iii) are not formalized here.

Mellin transforms use Mathlib's `mellin f s = ∫_{(0,∞)} t^{s−1} f(t) dt`; `MellinConvergent` is
absolute convergence of that integral.
-/

open Complex MeasureTheory Set Filter Real

namespace WeilRH
namespace R15Mellin

/-- `def:ccm-kernel`: the displayed kernel `k₀(u) = (π/2) u² (2πu² − 3) e^{−πu²}`. -/
noncomputable def k0 (u : ℝ) : ℝ := π / 2 * u ^ 2 * (2 * π * u ^ 2 - 3) * Real.exp (-(π * u ^ 2))

/-- The Gaussian `u ↦ e^{−πu²}`, as a complex-valued function. -/
noncomputable def gauss (u : ℝ) : ℂ := ((Real.exp (-(π * u ^ 2)) : ℝ) : ℂ)

/-- `u ↦ e^{−u}`. -/
noncomputable def e0 (t : ℝ) : ℂ := ((Real.exp (-t) : ℝ) : ℂ)

theorem hasMellin_e0 {s : ℂ} (hs : 0 < s.re) : HasMellin e0 s (Gamma s) := by
  refine ⟨?_, ?_⟩
  · have := Complex.GammaIntegral_convergent hs
    refine (integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi).1 this
    simp [e0, smul_eq_mul, mul_comm]
  · rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp [e0, smul_eq_mul, mul_comm]

/-- The Mellin transform of `u ↦ e^{−πu}` is `π^{−s} Γ(s)`. -/
theorem hasMellin_expPi {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t => e0 (π * t)) s ((π : ℂ) ^ (-s) * Gamma s) := by
  obtain ⟨hc, hm⟩ := hasMellin_e0 hs
  refine ⟨(MellinConvergent.comp_mul_left Real.pi_pos).2 hc, ?_⟩
  rw [mellin_comp_mul_left _ _ Real.pi_pos, hm, smul_eq_mul]

/-- The Mellin transform of the Gaussian: `∫₀^∞ e^{−πu²} u^{β−1} du = (1/2) π^{−β/2} Γ(β/2)` for
`Re β > 0`, with absolute convergence. -/
theorem hasMellin_gauss {β : ℂ} (hβ : 0 < β.re) :
    HasMellin gauss β (1 / 2 * (π : ℂ) ^ (-(β / 2)) * Gamma (β / 2)) := by
  have hβ2 : 0 < (β / 2).re := by
    rw [Complex.div_ofNat_re]; linarith
  obtain ⟨hc, hm⟩ := hasMellin_expPi hβ2
  have e2 : β / ((2 : ℝ) : ℂ) = β / 2 := by norm_num
  have hc' : MellinConvergent (fun t : ℝ => e0 (π * t)) (β / ((2 : ℝ) : ℂ)) := by
    rw [e2]; exact hc
  have hconv : MellinConvergent (fun t : ℝ => e0 (π * t ^ (2 : ℝ))) β :=
    (MellinConvergent.comp_rpow (f := fun t : ℝ => e0 (π * t)) (s := β)
      (by norm_num : (2 : ℝ) ≠ 0)).2 hc'
  have hmel : mellin (fun t : ℝ => e0 (π * t ^ (2 : ℝ))) β =
      |(2 : ℝ)|⁻¹ • mellin (fun t : ℝ => e0 (π * t)) (β / ((2 : ℝ) : ℂ)) :=
    mellin_comp_rpow (fun t : ℝ => e0 (π * t)) β 2
  have hfun : gauss = fun t : ℝ => e0 (π * t ^ (2 : ℝ)) := by
    funext u; simp only [gauss, e0, Real.rpow_two]
  rw [hfun]
  refine ⟨hconv, ?_⟩
  rw [hmel, e2, hm, abs_two, Complex.real_smul]
  push_cast
  ring

/-- `k₀` as a combination of Gaussian moments: `k₀(u) = π² u⁴ e^{−πu²} − (3π/2) u² e^{−πu²}`. -/
theorem k0_eq (u : ℝ) :
    ((k0 u : ℝ) : ℂ) = (π : ℂ) ^ 2 * ((u : ℂ) ^ (4 : ℂ) * gauss u) -
      3 * π / 2 * ((u : ℂ) ^ (2 : ℂ) * gauss u) := by
  have h4 : (u : ℂ) ^ (4 : ℂ) = (u : ℂ) ^ (4 : ℕ) := by
    rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  have h2 : (u : ℂ) ^ (2 : ℂ) = (u : ℂ) ^ (2 : ℕ) := by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  rw [h4, h2]
  simp only [k0, gauss]
  push_cast
  ring

/-- **`prop:R15` (i).** For `Re s > 0` the Mellin integral of `k₀` converges absolutely and
`M_{k₀}(s) = (1/8) s(s−1) π^{−s/2} Γ(s/2)`. -/
theorem hasMellin_k0 {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun u => ((k0 u : ℝ) : ℂ)) s
      (1 / 8 * s * (s - 1) * (π : ℂ) ^ (-(s / 2)) * Gamma (s / 2)) := by
  have h4 : 0 < (s + 4).re := by simp; linarith
  have h2 : 0 < (s + 2).re := by simp; linarith
  obtain ⟨c4, m4⟩ := hasMellin_gauss h4
  obtain ⟨c2, m2⟩ := hasMellin_gauss h2
  have c4' : MellinConvergent (fun t => (t : ℂ) ^ (4 : ℂ) • gauss t) s :=
    MellinConvergent.cpow_smul.2 c4
  have c2' : MellinConvergent (fun t => (t : ℂ) ^ (2 : ℂ) • gauss t) s :=
    MellinConvergent.cpow_smul.2 c2
  have m4' : mellin (fun t => (t : ℂ) ^ (4 : ℂ) • gauss t) s = mellin gauss (s + 4) :=
    mellin_cpow_smul _ _ _
  have m2' : mellin (fun t => (t : ℂ) ^ (2 : ℂ) • gauss t) s = mellin gauss (s + 2) :=
    mellin_cpow_smul _ _ _
  have H := hasMellin_sub (c4'.const_smul ((π : ℂ) ^ 2)) (c2'.const_smul (3 * (π : ℂ) / 2))
  -- the kernel agrees with the combination on `(0, ∞)`
  have heq : EqOn (fun u => ((k0 u : ℝ) : ℂ))
      (fun t => (π : ℂ) ^ 2 • ((t : ℂ) ^ (4 : ℂ) • gauss t) -
        (3 * (π : ℂ) / 2) • ((t : ℂ) ^ (2 : ℂ) • gauss t)) (Ioi 0) := by
    intro u hu
    simp only [smul_eq_mul]
    rw [k0_eq u]
  have hconv : MellinConvergent (fun u => ((k0 u : ℝ) : ℂ)) s := by
    refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi).2 H.1
    exact congrArg _ (heq ht)
  refine ⟨hconv, ?_⟩
  have hmel : mellin (fun u => ((k0 u : ℝ) : ℂ)) s =
      mellin (fun t => (π : ℂ) ^ 2 • ((t : ℂ) ^ (4 : ℂ) • gauss t) -
        (3 * (π : ℂ) / 2) • ((t : ℂ) ^ (2 : ℂ) • gauss t)) s := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    exact congrArg _ (heq ht)
  rw [hmel, H.2, mellin_const_smul, mellin_const_smul, m4', m2', m4, m2]
  -- algebra with `Γ(s/2 + 2) = (s/2+1)(s/2) Γ(s/2)` and `π`-powers
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΓ1 : Gamma (s / 2 + 1) = s / 2 * Gamma (s / 2) := Complex.Gamma_add_one _ (by
    intro h; have := congrArg Complex.re h; simp at this; linarith)
  have hΓ2 : Gamma (s / 2 + 2) = (s / 2 + 1) * (s / 2 * Gamma (s / 2)) := by
    rw [show s / 2 + 2 = (s / 2 + 1) + 1 by ring, Complex.Gamma_add_one _ (by
      intro h; have := congrArg Complex.re h; simp at this; linarith), hΓ1]
  have e4 : (s + 4) / 2 = s / 2 + 2 := by ring
  have e2 : (s + 2) / 2 = s / 2 + 1 := by ring
  have p4 : (π : ℂ) ^ (-(s / 2 + 2)) = (π : ℂ) ^ (-(s / 2)) * ((π : ℂ) ^ 2)⁻¹ := by
    rw [show -(s / 2 + 2) = -(s / 2) + (-2 : ℂ) by ring, Complex.cpow_add _ _ hpi]
    congr 1
    rw [Complex.cpow_neg, show ((2 : ℂ)) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  have p2 : (π : ℂ) ^ (-(s / 2 + 1)) = (π : ℂ) ^ (-(s / 2)) * (π : ℂ)⁻¹ := by
    rw [show -(s / 2 + 1) = -(s / 2) + (-1 : ℂ) by ring, Complex.cpow_add _ _ hpi,
      Complex.cpow_neg_one]
  rw [e4, e2, p4, p2, hΓ2, hΓ1]
  simp only [smul_eq_mul]
  field_simp
  ring

end R15Mellin
end WeilRH
