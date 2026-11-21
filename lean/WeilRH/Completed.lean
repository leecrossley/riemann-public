/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.RH

/-!
# The completed zeta datum `ξ` (report §2, AW2)

Source: `ai/2026-09-19-arithmetic-weil-cohomology/report.md`, §2:
`Λ(s) = π^{-s/2} Γ(s/2) ζ(s)`, `ξ(s) = ½ s (s - 1) Λ(s)`, `ξ` entire.

Mathlib provides `completedRiemannZeta` (`Λ`, with poles at `0`, `1`) and the entire function
`completedRiemannZeta₀ = Λ + 1/s + 1/(1-s)`. Mathlib has no `ξ`; we define

  `completedXi s = (s (s - 1) Λ₀(s) + 1) / 2`,

prove that it is entire (`differentiable_completedXi`), agrees with `½ s (s-1) Λ(s)` away from
`0, 1` (`completedXi_eq`), and that its zeros are *exactly* the nontrivial zeros of `ζ` in the
sense of `IsNontrivialZetaZero` (`completedXi_eq_zero_iff`; no side condition on `ρ` is needed,
because `ξ(0) = ξ(1) = 1/2`). Its analytic order is finite everywhere
(`analyticOrderAt_completedXi_ne_top`), so `analyticOrderNatAt completedXi ρ` is the honest
zero order.
-/

open Complex

namespace WeilRH

/-- Riemann's `ξ(s) = ½ s (s - 1) Λ(s)`, defined as an entire function via
`completedRiemannZeta₀`. -/
noncomputable def completedXi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- `ξ` is entire. -/
theorem differentiable_completedXi : Differentiable ℂ completedXi := by
  unfold completedXi
  have := differentiable_completedZeta₀
  fun_prop

/-- `ξ` is analytic at every point. -/
theorem analyticAt_completedXi (s : ℂ) : AnalyticAt ℂ completedXi s :=
  differentiable_completedXi.analyticAt s

/-- Agreement with the report's definition `ξ(s) = ½ s (s - 1) Λ(s)` for `s ≠ 0, 1`. -/
theorem completedXi_eq {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    completedXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  have h1 : (1 - s) ≠ 0 := sub_ne_zero.2 (Ne.symm hs')
  rw [completedXi, completedRiemannZeta_eq]
  field_simp
  ring

@[simp] theorem completedXi_zero : completedXi 0 = 1 / 2 := by simp [completedXi]

@[simp] theorem completedXi_one : completedXi 1 = 1 / 2 := by simp [completedXi]

/-- The functional equation `ξ(1 - s) = ξ(s)`. -/
theorem completedXi_one_sub (s : ℂ) : completedXi (1 - s) = completedXi s := by
  rw [completedXi, completedXi, completedRiemannZeta₀_one_sub]
  ring

/-- `ξ` is not identically zero. -/
theorem completedXi_ne_zero_somewhere : completedXi 0 ≠ 0 := by simp

/-- `Λ` does not vanish at the trivial zeros of `ζ`. -/
theorem completedRiemannZeta_neg_two_mul_nat_add_one_ne_zero (n : ℕ) :
    completedRiemannZeta (-2 * (n + 1)) ≠ 0 := by
  have hre : 1 < ((2 * n + 3 : ℂ)).re := by
    simp only [add_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have h := completedRiemannZeta_one_sub (2 * n + 3 : ℂ)
  have heq : (1 - (2 * n + 3) : ℂ) = -2 * (n + 1) := by ring
  rw [heq] at h
  rw [h]
  have hne : (2 * n + 3 : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hz := riemannZeta_def_of_ne_zero hne
  have hΓ := Gammaℝ_ne_zero_of_re_pos (s := (2 * n + 3 : ℂ)) (by linarith)
  have hζ := riemannZeta_ne_zero_of_one_lt_re hre
  intro hΛ
  rw [hΛ, zero_div] at hz
  exact hζ hz

/-- **Completed zeta datum.** The zeros of the entire function `ξ` are exactly the nontrivial
zeros of `ζ` (in the sense of Mathlib's `RiemannHypothesis`, `IsNontrivialZetaZero`). -/
theorem completedXi_eq_zero_iff (ρ : ℂ) : completedXi ρ = 0 ↔ IsNontrivialZetaZero ρ := by
  rcases eq_or_ne ρ 0 with rfl | h0
  · simp only [completedXi_zero, one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_iff]
    rintro ⟨h, -, -⟩
    rw [riemannZeta_zero] at h
    norm_num at h
  rcases eq_or_ne ρ 1 with rfl | h1
  · simp only [completedXi_one, one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_iff]
    rintro ⟨-, -, h⟩
    exact h rfl
  have hρ1 : ρ - 1 ≠ 0 := sub_ne_zero.2 h1
  rw [completedXi_eq h0 h1]
  have hΛ : completedXi ρ = 0 ↔ completedRiemannZeta ρ = 0 := by
    rw [completedXi_eq h0 h1]
    constructor
    · intro h
      have : ρ * (ρ - 1) * completedRiemannZeta ρ = 0 := by linear_combination 2 * h
      simpa [h0, hρ1] using this
    · intro h; simp [h]
  rw [← completedXi_eq h0 h1, hΛ]
  have hz := riemannZeta_def_of_ne_zero h0
  constructor
  · intro h
    refine ⟨by rw [hz, h, zero_div], ?_, h1⟩
    rintro ⟨n, rfl⟩
    exact completedRiemannZeta_neg_two_mul_nat_add_one_ne_zero n h
  · rintro ⟨hζ, htriv, -⟩
    rw [hz, div_eq_zero_iff] at hζ
    rcases hζ with h | h
    · exact h
    · obtain ⟨n, rfl⟩ := Gammaℝ_eq_zero_iff.1 h
      rcases n with _ | n
      · simp at h0
      · exact absurd ⟨n, by push_cast; ring⟩ htriv

/-- The analytic order of `ξ` is finite at every point (`ξ ≢ 0`, `ℂ` connected). -/
theorem analyticOrderAt_completedXi_ne_top (ρ : ℂ) : analyticOrderAt completedXi ρ ≠ ⊤ := by
  have hA : AnalyticOnNhd ℂ completedXi Set.univ := fun s _ => analyticAt_completedXi s
  refine hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
    (Set.mem_univ ρ) ?_
  rw [analyticOrderAt_eq_zero.2 (Or.inr completedXi_ne_zero_somewhere)]
  exact ENat.zero_ne_top

/-- The zero order of `ξ` at `ρ` is positive iff `ρ` is a nontrivial zero of `ζ`. -/
theorem analyticOrderNatAt_completedXi_pos_iff (ρ : ℂ) :
    0 < analyticOrderNatAt completedXi ρ ↔ IsNontrivialZetaZero ρ := by
  rw [← completedXi_eq_zero_iff, analyticOrderNatAt, Nat.pos_iff_ne_zero, Ne,
    ENat.toNat_eq_zero, or_iff_left (analyticOrderAt_completedXi_ne_top ρ), analyticOrderAt_eq_zero]
  simp [analyticAt_completedXi ρ]

end WeilRH
