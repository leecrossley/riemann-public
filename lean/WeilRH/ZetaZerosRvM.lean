/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.BlackBoxes2

/-!
# Zeros of `ζ` from Riemann–von Mangoldt (round 74)

Under the black box B6 (`RiemannVonMangoldt`), the counting function `N(T)` tends to infinity, so
`ζ` has zeros in the open critical strip with arbitrarily large imaginary part; in particular the
set of nontrivial zeros is nonempty and infinite. This is the zero-existence input used by
`prop:kun-over-Z` and the "`Z` nonempty" clause of `prop:P1Z` in `latex/notes.tex`.

## Main results

* `RvM.tendsto_zeroCount`: `N(T) → ∞`.
* `RvM.exists_zero_im_gt`: for every `T₀` there is `ρ` with `ζ(ρ) = 0`, `0 < Re ρ < 1`,
  `Im ρ > T₀`.
* `RvM.nontrivialZeros_infinite`: the set of zeros in the open strip with `Im ρ > 0` is infinite.

All results take `RiemannVonMangoldt` as an explicit hypothesis.
-/

open Filter Topology

namespace WeilRH.RvM

/-- `M(T) - C log T → ∞`. -/
lemma tendsto_mainTerm_sub (C : ℝ) :
    Tendsto (fun T : ℝ => mainTerm T - C * Real.log T) atTop atTop := by
  have hπ : 0 < 2 * Real.pi := by positivity
  -- `|C| log T ≤ T/(4π)` eventually
  have hlo := Real.isLittleO_log_id_atTop
  have hε : 0 < 1 / (2 * (2 * Real.pi) * (|C| + 1)) := by positivity
  have h1 := hlo.def hε
  -- `log(T/2π) - 1 ≥ 1` eventually
  have h2 : ∀ᶠ T : ℝ in atTop, 2 ≤ Real.log (T / (2 * Real.pi)) := by
    have : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const hπ)
    exact this.eventually_ge_atTop 2
  -- lower bound `T/(4π)`
  have hlow : ∀ᶠ T : ℝ in atTop, T / (2 * (2 * Real.pi)) ≤ mainTerm T - C * Real.log T := by
    filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with T hT1 hT2 hT
    have hT0 : 0 < T := by linarith
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT
    rw [Real.norm_of_nonneg hlog0, id, Real.norm_of_nonneg hT0.le] at hT1
    have hC : C * Real.log T ≤ T / (2 * (2 * Real.pi)) := by
      calc C * Real.log T ≤ |C| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
        _ ≤ (|C| + 1) * Real.log T := by nlinarith [abs_nonneg C]
        _ ≤ (|C| + 1) * (1 / (2 * (2 * Real.pi) * (|C| + 1)) * T) :=
          mul_le_mul_of_nonneg_left hT1 (by positivity)
        _ = T / (2 * (2 * Real.pi)) := by field_simp
    have hM : T / (2 * Real.pi) ≤ mainTerm T := by
      unfold mainTerm
      have : T / (2 * Real.pi) * 1 ≤ T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have : T / (2 * Real.pi) = 2 * (T / (2 * (2 * Real.pi))) := by field_simp
    linarith
  exact tendsto_atTop_mono' atTop hlow (tendsto_id.atTop_div_const (by positivity))

/-- **`N(T) → ∞`** under Riemann–von Mangoldt. -/
theorem tendsto_zeroCount (hB : RiemannVonMangoldt) :
    Tendsto (fun T : ℝ => (zeroCount T : ℝ)) atTop atTop := by
  obtain ⟨C, hC⟩ := hB
  refine tendsto_atTop_mono' atTop ?_ (tendsto_mainTerm_sub C)
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with T hT
  have := hC T hT
  have := (abs_le.1 this).1
  linarith

lemma nontrivialZeros_eq_of_no_zero {T₀ T₁ : ℝ} (h01 : T₀ ≤ T₁)
    (hno : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → T₀ < ρ.im → T₁ < ρ.im) :
    nontrivialZeros T₁ = nontrivialZeros T₀ := by
  ext ρ
  simp only [nontrivialZeros, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    refine ⟨h0, h1, h2, h3, ?_⟩
    by_contra hlt
    push Not at hlt
    exact absurd h4 (not_le.2 (hno ρ h0 h1 h2 hlt))
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨h0, h1, h2, h3, h4.trans h01⟩

/-- **Zeros of arbitrarily large height.** Under Riemann–von Mangoldt, for every `T₀` there is a
zero `ρ` of `ζ` with `0 < Re ρ < 1` and `Im ρ > T₀`. -/
theorem exists_zero_im_gt (hB : RiemannVonMangoldt) (T₀ : ℝ) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T₀ < ρ.im := by
  by_contra hne
  push Not at hne
  obtain ⟨T₁, hgt, hT₁⟩ := (((tendsto_zeroCount hB).eventually_gt_atTop
    (zeroCount T₀ : ℝ)).and (eventually_ge_atTop T₀)).exists
  have heq : nontrivialZeros T₁ = nontrivialZeros T₀ :=
    nontrivialZeros_eq_of_no_zero hT₁ fun ρ h0 h1 h2 h3 => absurd (hne ρ h0 h1 h2) (not_le.2 h3)
  have : zeroCount T₁ = zeroCount T₀ := by simp only [zeroCount, heq]
  rw [this] at hgt
  exact lt_irrefl _ hgt

/-- **The nontrivial zeros in the upper half-strip form an infinite set** (under B6). -/
theorem nontrivialZeros_infinite (hB : RiemannVonMangoldt) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im}.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image Complex.im).bddAbove
  obtain ⟨ρ, h0, h1, h2, h3⟩ := exists_zero_im_gt hB (max M 0)
  have hmem : ρ.im ∈ Complex.im '' {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im} :=
    ⟨ρ, ⟨h0, h1, h2, lt_of_le_of_lt (le_max_right _ _) h3⟩, rfl⟩
  have := hM hmem
  linarith [le_max_left M 0]

/-- In particular `ζ` has a zero in the open critical strip (under B6). -/
theorem exists_nontrivial_zero (hB : RiemannVonMangoldt) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 :=
  (exists_zero_im_gt hB 0).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

end WeilRH.RvM
